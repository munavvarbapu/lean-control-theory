# Publishing the source

The archive contains the project source. It deliberately leaves out the
downloaded compiler, mathlib checkout, build files, and local credentials.
Lean and Lake fetch the pinned dependencies when someone builds it.

## Through the GitHub website

1. Sign in to your GitHub account yourself.
2. Create a repository named `lean-control-theory`. Choose public visibility
   if you want reviewers to open the link without an invitation.
3. Extract this archive on your computer.
4. Upload the **contents** of the extracted `lean-control-theory` folder,
   including `.github`, `ControlTheory`, `docs`, `scripts`, and
   `verification`, to the new repository. Upload the source files rather
   than the ZIP itself.
5. Commit the files with a message such as
   `Formalize Kalman, PBH, feedback invariance, and Lyapunov decay`.
6. Check that the repository opens at its normal GitHub address. Wait for
   the Lean proofs workflow to complete before referring to hosted CI.

## Through Git

If you use Git locally, create an empty repository on GitHub, open a
terminal in the extracted project folder, and run:

```sh
git init
git add .
git commit -m "Formalize Kalman, PBH, feedback invariance, and Lyapunov decay"
git branch -M main
git remote add origin https://github.com/YOUR_USERNAME/lean-control-theory.git
git push -u origin main
```

Replace `YOUR_USERNAME` with your actual GitHub username. Complete any
authentication prompt yourself. The repository address becomes the link
you can share with a reviewer.

The README, mathematical notes, and acknowledgments describe the actual
scope and development of the work. Read the proofs and the review guide
before discussing the project in an interview.
