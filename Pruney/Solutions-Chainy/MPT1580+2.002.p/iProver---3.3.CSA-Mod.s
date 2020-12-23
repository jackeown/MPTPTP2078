%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:57 EST 2020

% Result     : CounterSatisfiable 4.07s
% Output     : Model 4.07s
% Verified   : 
% Statistics : Number of formulae       :    7 (   7 expanded)
%              Number of leaves         :    7 (   7 expanded)
%              Depth                    :    0
%              Number of atoms          :  220 ( 220 expanded)
%              Number of equality atoms :  209 ( 209 expanded)
%              Maximal formula depth    :   41 (  14 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%------ Positive definition of equality_sorted 
fof(lit_def,axiom,(
    ! [X0_0,X0_2,X1_2] :
      ( equality_sorted(X0_0,X0_2,X1_2)
    <=> ( ( X0_0 = $o
          & X1_2 = X0_2 )
        | ( X0_0 = $i
          & X0 != k1_zfmisc_1(X0)
          & X0 != u1_struct_0(X0)
          & X0 != sK3
          & ( X0 != sK1
            | X1 != sK2 )
          & X0 != u1_struct_0(sK1)
          & ( X0 != u1_struct_0(sK1)
            | X1 != u1_struct_0(sK2) )
          & X0 != sK2
          & X0 != u1_struct_0(sK2)
          & ( X0 != u1_struct_0(sK2)
            | X1 != u1_struct_0(sK1) )
          & ( X0 != u1_struct_0(sK2)
            | X1 != u1_struct_0(X1) )
          & X0 != sK0(X0,sK3)
          & X0 != sK0(X0,u1_struct_0(sK2))
          & ( X0 != sK0(X1,k1_zfmisc_1(X2))
            | X1 != sK0(X1,k1_zfmisc_1(X2)) )
          & ( X0 != sK0(X1,u1_struct_0(sK1))
            | X1 != sK0(X1,u1_struct_0(sK1)) )
          & ( X0 != sK0(X1,u1_struct_0(X2))
            | X1 != sK0(X1,u1_struct_0(X2)) )
          & ! [X3] : X0 != sK0(X0,X3)
          & X1 != k1_zfmisc_1(X1)
          & X1 != sK3
          & X1 != u1_struct_0(sK1)
          & X1 != sK2
          & X1 != u1_struct_0(sK2)
          & X1 != u1_struct_0(X1)
          & X1 != sK0(X1,sK3)
          & X1 != sK0(X1,X2)
          & X1 != sK0(X1,u1_struct_0(sK2)) )
        | ( X0_0 = $i
          & X0 = sK3
          & X1 = sK3 )
        | ( X0_0 = $i
          & X0 = u1_struct_0(sK1)
          & X1 = u1_struct_0(sK1) )
        | ? [X2] :
            ( X0_0 = $i
            & X0 = u1_struct_0(sK1)
            & X1 = k1_zfmisc_1(X2) )
        | ? [X2] :
            ( X0_0 = $i
            & X0 = u1_struct_0(sK1)
            & X1 = u1_struct_0(X2)
            & X2 != sK1
            & X2 != sK2 )
        | ( X0_0 = $i
          & X0 = sK2
          & X1 = sK2 )
        | ( X0_0 = $i
          & X0 = u1_struct_0(sK2)
          & X1 = u1_struct_0(sK2) )
        | ? [X2,X3] :
            ( X0_0 = $i
            & X0 = sK0(X2,X3)
            & X1 = sK0(X2,X3)
            & X3 != k1_zfmisc_1(X3)
            & X3 != sK3
            & X3 != u1_struct_0(sK1)
            & X3 != u1_struct_0(sK2)
            & X3 != u1_struct_0(X3) )
        | ? [X2,X3] :
            ( X0_0 = $i
            & X0 = k1_zfmisc_1(X2)
            & X1 = k1_zfmisc_1(X3) )
        | ? [X2] :
            ( X0_0 = $i
            & X0 = k1_zfmisc_1(X2)
            & X1 = u1_struct_0(sK1) )
        | ? [X2] :
            ( X0_0 = $i
            & X0 = k1_zfmisc_1(X2)
            & X1 = k1_zfmisc_1(X2) )
        | ? [X2,X3] :
            ( X0_0 = $i
            & X0 = k1_zfmisc_1(X2)
            & X1 = u1_struct_0(X3)
            & X3 != sK1
            & X3 != sK2 )
        | ? [X2,X3] :
            ( X0_0 = $i
            & X0 = u1_struct_0(X2)
            & X1 = k1_zfmisc_1(X3)
            & X2 != sK1
            & X2 != sK2 )
        | ? [X2] :
            ( X0_0 = $i
            & X0 = u1_struct_0(X2)
            & X1 = u1_struct_0(sK1)
            & X2 != sK1
            & X2 != sK2 )
        | ? [X2,X3] :
            ( X0_0 = $i
            & X0 = u1_struct_0(X2)
            & X1 = u1_struct_0(X3)
            & X2 != sK1
            & ( X2 != sK1
              | X3 != sK2 )
            & X2 != sK2
            & ( X2 != sK2
              | X3 != sK1 )
            & ( X2 != k1_zfmisc_1(X2)
              | X3 != sK2 )
            & X3 != sK1
            & X3 != sK2 )
        | ? [X2] :
            ( X0_0 = $i
            & X0 = u1_struct_0(X2)
            & X1 = u1_struct_0(X2)
            & X2 != sK1
            & X2 != sK2 )
        | ? [X2] :
            ( X0_0 = $i
            & X0 = sK0(X2,sK3)
            & X1 = sK0(X2,sK3) )
        | ? [X2] :
            ( X0_0 = $i
            & X0 = sK0(X2,u1_struct_0(sK2))
            & X1 = sK0(X2,u1_struct_0(sK2)) )
        | ? [X2,X3] :
            ( X0_0 = $i
            & X0 = sK0(X2,k1_zfmisc_1(X3))
            & X1 = sK0(X2,k1_zfmisc_1(X3)) )
        | ? [X2] :
            ( X0_0 = $i
            & X0 = sK0(X2,u1_struct_0(sK1))
            & X1 = sK0(X2,u1_struct_0(sK1)) )
        | ? [X2,X3] :
            ( X0_0 = $i
            & X0 = sK0(X2,u1_struct_0(X3))
            & X1 = sK0(X2,u1_struct_0(X3))
            & X3 != sK2 )
        | ( X0_0 = $i
          & X1 = X0
          & X0 != k1_zfmisc_1(X0)
          & X0 != u1_struct_0(X0)
          & X0 != sK3
          & X0 != u1_struct_0(sK1)
          & X0 != sK2
          & X0 != u1_struct_0(sK2)
          & X0 != sK0(X0,sK3)
          & X0 != sK0(X0,u1_struct_0(sK2))
          & X0 != sK0(X0,u1_struct_0(sK1))
          & ! [X2] : X0 != sK0(X0,X2)
          & X0 != sK0(X0,k1_zfmisc_1(X2))
          & X0 != sK0(X0,u1_struct_0(X2)) ) ) ) )).

%------ Positive definition of r1_tarski 
fof(lit_def_001,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> $false ) )).

%------ Positive definition of r2_hidden 
fof(lit_def_002,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
    <=> ( ? [X2,X3] :
            ( X0 = sK0(X2,X3)
            & X1 != k1_zfmisc_1(X1)
            & ( X1 != k1_zfmisc_1(X3)
              | X3 != k1_zfmisc_1(X3) )
            & X1 != sK3
            & X1 != u1_struct_0(sK1)
            & ( X1 != u1_struct_0(sK1)
              | X3 != u1_struct_0(sK1) )
            & X1 != u1_struct_0(X1)
            & ( X1 != k1_zfmisc_1(X2)
              | X2 != X2 )
            & ( X1 != k1_zfmisc_1(X2)
              | X2 != X2
              | X3 != u1_struct_0(sK2) )
            & ( X1 != u1_struct_0(X3)
              | X3 != u1_struct_0(sK2) )
            & ( X1 != u1_struct_0(X3)
              | X3 != u1_struct_0(X3) )
            & X3 != k1_zfmisc_1(X3)
            & X3 != sK3
            & X3 != u1_struct_0(sK1)
            & X3 != u1_struct_0(sK2)
            & X3 != u1_struct_0(X3) )
        | ? [X2] :
            ( X0 = sK0(X2,sK3)
            & X1 = sK3 )
        | ? [X2] :
            ( X0 = sK0(X2,u1_struct_0(sK2))
            & X1 = u1_struct_0(sK2) )
        | ? [X2] :
            ( X0 = sK0(X2,sK2)
            & X1 = sK2 )
        | ? [X2] :
            ( X0 = sK0(X2,X1)
            & X1 != k1_zfmisc_1(X1)
            & X1 != sK3
            & X1 != u1_struct_0(sK1)
            & X1 != sK2
            & X1 != u1_struct_0(sK2)
            & X1 != u1_struct_0(X1)
            & X1 != sK0(X1,sK3) )
        | ? [X2,X3] :
            ( X0 = sK0(X2,sK0(X3,sK3))
            & X1 = sK0(X3,sK3) ) ) ) )).

%------ Positive definition of m1_subset_1 
fof(lit_def_003,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
    <=> ( ( X0 = sK3
          & X1 = u1_struct_0(sK2) )
        | ? [X2,X3] :
            ( X0 = sK0(X2,X3)
            & X1 != k1_zfmisc_1(X1)
            & ( X1 != k1_zfmisc_1(X3)
              | X3 != k1_zfmisc_1(X3) )
            & X1 != u1_struct_0(sK1)
            & ( X1 != u1_struct_0(sK1)
              | X3 != sK3 )
            & ( X1 != u1_struct_0(sK1)
              | X3 != u1_struct_0(sK1) )
            & ( X1 != u1_struct_0(sK1)
              | X3 != u1_struct_0(sK2) )
            & X1 != u1_struct_0(X1)
            & ( X1 != k1_zfmisc_1(X2)
              | X2 != X2
              | X3 != sK3 )
            & ( X1 != u1_struct_0(X3)
              | X3 != u1_struct_0(sK2) )
            & ( X1 != u1_struct_0(X3)
              | X3 != u1_struct_0(X3) )
            & X3 != k1_zfmisc_1(X3)
            & X3 != sK3
            & X3 != u1_struct_0(sK1)
            & X3 != u1_struct_0(sK2)
            & X3 != u1_struct_0(X3) )
        | ? [X2] :
            ( X0 = sK0(X2,sK3)
            & X1 = sK3 )
        | ? [X2] :
            ( X0 = sK0(X2,u1_struct_0(sK2))
            & X1 = u1_struct_0(sK2) )
        | ? [X2] :
            ( X0 = sK0(X2,X1)
            & X1 != k1_zfmisc_1(X1)
            & X1 != sK3
            & X1 != u1_struct_0(sK1)
            & X1 != u1_struct_0(X1) ) ) ) )).

%------ Positive definition of v1_xboole_0 
fof(lit_def_004,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> $false ) )).

%------ Positive definition of v2_struct_0 
fof(lit_def_005,axiom,(
    ! [X0] :
      ( v2_struct_0(X0)
    <=> $false ) )).

%------ Positive definition of l1_orders_2 
fof(lit_def_006,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
    <=> $false ) )).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:53:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 4.07/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.07/0.99  
% 4.07/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.07/0.99  
% 4.07/0.99  ------  iProver source info
% 4.07/0.99  
% 4.07/0.99  git: date: 2020-06-30 10:37:57 +0100
% 4.07/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.07/0.99  git: non_committed_changes: false
% 4.07/0.99  git: last_make_outside_of_git: false
% 4.07/0.99  
% 4.07/0.99  ------ 
% 4.07/0.99  ------ Parsing...
% 4.07/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.07/0.99  
% 4.07/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 4.07/0.99  
% 4.07/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.07/0.99  
% 4.07/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.07/0.99  ------ Proving...
% 4.07/0.99  ------ Problem Properties 
% 4.07/0.99  
% 4.07/0.99  
% 4.07/0.99  clauses                                 7
% 4.07/0.99  conjectures                             2
% 4.07/0.99  EPR                                     1
% 4.07/0.99  Horn                                    6
% 4.07/0.99  unary                                   2
% 4.07/0.99  binary                                  2
% 4.07/0.99  lits                                    15
% 4.07/0.99  lits eq                                 2
% 4.07/0.99  fd_pure                                 0
% 4.07/0.99  fd_pseudo                               0
% 4.07/0.99  fd_cond                                 0
% 4.07/0.99  fd_pseudo_cond                          2
% 4.07/0.99  AC symbols                              0
% 4.07/0.99  
% 4.07/0.99  ------ Input Options Time Limit: Unbounded
% 4.07/0.99  
% 4.07/0.99  
% 4.07/0.99  ------ 
% 4.07/0.99  Current options:
% 4.07/0.99  ------ 
% 4.07/0.99  
% 4.07/0.99  
% 4.07/0.99  
% 4.07/0.99  
% 4.07/0.99  ------ Proving...
% 4.07/0.99  
% 4.07/0.99  
% 4.07/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 4.07/0.99  
% 4.07/0.99  ------ Building Model...Done
% 4.07/0.99  
% 4.07/0.99  %------ The model is defined over ground terms (initial term algebra).
% 4.07/0.99  %------ Predicates are defined as (\forall x_1,..,x_n  ((~)P(x_1,..,x_n) <=> (\phi(x_1,..,x_n)))) 
% 4.07/0.99  %------ where \phi is a formula over the term algebra.
% 4.07/0.99  %------ If we have equality in the problem then it is also defined as a predicate above, 
% 4.07/0.99  %------ with "=" on the right-hand-side of the definition interpreted over the term algebra term_algebra_type
% 4.07/0.99  %------ See help for --sat_out_model for different model outputs.
% 4.07/0.99  %------ equality_sorted(X0,X1,X2) can be used in the place of usual "="
% 4.07/0.99  %------ where the first argument stands for the sort ($i in the unsorted case)
% 4.07/0.99  % SZS output start Model for theBenchmark.p
% 4.07/0.99  
% 4.07/0.99  %------ Positive definition of equality_sorted 
% 4.07/0.99  fof(lit_def,axiom,
% 4.07/0.99      (! [X0_0,X0_2,X1_2] : 
% 4.07/0.99        ( equality_sorted(X0_0,X0_2,X1_2) <=>
% 4.07/0.99             (
% 4.07/0.99                (
% 4.07/0.99                  ( X0_0=$o & X1_2=X0_2 )
% 4.07/0.99                )
% 4.07/0.99  
% 4.07/0.99               | 
% 4.07/0.99                (
% 4.07/0.99                  ( X0_0=$i )
% 4.07/0.99                 &
% 4.07/0.99                  ( X0!=k1_zfmisc_1(X0) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X0!=u1_struct_0(X0) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X0!=sK3 )
% 4.07/0.99                 &
% 4.07/0.99                  ( X0!=sK1 | X1!=sK2 )
% 4.07/0.99                 &
% 4.07/0.99                  ( X0!=u1_struct_0(sK1) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X0!=u1_struct_0(sK1) | X1!=u1_struct_0(sK2) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X0!=sK2 )
% 4.07/0.99                 &
% 4.07/0.99                  ( X0!=u1_struct_0(sK2) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X0!=u1_struct_0(sK2) | X1!=u1_struct_0(sK1) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X0!=u1_struct_0(sK2) | X1!=u1_struct_0(X1) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X0!=sK0(X0,sK3) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X0!=sK0(X0,u1_struct_0(sK2)) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X0!=sK0(X1,k1_zfmisc_1(X2)) | X1!=sK0(X1,k1_zfmisc_1(X2)) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X0!=sK0(X1,u1_struct_0(sK1)) | X1!=sK0(X1,u1_struct_0(sK1)) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X0!=sK0(X1,u1_struct_0(X2)) | X1!=sK0(X1,u1_struct_0(X2)) )
% 4.07/0.99                 &
% 4.07/0.99                  ! [X3] : ( X0!=sK0(X0,X3) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=k1_zfmisc_1(X1) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=sK3 )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=u1_struct_0(sK1) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=sK2 )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=u1_struct_0(sK2) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=u1_struct_0(X1) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=sK0(X1,sK3) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=sK0(X1,X2) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=sK0(X1,u1_struct_0(sK2)) )
% 4.07/0.99                )
% 4.07/0.99  
% 4.07/0.99               | 
% 4.07/0.99                (
% 4.07/0.99                  ( X0_0=$i & X0=sK3 & X1=sK3 )
% 4.07/0.99                )
% 4.07/0.99  
% 4.07/0.99               | 
% 4.07/0.99                (
% 4.07/0.99                  ( X0_0=$i & X0=u1_struct_0(sK1) & X1=u1_struct_0(sK1) )
% 4.07/0.99                )
% 4.07/0.99  
% 4.07/0.99               | 
% 4.07/0.99              ? [X2] : 
% 4.07/0.99                (
% 4.07/0.99                  ( X0_0=$i & X0=u1_struct_0(sK1) & X1=k1_zfmisc_1(X2) )
% 4.07/0.99                )
% 4.07/0.99  
% 4.07/0.99               | 
% 4.07/0.99              ? [X2] : 
% 4.07/0.99                (
% 4.07/0.99                  ( X0_0=$i & X0=u1_struct_0(sK1) & X1=u1_struct_0(X2) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X2!=sK1 )
% 4.07/0.99                 &
% 4.07/0.99                  ( X2!=sK2 )
% 4.07/0.99                )
% 4.07/0.99  
% 4.07/0.99               | 
% 4.07/0.99                (
% 4.07/0.99                  ( X0_0=$i & X0=sK2 & X1=sK2 )
% 4.07/0.99                )
% 4.07/0.99  
% 4.07/0.99               | 
% 4.07/0.99                (
% 4.07/0.99                  ( X0_0=$i & X0=u1_struct_0(sK2) & X1=u1_struct_0(sK2) )
% 4.07/0.99                )
% 4.07/0.99  
% 4.07/0.99               | 
% 4.07/0.99              ? [X2,X3] : 
% 4.07/0.99                (
% 4.07/0.99                  ( X0_0=$i & X0=sK0(X2,X3) & X1=sK0(X2,X3) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X3!=k1_zfmisc_1(X3) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X3!=sK3 )
% 4.07/0.99                 &
% 4.07/0.99                  ( X3!=u1_struct_0(sK1) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X3!=u1_struct_0(sK2) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X3!=u1_struct_0(X3) )
% 4.07/0.99                )
% 4.07/0.99  
% 4.07/0.99               | 
% 4.07/0.99              ? [X2,X3] : 
% 4.07/0.99                (
% 4.07/0.99                  ( X0_0=$i & X0=k1_zfmisc_1(X2) & X1=k1_zfmisc_1(X3) )
% 4.07/0.99                )
% 4.07/0.99  
% 4.07/0.99               | 
% 4.07/0.99              ? [X2] : 
% 4.07/0.99                (
% 4.07/0.99                  ( X0_0=$i & X0=k1_zfmisc_1(X2) & X1=u1_struct_0(sK1) )
% 4.07/0.99                )
% 4.07/0.99  
% 4.07/0.99               | 
% 4.07/0.99              ? [X2] : 
% 4.07/0.99                (
% 4.07/0.99                  ( X0_0=$i & X0=k1_zfmisc_1(X2) & X1=k1_zfmisc_1(X2) )
% 4.07/0.99                )
% 4.07/0.99  
% 4.07/0.99               | 
% 4.07/0.99              ? [X2,X3] : 
% 4.07/0.99                (
% 4.07/0.99                  ( X0_0=$i & X0=k1_zfmisc_1(X2) & X1=u1_struct_0(X3) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X3!=sK1 )
% 4.07/0.99                 &
% 4.07/0.99                  ( X3!=sK2 )
% 4.07/0.99                )
% 4.07/0.99  
% 4.07/0.99               | 
% 4.07/0.99              ? [X2,X3] : 
% 4.07/0.99                (
% 4.07/0.99                  ( X0_0=$i & X0=u1_struct_0(X2) & X1=k1_zfmisc_1(X3) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X2!=sK1 )
% 4.07/0.99                 &
% 4.07/0.99                  ( X2!=sK2 )
% 4.07/0.99                )
% 4.07/0.99  
% 4.07/0.99               | 
% 4.07/0.99              ? [X2] : 
% 4.07/0.99                (
% 4.07/0.99                  ( X0_0=$i & X0=u1_struct_0(X2) & X1=u1_struct_0(sK1) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X2!=sK1 )
% 4.07/0.99                 &
% 4.07/0.99                  ( X2!=sK2 )
% 4.07/0.99                )
% 4.07/0.99  
% 4.07/0.99               | 
% 4.07/0.99              ? [X2,X3] : 
% 4.07/0.99                (
% 4.07/0.99                  ( X0_0=$i & X0=u1_struct_0(X2) & X1=u1_struct_0(X3) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X2!=sK1 )
% 4.07/0.99                 &
% 4.07/0.99                  ( X2!=sK1 | X3!=sK2 )
% 4.07/0.99                 &
% 4.07/0.99                  ( X2!=sK2 )
% 4.07/0.99                 &
% 4.07/0.99                  ( X2!=sK2 | X3!=sK1 )
% 4.07/0.99                 &
% 4.07/0.99                  ( X2!=k1_zfmisc_1(X2) | X3!=sK2 )
% 4.07/0.99                 &
% 4.07/0.99                  ( X3!=sK1 )
% 4.07/0.99                 &
% 4.07/0.99                  ( X3!=sK2 )
% 4.07/0.99                )
% 4.07/0.99  
% 4.07/0.99               | 
% 4.07/0.99              ? [X2] : 
% 4.07/0.99                (
% 4.07/0.99                  ( X0_0=$i & X0=u1_struct_0(X2) & X1=u1_struct_0(X2) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X2!=sK1 )
% 4.07/0.99                 &
% 4.07/0.99                  ( X2!=sK2 )
% 4.07/0.99                )
% 4.07/0.99  
% 4.07/0.99               | 
% 4.07/0.99              ? [X2] : 
% 4.07/0.99                (
% 4.07/0.99                  ( X0_0=$i & X0=sK0(X2,sK3) & X1=sK0(X2,sK3) )
% 4.07/0.99                )
% 4.07/0.99  
% 4.07/0.99               | 
% 4.07/0.99              ? [X2] : 
% 4.07/0.99                (
% 4.07/0.99                  ( X0_0=$i & X0=sK0(X2,u1_struct_0(sK2)) & X1=sK0(X2,u1_struct_0(sK2)) )
% 4.07/0.99                )
% 4.07/0.99  
% 4.07/0.99               | 
% 4.07/0.99              ? [X2,X3] : 
% 4.07/0.99                (
% 4.07/0.99                  ( X0_0=$i & X0=sK0(X2,k1_zfmisc_1(X3)) & X1=sK0(X2,k1_zfmisc_1(X3)) )
% 4.07/0.99                )
% 4.07/0.99  
% 4.07/0.99               | 
% 4.07/0.99              ? [X2] : 
% 4.07/0.99                (
% 4.07/0.99                  ( X0_0=$i & X0=sK0(X2,u1_struct_0(sK1)) & X1=sK0(X2,u1_struct_0(sK1)) )
% 4.07/0.99                )
% 4.07/0.99  
% 4.07/0.99               | 
% 4.07/0.99              ? [X2,X3] : 
% 4.07/0.99                (
% 4.07/0.99                  ( X0_0=$i & X0=sK0(X2,u1_struct_0(X3)) & X1=sK0(X2,u1_struct_0(X3)) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X3!=sK2 )
% 4.07/0.99                )
% 4.07/0.99  
% 4.07/0.99               | 
% 4.07/0.99                (
% 4.07/0.99                  ( X0_0=$i & X1=X0 )
% 4.07/0.99                 &
% 4.07/0.99                  ( X0!=k1_zfmisc_1(X0) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X0!=u1_struct_0(X0) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X0!=sK3 )
% 4.07/0.99                 &
% 4.07/0.99                  ( X0!=u1_struct_0(sK1) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X0!=sK2 )
% 4.07/0.99                 &
% 4.07/0.99                  ( X0!=u1_struct_0(sK2) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X0!=sK0(X0,sK3) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X0!=sK0(X0,u1_struct_0(sK2)) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X0!=sK0(X0,u1_struct_0(sK1)) )
% 4.07/0.99                 &
% 4.07/0.99                  ! [X2] : ( X0!=sK0(X0,X2) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X0!=sK0(X0,k1_zfmisc_1(X2)) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X0!=sK0(X0,u1_struct_0(X2)) )
% 4.07/0.99                )
% 4.07/0.99  
% 4.07/0.99             )
% 4.07/0.99        )
% 4.07/0.99      )
% 4.07/0.99     ).
% 4.07/0.99  
% 4.07/0.99  %------ Positive definition of r1_tarski 
% 4.07/0.99  fof(lit_def,axiom,
% 4.07/0.99      (! [X0,X1] : 
% 4.07/0.99        ( r1_tarski(X0,X1) <=>
% 4.07/0.99            $false
% 4.07/0.99        )
% 4.07/0.99      )
% 4.07/0.99     ).
% 4.07/0.99  
% 4.07/0.99  %------ Positive definition of r2_hidden 
% 4.07/0.99  fof(lit_def,axiom,
% 4.07/0.99      (! [X0,X1] : 
% 4.07/0.99        ( r2_hidden(X0,X1) <=>
% 4.07/0.99             (
% 4.07/0.99              ? [X2,X3] : 
% 4.07/0.99                (
% 4.07/0.99                  ( X0=sK0(X2,X3) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=k1_zfmisc_1(X1) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=k1_zfmisc_1(X3) | X3!=k1_zfmisc_1(X3) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=sK3 )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=u1_struct_0(sK1) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=u1_struct_0(sK1) | X3!=u1_struct_0(sK1) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=u1_struct_0(X1) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=k1_zfmisc_1(X2) | X2!=X2 )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=k1_zfmisc_1(X2) | X2!=X2 | X3!=u1_struct_0(sK2) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=u1_struct_0(X3) | X3!=u1_struct_0(sK2) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=u1_struct_0(X3) | X3!=u1_struct_0(X3) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X3!=k1_zfmisc_1(X3) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X3!=sK3 )
% 4.07/0.99                 &
% 4.07/0.99                  ( X3!=u1_struct_0(sK1) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X3!=u1_struct_0(sK2) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X3!=u1_struct_0(X3) )
% 4.07/0.99                )
% 4.07/0.99  
% 4.07/0.99               | 
% 4.07/0.99              ? [X2] : 
% 4.07/0.99                (
% 4.07/0.99                  ( X0=sK0(X2,sK3) & X1=sK3 )
% 4.07/0.99                )
% 4.07/0.99  
% 4.07/0.99               | 
% 4.07/0.99              ? [X2] : 
% 4.07/0.99                (
% 4.07/0.99                  ( X0=sK0(X2,u1_struct_0(sK2)) & X1=u1_struct_0(sK2) )
% 4.07/0.99                )
% 4.07/0.99  
% 4.07/0.99               | 
% 4.07/0.99              ? [X2] : 
% 4.07/0.99                (
% 4.07/0.99                  ( X0=sK0(X2,sK2) & X1=sK2 )
% 4.07/0.99                )
% 4.07/0.99  
% 4.07/0.99               | 
% 4.07/0.99              ? [X2] : 
% 4.07/0.99                (
% 4.07/0.99                  ( X0=sK0(X2,X1) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=k1_zfmisc_1(X1) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=sK3 )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=u1_struct_0(sK1) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=sK2 )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=u1_struct_0(sK2) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=u1_struct_0(X1) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=sK0(X1,sK3) )
% 4.07/0.99                )
% 4.07/0.99  
% 4.07/0.99               | 
% 4.07/0.99              ? [X2,X3] : 
% 4.07/0.99                (
% 4.07/0.99                  ( X0=sK0(X2,sK0(X3,sK3)) & X1=sK0(X3,sK3) )
% 4.07/0.99                )
% 4.07/0.99  
% 4.07/0.99             )
% 4.07/0.99        )
% 4.07/0.99      )
% 4.07/0.99     ).
% 4.07/0.99  
% 4.07/0.99  %------ Positive definition of m1_subset_1 
% 4.07/0.99  fof(lit_def,axiom,
% 4.07/0.99      (! [X0,X1] : 
% 4.07/0.99        ( m1_subset_1(X0,X1) <=>
% 4.07/0.99             (
% 4.07/0.99                (
% 4.07/0.99                  ( X0=sK3 & X1=u1_struct_0(sK2) )
% 4.07/0.99                )
% 4.07/0.99  
% 4.07/0.99               | 
% 4.07/0.99              ? [X2,X3] : 
% 4.07/0.99                (
% 4.07/0.99                  ( X0=sK0(X2,X3) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=k1_zfmisc_1(X1) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=k1_zfmisc_1(X3) | X3!=k1_zfmisc_1(X3) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=u1_struct_0(sK1) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=u1_struct_0(sK1) | X3!=sK3 )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=u1_struct_0(sK1) | X3!=u1_struct_0(sK1) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=u1_struct_0(sK1) | X3!=u1_struct_0(sK2) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=u1_struct_0(X1) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=k1_zfmisc_1(X2) | X2!=X2 | X3!=sK3 )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=u1_struct_0(X3) | X3!=u1_struct_0(sK2) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=u1_struct_0(X3) | X3!=u1_struct_0(X3) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X3!=k1_zfmisc_1(X3) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X3!=sK3 )
% 4.07/0.99                 &
% 4.07/0.99                  ( X3!=u1_struct_0(sK1) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X3!=u1_struct_0(sK2) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X3!=u1_struct_0(X3) )
% 4.07/0.99                )
% 4.07/0.99  
% 4.07/0.99               | 
% 4.07/0.99              ? [X2] : 
% 4.07/0.99                (
% 4.07/0.99                  ( X0=sK0(X2,sK3) & X1=sK3 )
% 4.07/0.99                )
% 4.07/0.99  
% 4.07/0.99               | 
% 4.07/0.99              ? [X2] : 
% 4.07/0.99                (
% 4.07/0.99                  ( X0=sK0(X2,u1_struct_0(sK2)) & X1=u1_struct_0(sK2) )
% 4.07/0.99                )
% 4.07/0.99  
% 4.07/0.99               | 
% 4.07/0.99              ? [X2] : 
% 4.07/0.99                (
% 4.07/0.99                  ( X0=sK0(X2,X1) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=k1_zfmisc_1(X1) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=sK3 )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=u1_struct_0(sK1) )
% 4.07/0.99                 &
% 4.07/0.99                  ( X1!=u1_struct_0(X1) )
% 4.07/0.99                )
% 4.07/0.99  
% 4.07/0.99             )
% 4.07/0.99        )
% 4.07/0.99      )
% 4.07/0.99     ).
% 4.07/0.99  
% 4.07/0.99  %------ Positive definition of v1_xboole_0 
% 4.07/0.99  fof(lit_def,axiom,
% 4.07/0.99      (! [X0] : 
% 4.07/0.99        ( v1_xboole_0(X0) <=>
% 4.07/0.99            $false
% 4.07/0.99        )
% 4.07/0.99      )
% 4.07/0.99     ).
% 4.07/0.99  
% 4.07/0.99  %------ Positive definition of v2_struct_0 
% 4.07/0.99  fof(lit_def,axiom,
% 4.07/0.99      (! [X0] : 
% 4.07/0.99        ( v2_struct_0(X0) <=>
% 4.07/0.99            $false
% 4.07/0.99        )
% 4.07/0.99      )
% 4.07/0.99     ).
% 4.07/0.99  
% 4.07/0.99  %------ Positive definition of l1_orders_2 
% 4.07/0.99  fof(lit_def,axiom,
% 4.07/0.99      (! [X0] : 
% 4.07/0.99        ( l1_orders_2(X0) <=>
% 4.07/0.99            $false
% 4.07/0.99        )
% 4.07/0.99      )
% 4.07/0.99     ).
% 4.07/0.99  % SZS output end Model for theBenchmark.p
% 4.07/0.99  ------                               Statistics
% 4.07/0.99  
% 4.07/0.99  ------ Selected
% 4.07/0.99  
% 4.07/0.99  total_time:                             0.435
% 4.07/0.99  
%------------------------------------------------------------------------------
