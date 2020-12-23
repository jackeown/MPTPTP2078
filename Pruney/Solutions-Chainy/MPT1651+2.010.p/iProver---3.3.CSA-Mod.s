%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:20:55 EST 2020

% Result     : CounterSatisfiable 1.98s
% Output     : Model 1.98s
% Verified   : 
% Statistics : Number of formulae       :    4 (   4 expanded)
%              Number of leaves         :    4 (   4 expanded)
%              Depth                    :    0
%              Number of atoms          :   14 (  14 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    9 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%------ Negative definition of r2_lattice3 
fof(lit_def,axiom,(
    ! [X0_43,X0_45,X0_44] :
      ( ~ r2_lattice3(X0_43,X0_45,X0_44)
    <=> ( ( X0_43 = sK1
          & X0_45 = k3_waybel_0(sK1,sK2) )
        | ( X0_43 = sK1
          & X0_45 = k3_waybel_0(sK1,sK2)
          & X0_44 = sK3 )
        | ? [X1_44] :
            ( X0_43 = sK1
            & X0_45 = k1_tarski(X1_44) ) ) ) )).

%------ Positive definition of r1_orders_2 
fof(lit_def_001,axiom,(
    ! [X0_43,X0_44,X1_44] :
      ( r1_orders_2(X0_43,X0_44,X1_44)
    <=> $false ) )).

%------ Negative definition of m1_subset_1 
fof(lit_def_002,axiom,(
    ! [X0_45,X0] :
      ( ~ m1_subset_1(X0_45,X0)
    <=> $false ) )).

%------ Positive definition of r1_lattice3 
fof(lit_def_003,axiom,(
    ! [X0_43,X0_45,X0_44] :
      ( r1_lattice3(X0_43,X0_45,X0_44)
    <=> $false ) )).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:28:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.98/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/0.99  
% 1.98/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.98/0.99  
% 1.98/0.99  ------  iProver source info
% 1.98/0.99  
% 1.98/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.98/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.98/0.99  git: non_committed_changes: false
% 1.98/0.99  git: last_make_outside_of_git: false
% 1.98/0.99  
% 1.98/0.99  ------ 
% 1.98/0.99  ------ Parsing...
% 1.98/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.98/0.99  
% 1.98/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 0 0s  sf_e  pe_s  pe_e 
% 1.98/0.99  
% 1.98/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.98/0.99  ------ Proving...
% 1.98/0.99  ------ Problem Properties 
% 1.98/0.99  
% 1.98/0.99  
% 1.98/0.99  clauses                                 12
% 1.98/0.99  conjectures                             3
% 1.98/0.99  EPR                                     0
% 1.98/0.99  Horn                                    9
% 1.98/0.99  unary                                   1
% 1.98/0.99  binary                                  2
% 1.98/0.99  lits                                    42
% 1.98/0.99  lits eq                                 0
% 1.98/0.99  fd_pure                                 0
% 1.98/0.99  fd_pseudo                               0
% 1.98/0.99  fd_cond                                 0
% 1.98/0.99  fd_pseudo_cond                          0
% 1.98/0.99  AC symbols                              0
% 1.98/0.99  
% 1.98/0.99  ------ Input Options Time Limit: Unbounded
% 1.98/0.99  
% 1.98/0.99  
% 1.98/0.99  ------ 
% 1.98/0.99  Current options:
% 1.98/0.99  ------ 
% 1.98/0.99  
% 1.98/0.99  
% 1.98/0.99  
% 1.98/0.99  
% 1.98/0.99  ------ Proving...
% 1.98/0.99  
% 1.98/0.99  
% 1.98/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 1.98/0.99  
% 1.98/0.99  ------ Building Model...Done
% 1.98/0.99  
% 1.98/0.99  %------ The model is defined over ground terms (initial term algebra).
% 1.98/0.99  %------ Predicates are defined as (\forall x_1,..,x_n  ((~)P(x_1,..,x_n) <=> (\phi(x_1,..,x_n)))) 
% 1.98/0.99  %------ where \phi is a formula over the term algebra.
% 1.98/0.99  %------ If we have equality in the problem then it is also defined as a predicate above, 
% 1.98/0.99  %------ with "=" on the right-hand-side of the definition interpreted over the term algebra term_algebra_type
% 1.98/0.99  %------ See help for --sat_out_model for different model outputs.
% 1.98/0.99  %------ equality_sorted(X0,X1,X2) can be used in the place of usual "="
% 1.98/0.99  %------ where the first argument stands for the sort ($i in the unsorted case)
% 1.98/0.99  % SZS output start Model for theBenchmark.p
% 1.98/0.99  
% 1.98/0.99  %------ Negative definition of r2_lattice3 
% 1.98/0.99  fof(lit_def,axiom,
% 1.98/0.99      (! [X0_43,X0_45,X0_44] : 
% 1.98/0.99        ( ~(r2_lattice3(X0_43,X0_45,X0_44)) <=>
% 1.98/0.99             (
% 1.98/0.99                (
% 1.98/0.99                  ( X0_43=sK1 & X0_45=k3_waybel_0(sK1,sK2) )
% 1.98/0.99                )
% 1.98/0.99  
% 1.98/0.99               | 
% 1.98/0.99                (
% 1.98/0.99                  ( X0_43=sK1 & X0_45=k3_waybel_0(sK1,sK2) & X0_44=sK3 )
% 1.98/0.99                )
% 1.98/0.99  
% 1.98/0.99               | 
% 1.98/0.99              ? [X1_44] : 
% 1.98/0.99                (
% 1.98/0.99                  ( X0_43=sK1 & X0_45=k1_tarski(X1_44) )
% 1.98/0.99                )
% 1.98/0.99  
% 1.98/0.99             )
% 1.98/0.99        )
% 1.98/0.99      )
% 1.98/0.99     ).
% 1.98/0.99  
% 1.98/0.99  %------ Positive definition of r1_orders_2 
% 1.98/0.99  fof(lit_def,axiom,
% 1.98/0.99      (! [X0_43,X0_44,X1_44] : 
% 1.98/0.99        ( r1_orders_2(X0_43,X0_44,X1_44) <=>
% 1.98/0.99            $false
% 1.98/0.99        )
% 1.98/0.99      )
% 1.98/0.99     ).
% 1.98/0.99  
% 1.98/0.99  %------ Negative definition of m1_subset_1 
% 1.98/0.99  fof(lit_def,axiom,
% 1.98/0.99      (! [X0_45,X0] : 
% 1.98/0.99        ( ~(m1_subset_1(X0_45,X0)) <=>
% 1.98/0.99            $false
% 1.98/0.99        )
% 1.98/0.99      )
% 1.98/0.99     ).
% 1.98/0.99  
% 1.98/0.99  %------ Positive definition of r1_lattice3 
% 1.98/0.99  fof(lit_def,axiom,
% 1.98/0.99      (! [X0_43,X0_45,X0_44] : 
% 1.98/0.99        ( r1_lattice3(X0_43,X0_45,X0_44) <=>
% 1.98/0.99            $false
% 1.98/0.99        )
% 1.98/0.99      )
% 1.98/0.99     ).
% 1.98/0.99  % SZS output end Model for theBenchmark.p
% 1.98/0.99  ------                               Statistics
% 1.98/0.99  
% 1.98/0.99  ------ Selected
% 1.98/0.99  
% 1.98/0.99  total_time:                             0.058
% 1.98/0.99  
%------------------------------------------------------------------------------
