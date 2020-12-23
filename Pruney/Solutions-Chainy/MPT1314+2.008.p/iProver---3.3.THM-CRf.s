%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:42 EST 2020

% Result     : Theorem 35.55s
% Output     : CNFRefutation 35.55s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 317 expanded)
%              Number of clauses        :   79 ( 110 expanded)
%              Number of leaves         :   20 ( 104 expanded)
%              Depth                    :   13
%              Number of atoms          :  420 (1611 expanded)
%              Number of equality atoms :  153 ( 373 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f52,f51])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f88,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f12,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( v3_pre_topc(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( X1 = X3
                       => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f44,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ v3_pre_topc(X3,X2)
          & X1 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( ~ v3_pre_topc(sK9,X2)
        & sK9 = X1
        & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ v3_pre_topc(X3,X2)
              & X1 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
          & v3_pre_topc(X1,X0)
          & m1_pre_topc(X2,X0) )
     => ( ? [X3] :
            ( ~ v3_pre_topc(X3,sK8)
            & X1 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK8))) )
        & v3_pre_topc(X1,X0)
        & m1_pre_topc(sK8,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ v3_pre_topc(X3,X2)
                & sK7 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
            & v3_pre_topc(sK7,X0)
            & m1_pre_topc(X2,X0) )
        & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v3_pre_topc(X3,X2)
                    & X1 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
                & v3_pre_topc(X1,X0)
                & m1_pre_topc(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,sK6)
              & m1_pre_topc(X2,sK6) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) )
      & l1_pre_topc(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ~ v3_pre_topc(sK9,sK8)
    & sK7 = sK9
    & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    & v3_pre_topc(sK7,sK6)
    & m1_pre_topc(sK8,sK6)
    & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))
    & l1_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f22,f44,f43,f42,f41])).

fof(f77,plain,(
    m1_pre_topc(sK8,sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f70,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f75,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f69,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f55,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f79,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f45])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v3_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                      & v3_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f37])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2),k2_struct_0(X1)) = X2
        & v3_pre_topc(sK5(X0,X1,X2),X0)
        & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2),k2_struct_0(X1)) = X2
                    & v3_pre_topc(sK5(X0,X1,X2),X0)
                    & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v3_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X1)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f74])).

fof(f81,plain,(
    ~ v3_pre_topc(sK9,sK8) ),
    inference(cnf_transformation,[],[f45])).

fof(f78,plain,(
    v3_pre_topc(sK7,sK6) ),
    inference(cnf_transformation,[],[f45])).

fof(f80,plain,(
    sK7 = sK9 ),
    inference(cnf_transformation,[],[f45])).

fof(f85,plain,(
    v3_pre_topc(sK9,sK6) ),
    inference(definition_unfolding,[],[f78,f80])).

fof(f76,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f45])).

fof(f86,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(definition_unfolding,[],[f76,f80])).

cnf(c_3000,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_79130,plain,
    ( X0 != X1
    | sK9 != X1
    | sK9 = X0 ),
    inference(instantiation,[status(thm)],[c_3000])).

cnf(c_79935,plain,
    ( X0 != sK9
    | sK9 = X0
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_79130])).

cnf(c_80215,plain,
    ( k4_xboole_0(sK9,k4_xboole_0(sK9,X0)) != sK9
    | sK9 = k4_xboole_0(sK9,k4_xboole_0(sK9,X0))
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_79935])).

cnf(c_126254,plain,
    ( k4_xboole_0(sK9,k4_xboole_0(sK9,k2_struct_0(sK8))) != sK9
    | sK9 = k4_xboole_0(sK9,k4_xboole_0(sK9,k2_struct_0(sK8)))
    | sK9 != sK9 ),
    inference(instantiation,[status(thm)],[c_80215])).

cnf(c_3005,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_78048,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k9_subset_1(u1_struct_0(sK8),X2,k2_struct_0(sK8)),k1_zfmisc_1(u1_struct_0(sK8)))
    | k9_subset_1(u1_struct_0(sK8),X2,k2_struct_0(sK8)) != X0
    | k1_zfmisc_1(u1_struct_0(sK8)) != X1 ),
    inference(instantiation,[status(thm)],[c_3005])).

cnf(c_78213,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | m1_subset_1(k9_subset_1(u1_struct_0(sK8),X1,k2_struct_0(sK8)),k1_zfmisc_1(u1_struct_0(sK8)))
    | k9_subset_1(u1_struct_0(sK8),X1,k2_struct_0(sK8)) != X0
    | k1_zfmisc_1(u1_struct_0(sK8)) != k1_zfmisc_1(u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_78048])).

cnf(c_97438,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK8),X0,k2_struct_0(sK8)),k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(k4_xboole_0(X0,k4_xboole_0(X0,k2_struct_0(sK8))),k1_zfmisc_1(u1_struct_0(sK8)))
    | k9_subset_1(u1_struct_0(sK8),X0,k2_struct_0(sK8)) != k4_xboole_0(X0,k4_xboole_0(X0,k2_struct_0(sK8)))
    | k1_zfmisc_1(u1_struct_0(sK8)) != k1_zfmisc_1(u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_78213])).

cnf(c_125470,plain,
    ( m1_subset_1(k9_subset_1(u1_struct_0(sK8),sK9,k2_struct_0(sK8)),k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(k4_xboole_0(sK9,k4_xboole_0(sK9,k2_struct_0(sK8))),k1_zfmisc_1(u1_struct_0(sK8)))
    | k9_subset_1(u1_struct_0(sK8),sK9,k2_struct_0(sK8)) != k4_xboole_0(sK9,k4_xboole_0(sK9,k2_struct_0(sK8)))
    | k1_zfmisc_1(u1_struct_0(sK8)) != k1_zfmisc_1(u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_97438])).

cnf(c_85852,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
    | X2 != X0
    | k1_zfmisc_1(u1_struct_0(sK8)) != X1 ),
    inference(instantiation,[status(thm)],[c_3005])).

cnf(c_96898,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
    | X1 != X0
    | k1_zfmisc_1(u1_struct_0(sK8)) != k1_zfmisc_1(u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_85852])).

cnf(c_117474,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | X0 != sK9
    | k1_zfmisc_1(u1_struct_0(sK8)) != k1_zfmisc_1(u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_96898])).

cnf(c_124239,plain,
    ( m1_subset_1(k4_xboole_0(sK9,k4_xboole_0(sK9,X0)),k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | k4_xboole_0(sK9,k4_xboole_0(sK9,X0)) != sK9
    | k1_zfmisc_1(u1_struct_0(sK8)) != k1_zfmisc_1(u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_117474])).

cnf(c_125469,plain,
    ( m1_subset_1(k4_xboole_0(sK9,k4_xboole_0(sK9,k2_struct_0(sK8))),k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
    | k4_xboole_0(sK9,k4_xboole_0(sK9,k2_struct_0(sK8))) != sK9
    | k1_zfmisc_1(u1_struct_0(sK8)) != k1_zfmisc_1(u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_124239])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_258,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_259,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_258])).

cnf(c_319,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_259])).

cnf(c_86540,plain,
    ( ~ r1_tarski(k2_struct_0(sK8),u1_struct_0(sK8))
    | k4_xboole_0(X0,k4_xboole_0(X0,k2_struct_0(sK8))) = k9_subset_1(u1_struct_0(sK8),X0,k2_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_319])).

cnf(c_105948,plain,
    ( ~ r1_tarski(k2_struct_0(sK8),u1_struct_0(sK8))
    | k4_xboole_0(sK9,k4_xboole_0(sK9,k2_struct_0(sK8))) = k9_subset_1(u1_struct_0(sK8),sK9,k2_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_86540])).

cnf(c_2999,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_101743,plain,
    ( k9_subset_1(u1_struct_0(sK8),sK9,k2_struct_0(sK8)) = k9_subset_1(u1_struct_0(sK8),sK9,k2_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_2999])).

cnf(c_82258,plain,
    ( X0 != k4_xboole_0(sK9,k4_xboole_0(sK9,X1))
    | sK9 = X0
    | sK9 != k4_xboole_0(sK9,k4_xboole_0(sK9,X1)) ),
    inference(instantiation,[status(thm)],[c_79130])).

cnf(c_97453,plain,
    ( k9_subset_1(u1_struct_0(sK8),sK9,k2_struct_0(sK8)) != k4_xboole_0(sK9,k4_xboole_0(sK9,k2_struct_0(sK8)))
    | sK9 = k9_subset_1(u1_struct_0(sK8),sK9,k2_struct_0(sK8))
    | sK9 != k4_xboole_0(sK9,k4_xboole_0(sK9,k2_struct_0(sK8))) ),
    inference(instantiation,[status(thm)],[c_82258])).

cnf(c_78496,plain,
    ( X0 != X1
    | k9_subset_1(u1_struct_0(sK8),X2,k2_struct_0(sK8)) != X1
    | k9_subset_1(u1_struct_0(sK8),X2,k2_struct_0(sK8)) = X0 ),
    inference(instantiation,[status(thm)],[c_3000])).

cnf(c_79445,plain,
    ( X0 != k9_subset_1(u1_struct_0(sK8),X1,k2_struct_0(sK8))
    | k9_subset_1(u1_struct_0(sK8),X1,k2_struct_0(sK8)) = X0
    | k9_subset_1(u1_struct_0(sK8),X1,k2_struct_0(sK8)) != k9_subset_1(u1_struct_0(sK8),X1,k2_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_78496])).

cnf(c_81287,plain,
    ( k9_subset_1(u1_struct_0(sK8),X0,k2_struct_0(sK8)) != k9_subset_1(u1_struct_0(sK8),X0,k2_struct_0(sK8))
    | k9_subset_1(u1_struct_0(sK8),X0,k2_struct_0(sK8)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_struct_0(sK8)))
    | k4_xboole_0(X0,k4_xboole_0(X0,k2_struct_0(sK8))) != k9_subset_1(u1_struct_0(sK8),X0,k2_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_79445])).

cnf(c_97451,plain,
    ( k9_subset_1(u1_struct_0(sK8),sK9,k2_struct_0(sK8)) != k9_subset_1(u1_struct_0(sK8),sK9,k2_struct_0(sK8))
    | k9_subset_1(u1_struct_0(sK8),sK9,k2_struct_0(sK8)) = k4_xboole_0(sK9,k4_xboole_0(sK9,k2_struct_0(sK8)))
    | k4_xboole_0(sK9,k4_xboole_0(sK9,k2_struct_0(sK8))) != k9_subset_1(u1_struct_0(sK8),sK9,k2_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_81287])).

cnf(c_3002,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_5708,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,u1_struct_0(sK8))
    | X2 != X0
    | u1_struct_0(sK8) != X1 ),
    inference(instantiation,[status(thm)],[c_3002])).

cnf(c_8530,plain,
    ( r1_tarski(X0,u1_struct_0(sK8))
    | ~ r1_tarski(X1,k2_struct_0(sK8))
    | X0 != X1
    | u1_struct_0(sK8) != k2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_5708])).

cnf(c_15625,plain,
    ( r1_tarski(X0,u1_struct_0(sK8))
    | ~ r1_tarski(k2_struct_0(sK8),k2_struct_0(sK8))
    | X0 != k2_struct_0(sK8)
    | u1_struct_0(sK8) != k2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_8530])).

cnf(c_26739,plain,
    ( r1_tarski(k2_struct_0(sK8),u1_struct_0(sK8))
    | ~ r1_tarski(k2_struct_0(sK8),k2_struct_0(sK8))
    | u1_struct_0(sK8) != k2_struct_0(sK8)
    | k2_struct_0(sK8) != k2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_15625])).

cnf(c_13810,plain,
    ( k2_struct_0(sK8) = k2_struct_0(sK8) ),
    inference(instantiation,[status(thm)],[c_2999])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_5416,plain,
    ( r1_tarski(k2_struct_0(X0),k2_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_10714,plain,
    ( r1_tarski(k2_struct_0(sK8),k2_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_5416])).

cnf(c_4983,plain,
    ( k1_zfmisc_1(u1_struct_0(sK8)) = k1_zfmisc_1(u1_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_2999])).

cnf(c_31,negated_conjecture,
    ( m1_pre_topc(sK8,sK6) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3668,plain,
    ( m1_pre_topc(sK8,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_23,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3676,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4617,plain,
    ( l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_3668,c_3676])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_34,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_603,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK6 != X0
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_31])).

cnf(c_604,plain,
    ( ~ l1_pre_topc(sK6)
    | l1_pre_topc(sK8) ),
    inference(unflattening,[status(thm)],[c_603])).

cnf(c_605,plain,
    ( l1_pre_topc(sK6) != iProver_top
    | l1_pre_topc(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_604])).

cnf(c_4818,plain,
    ( l1_pre_topc(sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4617,c_34,c_605])).

cnf(c_22,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_8,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_433,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_22,c_8])).

cnf(c_3664,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_433])).

cnf(c_4822,plain,
    ( u1_struct_0(sK8) = k2_struct_0(sK8) ),
    inference(superposition,[status(thm)],[c_4818,c_3664])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_3670,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_3687,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4048,plain,
    ( r1_tarski(sK9,u1_struct_0(sK8)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3670,c_3687])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3689,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4188,plain,
    ( k4_xboole_0(sK9,k4_xboole_0(sK9,u1_struct_0(sK8))) = sK9 ),
    inference(superposition,[status(thm)],[c_4048,c_3689])).

cnf(c_4882,plain,
    ( k4_xboole_0(sK9,k4_xboole_0(sK9,k2_struct_0(sK8))) = sK9 ),
    inference(demodulation,[status(thm)],[c_4822,c_4188])).

cnf(c_3010,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3728,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(sK9,sK8)
    | sK8 != X1
    | sK9 != X0 ),
    inference(instantiation,[status(thm)],[c_3010])).

cnf(c_3736,plain,
    ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,k2_struct_0(X0)),X0)
    | v3_pre_topc(sK9,sK8)
    | sK8 != X0
    | sK9 != k9_subset_1(u1_struct_0(X0),X1,k2_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_3728])).

cnf(c_3757,plain,
    ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(sK8),X0,k2_struct_0(sK8)),sK8)
    | v3_pre_topc(sK9,sK8)
    | sK8 != sK8
    | sK9 != k9_subset_1(u1_struct_0(sK8),X0,k2_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_3736])).

cnf(c_4305,plain,
    ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(sK8),sK9,k2_struct_0(sK8)),sK8)
    | v3_pre_topc(sK9,sK8)
    | sK8 != sK8
    | sK9 != k9_subset_1(u1_struct_0(sK8),sK9,k2_struct_0(sK8)) ),
    inference(instantiation,[status(thm)],[c_3757])).

cnf(c_24,plain,
    ( ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_4086,plain,
    ( v3_pre_topc(k9_subset_1(u1_struct_0(X0),sK9,k2_struct_0(X0)),X0)
    | ~ v3_pre_topc(sK9,sK6)
    | ~ m1_pre_topc(X0,sK6)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),sK9,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_4304,plain,
    ( v3_pre_topc(k9_subset_1(u1_struct_0(sK8),sK9,k2_struct_0(sK8)),sK8)
    | ~ v3_pre_topc(sK9,sK6)
    | ~ m1_pre_topc(sK8,sK6)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK8),sK9,k2_struct_0(sK8)),k1_zfmisc_1(u1_struct_0(sK8)))
    | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6)))
    | ~ l1_pre_topc(sK6) ),
    inference(instantiation,[status(thm)],[c_4086])).

cnf(c_3973,plain,
    ( sK9 = sK9 ),
    inference(instantiation,[status(thm)],[c_2999])).

cnf(c_3785,plain,
    ( sK8 = sK8 ),
    inference(instantiation,[status(thm)],[c_2999])).

cnf(c_28,negated_conjecture,
    ( ~ v3_pre_topc(sK9,sK8) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_30,negated_conjecture,
    ( v3_pre_topc(sK9,sK6) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(cnf_transformation,[],[f86])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_126254,c_125470,c_125469,c_105948,c_101743,c_97453,c_97451,c_26739,c_13810,c_10714,c_4983,c_4882,c_4822,c_4305,c_4304,c_3973,c_3785,c_28,c_29,c_30,c_31,c_32,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:38:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 35.55/5.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 35.55/5.00  
% 35.55/5.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 35.55/5.00  
% 35.55/5.00  ------  iProver source info
% 35.55/5.00  
% 35.55/5.00  git: date: 2020-06-30 10:37:57 +0100
% 35.55/5.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 35.55/5.00  git: non_committed_changes: false
% 35.55/5.00  git: last_make_outside_of_git: false
% 35.55/5.00  
% 35.55/5.00  ------ 
% 35.55/5.00  
% 35.55/5.00  ------ Input Options
% 35.55/5.00  
% 35.55/5.00  --out_options                           all
% 35.55/5.00  --tptp_safe_out                         true
% 35.55/5.00  --problem_path                          ""
% 35.55/5.00  --include_path                          ""
% 35.55/5.00  --clausifier                            res/vclausify_rel
% 35.55/5.00  --clausifier_options                    ""
% 35.55/5.00  --stdin                                 false
% 35.55/5.00  --stats_out                             all
% 35.55/5.00  
% 35.55/5.00  ------ General Options
% 35.55/5.00  
% 35.55/5.00  --fof                                   false
% 35.55/5.00  --time_out_real                         305.
% 35.55/5.00  --time_out_virtual                      -1.
% 35.55/5.00  --symbol_type_check                     false
% 35.55/5.00  --clausify_out                          false
% 35.55/5.00  --sig_cnt_out                           false
% 35.55/5.00  --trig_cnt_out                          false
% 35.55/5.00  --trig_cnt_out_tolerance                1.
% 35.55/5.00  --trig_cnt_out_sk_spl                   false
% 35.55/5.00  --abstr_cl_out                          false
% 35.55/5.00  
% 35.55/5.00  ------ Global Options
% 35.55/5.00  
% 35.55/5.00  --schedule                              default
% 35.55/5.00  --add_important_lit                     false
% 35.55/5.00  --prop_solver_per_cl                    1000
% 35.55/5.00  --min_unsat_core                        false
% 35.55/5.00  --soft_assumptions                      false
% 35.55/5.00  --soft_lemma_size                       3
% 35.55/5.00  --prop_impl_unit_size                   0
% 35.55/5.00  --prop_impl_unit                        []
% 35.55/5.00  --share_sel_clauses                     true
% 35.55/5.00  --reset_solvers                         false
% 35.55/5.00  --bc_imp_inh                            [conj_cone]
% 35.55/5.00  --conj_cone_tolerance                   3.
% 35.55/5.00  --extra_neg_conj                        none
% 35.55/5.00  --large_theory_mode                     true
% 35.55/5.00  --prolific_symb_bound                   200
% 35.55/5.00  --lt_threshold                          2000
% 35.55/5.00  --clause_weak_htbl                      true
% 35.55/5.00  --gc_record_bc_elim                     false
% 35.55/5.00  
% 35.55/5.00  ------ Preprocessing Options
% 35.55/5.00  
% 35.55/5.00  --preprocessing_flag                    true
% 35.55/5.00  --time_out_prep_mult                    0.1
% 35.55/5.00  --splitting_mode                        input
% 35.55/5.00  --splitting_grd                         true
% 35.55/5.00  --splitting_cvd                         false
% 35.55/5.00  --splitting_cvd_svl                     false
% 35.55/5.00  --splitting_nvd                         32
% 35.55/5.00  --sub_typing                            true
% 35.55/5.00  --prep_gs_sim                           true
% 35.55/5.00  --prep_unflatten                        true
% 35.55/5.00  --prep_res_sim                          true
% 35.55/5.00  --prep_upred                            true
% 35.55/5.00  --prep_sem_filter                       exhaustive
% 35.55/5.00  --prep_sem_filter_out                   false
% 35.55/5.00  --pred_elim                             true
% 35.55/5.00  --res_sim_input                         true
% 35.55/5.00  --eq_ax_congr_red                       true
% 35.55/5.00  --pure_diseq_elim                       true
% 35.55/5.00  --brand_transform                       false
% 35.55/5.00  --non_eq_to_eq                          false
% 35.55/5.00  --prep_def_merge                        true
% 35.55/5.00  --prep_def_merge_prop_impl              false
% 35.55/5.00  --prep_def_merge_mbd                    true
% 35.55/5.00  --prep_def_merge_tr_red                 false
% 35.55/5.00  --prep_def_merge_tr_cl                  false
% 35.55/5.00  --smt_preprocessing                     true
% 35.55/5.00  --smt_ac_axioms                         fast
% 35.55/5.00  --preprocessed_out                      false
% 35.55/5.00  --preprocessed_stats                    false
% 35.55/5.00  
% 35.55/5.00  ------ Abstraction refinement Options
% 35.55/5.00  
% 35.55/5.00  --abstr_ref                             []
% 35.55/5.00  --abstr_ref_prep                        false
% 35.55/5.00  --abstr_ref_until_sat                   false
% 35.55/5.00  --abstr_ref_sig_restrict                funpre
% 35.55/5.00  --abstr_ref_af_restrict_to_split_sk     false
% 35.55/5.00  --abstr_ref_under                       []
% 35.55/5.00  
% 35.55/5.00  ------ SAT Options
% 35.55/5.00  
% 35.55/5.00  --sat_mode                              false
% 35.55/5.00  --sat_fm_restart_options                ""
% 35.55/5.00  --sat_gr_def                            false
% 35.55/5.00  --sat_epr_types                         true
% 35.55/5.00  --sat_non_cyclic_types                  false
% 35.55/5.00  --sat_finite_models                     false
% 35.55/5.00  --sat_fm_lemmas                         false
% 35.55/5.00  --sat_fm_prep                           false
% 35.55/5.00  --sat_fm_uc_incr                        true
% 35.55/5.00  --sat_out_model                         small
% 35.55/5.00  --sat_out_clauses                       false
% 35.55/5.00  
% 35.55/5.00  ------ QBF Options
% 35.55/5.00  
% 35.55/5.00  --qbf_mode                              false
% 35.55/5.00  --qbf_elim_univ                         false
% 35.55/5.00  --qbf_dom_inst                          none
% 35.55/5.00  --qbf_dom_pre_inst                      false
% 35.55/5.00  --qbf_sk_in                             false
% 35.55/5.00  --qbf_pred_elim                         true
% 35.55/5.00  --qbf_split                             512
% 35.55/5.00  
% 35.55/5.00  ------ BMC1 Options
% 35.55/5.00  
% 35.55/5.00  --bmc1_incremental                      false
% 35.55/5.00  --bmc1_axioms                           reachable_all
% 35.55/5.00  --bmc1_min_bound                        0
% 35.55/5.00  --bmc1_max_bound                        -1
% 35.55/5.00  --bmc1_max_bound_default                -1
% 35.55/5.00  --bmc1_symbol_reachability              true
% 35.55/5.00  --bmc1_property_lemmas                  false
% 35.55/5.00  --bmc1_k_induction                      false
% 35.55/5.00  --bmc1_non_equiv_states                 false
% 35.55/5.00  --bmc1_deadlock                         false
% 35.55/5.00  --bmc1_ucm                              false
% 35.55/5.00  --bmc1_add_unsat_core                   none
% 35.55/5.00  --bmc1_unsat_core_children              false
% 35.55/5.00  --bmc1_unsat_core_extrapolate_axioms    false
% 35.55/5.00  --bmc1_out_stat                         full
% 35.55/5.00  --bmc1_ground_init                      false
% 35.55/5.00  --bmc1_pre_inst_next_state              false
% 35.55/5.00  --bmc1_pre_inst_state                   false
% 35.55/5.00  --bmc1_pre_inst_reach_state             false
% 35.55/5.00  --bmc1_out_unsat_core                   false
% 35.55/5.00  --bmc1_aig_witness_out                  false
% 35.55/5.00  --bmc1_verbose                          false
% 35.55/5.00  --bmc1_dump_clauses_tptp                false
% 35.55/5.00  --bmc1_dump_unsat_core_tptp             false
% 35.55/5.00  --bmc1_dump_file                        -
% 35.55/5.00  --bmc1_ucm_expand_uc_limit              128
% 35.55/5.00  --bmc1_ucm_n_expand_iterations          6
% 35.55/5.00  --bmc1_ucm_extend_mode                  1
% 35.55/5.00  --bmc1_ucm_init_mode                    2
% 35.55/5.00  --bmc1_ucm_cone_mode                    none
% 35.55/5.00  --bmc1_ucm_reduced_relation_type        0
% 35.55/5.00  --bmc1_ucm_relax_model                  4
% 35.55/5.00  --bmc1_ucm_full_tr_after_sat            true
% 35.55/5.00  --bmc1_ucm_expand_neg_assumptions       false
% 35.55/5.00  --bmc1_ucm_layered_model                none
% 35.55/5.00  --bmc1_ucm_max_lemma_size               10
% 35.55/5.00  
% 35.55/5.00  ------ AIG Options
% 35.55/5.00  
% 35.55/5.00  --aig_mode                              false
% 35.55/5.00  
% 35.55/5.00  ------ Instantiation Options
% 35.55/5.00  
% 35.55/5.00  --instantiation_flag                    true
% 35.55/5.00  --inst_sos_flag                         true
% 35.55/5.00  --inst_sos_phase                        true
% 35.55/5.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.55/5.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.55/5.00  --inst_lit_sel_side                     num_symb
% 35.55/5.00  --inst_solver_per_active                1400
% 35.55/5.00  --inst_solver_calls_frac                1.
% 35.55/5.00  --inst_passive_queue_type               priority_queues
% 35.55/5.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.55/5.00  --inst_passive_queues_freq              [25;2]
% 35.55/5.00  --inst_dismatching                      true
% 35.55/5.00  --inst_eager_unprocessed_to_passive     true
% 35.55/5.00  --inst_prop_sim_given                   true
% 35.55/5.00  --inst_prop_sim_new                     false
% 35.55/5.00  --inst_subs_new                         false
% 35.55/5.00  --inst_eq_res_simp                      false
% 35.55/5.00  --inst_subs_given                       false
% 35.55/5.00  --inst_orphan_elimination               true
% 35.55/5.00  --inst_learning_loop_flag               true
% 35.55/5.00  --inst_learning_start                   3000
% 35.55/5.00  --inst_learning_factor                  2
% 35.55/5.00  --inst_start_prop_sim_after_learn       3
% 35.55/5.00  --inst_sel_renew                        solver
% 35.55/5.00  --inst_lit_activity_flag                true
% 35.55/5.00  --inst_restr_to_given                   false
% 35.55/5.00  --inst_activity_threshold               500
% 35.55/5.00  --inst_out_proof                        true
% 35.55/5.00  
% 35.55/5.00  ------ Resolution Options
% 35.55/5.00  
% 35.55/5.00  --resolution_flag                       true
% 35.55/5.00  --res_lit_sel                           adaptive
% 35.55/5.00  --res_lit_sel_side                      none
% 35.55/5.00  --res_ordering                          kbo
% 35.55/5.00  --res_to_prop_solver                    active
% 35.55/5.00  --res_prop_simpl_new                    false
% 35.55/5.00  --res_prop_simpl_given                  true
% 35.55/5.00  --res_passive_queue_type                priority_queues
% 35.55/5.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.55/5.00  --res_passive_queues_freq               [15;5]
% 35.55/5.00  --res_forward_subs                      full
% 35.55/5.00  --res_backward_subs                     full
% 35.55/5.00  --res_forward_subs_resolution           true
% 35.55/5.00  --res_backward_subs_resolution          true
% 35.55/5.00  --res_orphan_elimination                true
% 35.55/5.00  --res_time_limit                        2.
% 35.55/5.00  --res_out_proof                         true
% 35.55/5.00  
% 35.55/5.00  ------ Superposition Options
% 35.55/5.00  
% 35.55/5.00  --superposition_flag                    true
% 35.55/5.00  --sup_passive_queue_type                priority_queues
% 35.55/5.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.55/5.00  --sup_passive_queues_freq               [8;1;4]
% 35.55/5.00  --demod_completeness_check              fast
% 35.55/5.00  --demod_use_ground                      true
% 35.55/5.00  --sup_to_prop_solver                    passive
% 35.55/5.00  --sup_prop_simpl_new                    true
% 35.55/5.00  --sup_prop_simpl_given                  true
% 35.55/5.00  --sup_fun_splitting                     true
% 35.55/5.00  --sup_smt_interval                      50000
% 35.55/5.00  
% 35.55/5.00  ------ Superposition Simplification Setup
% 35.55/5.00  
% 35.55/5.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.55/5.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.55/5.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.55/5.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.55/5.00  --sup_full_triv                         [TrivRules;PropSubs]
% 35.55/5.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.55/5.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.55/5.00  --sup_immed_triv                        [TrivRules]
% 35.55/5.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.55/5.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.55/5.00  --sup_immed_bw_main                     []
% 35.55/5.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.55/5.00  --sup_input_triv                        [Unflattening;TrivRules]
% 35.55/5.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.55/5.00  --sup_input_bw                          []
% 35.55/5.00  
% 35.55/5.00  ------ Combination Options
% 35.55/5.00  
% 35.55/5.00  --comb_res_mult                         3
% 35.55/5.00  --comb_sup_mult                         2
% 35.55/5.00  --comb_inst_mult                        10
% 35.55/5.00  
% 35.55/5.00  ------ Debug Options
% 35.55/5.00  
% 35.55/5.00  --dbg_backtrace                         false
% 35.55/5.00  --dbg_dump_prop_clauses                 false
% 35.55/5.00  --dbg_dump_prop_clauses_file            -
% 35.55/5.00  --dbg_out_stat                          false
% 35.55/5.00  ------ Parsing...
% 35.55/5.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 35.55/5.00  
% 35.55/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 35.55/5.00  
% 35.55/5.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 35.55/5.00  
% 35.55/5.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 35.55/5.00  ------ Proving...
% 35.55/5.00  ------ Problem Properties 
% 35.55/5.00  
% 35.55/5.00  
% 35.55/5.00  clauses                                 31
% 35.55/5.00  conjectures                             6
% 35.55/5.00  EPR                                     9
% 35.55/5.00  Horn                                    27
% 35.55/5.00  unary                                   8
% 35.55/5.00  binary                                  6
% 35.55/5.00  lits                                    92
% 35.55/5.00  lits eq                                 9
% 35.55/5.00  fd_pure                                 0
% 35.55/5.00  fd_pseudo                               0
% 35.55/5.00  fd_cond                                 0
% 35.55/5.00  fd_pseudo_cond                          1
% 35.55/5.00  AC symbols                              0
% 35.55/5.00  
% 35.55/5.00  ------ Schedule dynamic 5 is on 
% 35.55/5.00  
% 35.55/5.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 35.55/5.00  
% 35.55/5.00  
% 35.55/5.00  ------ 
% 35.55/5.00  Current options:
% 35.55/5.00  ------ 
% 35.55/5.00  
% 35.55/5.00  ------ Input Options
% 35.55/5.00  
% 35.55/5.00  --out_options                           all
% 35.55/5.00  --tptp_safe_out                         true
% 35.55/5.00  --problem_path                          ""
% 35.55/5.00  --include_path                          ""
% 35.55/5.00  --clausifier                            res/vclausify_rel
% 35.55/5.00  --clausifier_options                    ""
% 35.55/5.00  --stdin                                 false
% 35.55/5.00  --stats_out                             all
% 35.55/5.00  
% 35.55/5.00  ------ General Options
% 35.55/5.00  
% 35.55/5.00  --fof                                   false
% 35.55/5.00  --time_out_real                         305.
% 35.55/5.00  --time_out_virtual                      -1.
% 35.55/5.00  --symbol_type_check                     false
% 35.55/5.00  --clausify_out                          false
% 35.55/5.00  --sig_cnt_out                           false
% 35.55/5.00  --trig_cnt_out                          false
% 35.55/5.00  --trig_cnt_out_tolerance                1.
% 35.55/5.00  --trig_cnt_out_sk_spl                   false
% 35.55/5.00  --abstr_cl_out                          false
% 35.55/5.00  
% 35.55/5.00  ------ Global Options
% 35.55/5.00  
% 35.55/5.00  --schedule                              default
% 35.55/5.00  --add_important_lit                     false
% 35.55/5.00  --prop_solver_per_cl                    1000
% 35.55/5.00  --min_unsat_core                        false
% 35.55/5.00  --soft_assumptions                      false
% 35.55/5.00  --soft_lemma_size                       3
% 35.55/5.00  --prop_impl_unit_size                   0
% 35.55/5.00  --prop_impl_unit                        []
% 35.55/5.00  --share_sel_clauses                     true
% 35.55/5.00  --reset_solvers                         false
% 35.55/5.00  --bc_imp_inh                            [conj_cone]
% 35.55/5.00  --conj_cone_tolerance                   3.
% 35.55/5.00  --extra_neg_conj                        none
% 35.55/5.00  --large_theory_mode                     true
% 35.55/5.00  --prolific_symb_bound                   200
% 35.55/5.00  --lt_threshold                          2000
% 35.55/5.00  --clause_weak_htbl                      true
% 35.55/5.00  --gc_record_bc_elim                     false
% 35.55/5.00  
% 35.55/5.00  ------ Preprocessing Options
% 35.55/5.00  
% 35.55/5.00  --preprocessing_flag                    true
% 35.55/5.00  --time_out_prep_mult                    0.1
% 35.55/5.00  --splitting_mode                        input
% 35.55/5.00  --splitting_grd                         true
% 35.55/5.00  --splitting_cvd                         false
% 35.55/5.00  --splitting_cvd_svl                     false
% 35.55/5.00  --splitting_nvd                         32
% 35.55/5.00  --sub_typing                            true
% 35.55/5.00  --prep_gs_sim                           true
% 35.55/5.00  --prep_unflatten                        true
% 35.55/5.00  --prep_res_sim                          true
% 35.55/5.00  --prep_upred                            true
% 35.55/5.00  --prep_sem_filter                       exhaustive
% 35.55/5.00  --prep_sem_filter_out                   false
% 35.55/5.00  --pred_elim                             true
% 35.55/5.00  --res_sim_input                         true
% 35.55/5.00  --eq_ax_congr_red                       true
% 35.55/5.00  --pure_diseq_elim                       true
% 35.55/5.00  --brand_transform                       false
% 35.55/5.00  --non_eq_to_eq                          false
% 35.55/5.00  --prep_def_merge                        true
% 35.55/5.00  --prep_def_merge_prop_impl              false
% 35.55/5.00  --prep_def_merge_mbd                    true
% 35.55/5.00  --prep_def_merge_tr_red                 false
% 35.55/5.00  --prep_def_merge_tr_cl                  false
% 35.55/5.00  --smt_preprocessing                     true
% 35.55/5.00  --smt_ac_axioms                         fast
% 35.55/5.00  --preprocessed_out                      false
% 35.55/5.00  --preprocessed_stats                    false
% 35.55/5.00  
% 35.55/5.00  ------ Abstraction refinement Options
% 35.55/5.00  
% 35.55/5.00  --abstr_ref                             []
% 35.55/5.00  --abstr_ref_prep                        false
% 35.55/5.00  --abstr_ref_until_sat                   false
% 35.55/5.00  --abstr_ref_sig_restrict                funpre
% 35.55/5.00  --abstr_ref_af_restrict_to_split_sk     false
% 35.55/5.00  --abstr_ref_under                       []
% 35.55/5.00  
% 35.55/5.00  ------ SAT Options
% 35.55/5.00  
% 35.55/5.00  --sat_mode                              false
% 35.55/5.00  --sat_fm_restart_options                ""
% 35.55/5.00  --sat_gr_def                            false
% 35.55/5.00  --sat_epr_types                         true
% 35.55/5.00  --sat_non_cyclic_types                  false
% 35.55/5.00  --sat_finite_models                     false
% 35.55/5.00  --sat_fm_lemmas                         false
% 35.55/5.00  --sat_fm_prep                           false
% 35.55/5.00  --sat_fm_uc_incr                        true
% 35.55/5.00  --sat_out_model                         small
% 35.55/5.00  --sat_out_clauses                       false
% 35.55/5.00  
% 35.55/5.00  ------ QBF Options
% 35.55/5.00  
% 35.55/5.00  --qbf_mode                              false
% 35.55/5.00  --qbf_elim_univ                         false
% 35.55/5.00  --qbf_dom_inst                          none
% 35.55/5.00  --qbf_dom_pre_inst                      false
% 35.55/5.00  --qbf_sk_in                             false
% 35.55/5.00  --qbf_pred_elim                         true
% 35.55/5.00  --qbf_split                             512
% 35.55/5.00  
% 35.55/5.00  ------ BMC1 Options
% 35.55/5.00  
% 35.55/5.00  --bmc1_incremental                      false
% 35.55/5.00  --bmc1_axioms                           reachable_all
% 35.55/5.00  --bmc1_min_bound                        0
% 35.55/5.00  --bmc1_max_bound                        -1
% 35.55/5.00  --bmc1_max_bound_default                -1
% 35.55/5.00  --bmc1_symbol_reachability              true
% 35.55/5.00  --bmc1_property_lemmas                  false
% 35.55/5.00  --bmc1_k_induction                      false
% 35.55/5.00  --bmc1_non_equiv_states                 false
% 35.55/5.00  --bmc1_deadlock                         false
% 35.55/5.00  --bmc1_ucm                              false
% 35.55/5.00  --bmc1_add_unsat_core                   none
% 35.55/5.00  --bmc1_unsat_core_children              false
% 35.55/5.00  --bmc1_unsat_core_extrapolate_axioms    false
% 35.55/5.00  --bmc1_out_stat                         full
% 35.55/5.00  --bmc1_ground_init                      false
% 35.55/5.00  --bmc1_pre_inst_next_state              false
% 35.55/5.00  --bmc1_pre_inst_state                   false
% 35.55/5.00  --bmc1_pre_inst_reach_state             false
% 35.55/5.00  --bmc1_out_unsat_core                   false
% 35.55/5.00  --bmc1_aig_witness_out                  false
% 35.55/5.00  --bmc1_verbose                          false
% 35.55/5.00  --bmc1_dump_clauses_tptp                false
% 35.55/5.00  --bmc1_dump_unsat_core_tptp             false
% 35.55/5.00  --bmc1_dump_file                        -
% 35.55/5.00  --bmc1_ucm_expand_uc_limit              128
% 35.55/5.00  --bmc1_ucm_n_expand_iterations          6
% 35.55/5.00  --bmc1_ucm_extend_mode                  1
% 35.55/5.00  --bmc1_ucm_init_mode                    2
% 35.55/5.00  --bmc1_ucm_cone_mode                    none
% 35.55/5.00  --bmc1_ucm_reduced_relation_type        0
% 35.55/5.00  --bmc1_ucm_relax_model                  4
% 35.55/5.00  --bmc1_ucm_full_tr_after_sat            true
% 35.55/5.00  --bmc1_ucm_expand_neg_assumptions       false
% 35.55/5.00  --bmc1_ucm_layered_model                none
% 35.55/5.00  --bmc1_ucm_max_lemma_size               10
% 35.55/5.00  
% 35.55/5.00  ------ AIG Options
% 35.55/5.00  
% 35.55/5.00  --aig_mode                              false
% 35.55/5.00  
% 35.55/5.00  ------ Instantiation Options
% 35.55/5.00  
% 35.55/5.00  --instantiation_flag                    true
% 35.55/5.00  --inst_sos_flag                         true
% 35.55/5.00  --inst_sos_phase                        true
% 35.55/5.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 35.55/5.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 35.55/5.00  --inst_lit_sel_side                     none
% 35.55/5.00  --inst_solver_per_active                1400
% 35.55/5.00  --inst_solver_calls_frac                1.
% 35.55/5.00  --inst_passive_queue_type               priority_queues
% 35.55/5.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 35.55/5.00  --inst_passive_queues_freq              [25;2]
% 35.55/5.00  --inst_dismatching                      true
% 35.55/5.00  --inst_eager_unprocessed_to_passive     true
% 35.55/5.00  --inst_prop_sim_given                   true
% 35.55/5.00  --inst_prop_sim_new                     false
% 35.55/5.00  --inst_subs_new                         false
% 35.55/5.00  --inst_eq_res_simp                      false
% 35.55/5.00  --inst_subs_given                       false
% 35.55/5.00  --inst_orphan_elimination               true
% 35.55/5.00  --inst_learning_loop_flag               true
% 35.55/5.00  --inst_learning_start                   3000
% 35.55/5.00  --inst_learning_factor                  2
% 35.55/5.00  --inst_start_prop_sim_after_learn       3
% 35.55/5.00  --inst_sel_renew                        solver
% 35.55/5.00  --inst_lit_activity_flag                true
% 35.55/5.00  --inst_restr_to_given                   false
% 35.55/5.00  --inst_activity_threshold               500
% 35.55/5.00  --inst_out_proof                        true
% 35.55/5.00  
% 35.55/5.00  ------ Resolution Options
% 35.55/5.00  
% 35.55/5.00  --resolution_flag                       false
% 35.55/5.00  --res_lit_sel                           adaptive
% 35.55/5.00  --res_lit_sel_side                      none
% 35.55/5.00  --res_ordering                          kbo
% 35.55/5.00  --res_to_prop_solver                    active
% 35.55/5.00  --res_prop_simpl_new                    false
% 35.55/5.00  --res_prop_simpl_given                  true
% 35.55/5.00  --res_passive_queue_type                priority_queues
% 35.55/5.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 35.55/5.00  --res_passive_queues_freq               [15;5]
% 35.55/5.00  --res_forward_subs                      full
% 35.55/5.00  --res_backward_subs                     full
% 35.55/5.00  --res_forward_subs_resolution           true
% 35.55/5.00  --res_backward_subs_resolution          true
% 35.55/5.00  --res_orphan_elimination                true
% 35.55/5.00  --res_time_limit                        2.
% 35.55/5.00  --res_out_proof                         true
% 35.55/5.00  
% 35.55/5.00  ------ Superposition Options
% 35.55/5.00  
% 35.55/5.00  --superposition_flag                    true
% 35.55/5.00  --sup_passive_queue_type                priority_queues
% 35.55/5.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 35.55/5.00  --sup_passive_queues_freq               [8;1;4]
% 35.55/5.00  --demod_completeness_check              fast
% 35.55/5.00  --demod_use_ground                      true
% 35.55/5.00  --sup_to_prop_solver                    passive
% 35.55/5.00  --sup_prop_simpl_new                    true
% 35.55/5.00  --sup_prop_simpl_given                  true
% 35.55/5.00  --sup_fun_splitting                     true
% 35.55/5.00  --sup_smt_interval                      50000
% 35.55/5.00  
% 35.55/5.00  ------ Superposition Simplification Setup
% 35.55/5.00  
% 35.55/5.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 35.55/5.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 35.55/5.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 35.55/5.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 35.55/5.00  --sup_full_triv                         [TrivRules;PropSubs]
% 35.55/5.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 35.55/5.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 35.55/5.00  --sup_immed_triv                        [TrivRules]
% 35.55/5.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 35.55/5.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.55/5.00  --sup_immed_bw_main                     []
% 35.55/5.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 35.55/5.00  --sup_input_triv                        [Unflattening;TrivRules]
% 35.55/5.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 35.55/5.00  --sup_input_bw                          []
% 35.55/5.00  
% 35.55/5.00  ------ Combination Options
% 35.55/5.00  
% 35.55/5.00  --comb_res_mult                         3
% 35.55/5.00  --comb_sup_mult                         2
% 35.55/5.00  --comb_inst_mult                        10
% 35.55/5.00  
% 35.55/5.00  ------ Debug Options
% 35.55/5.00  
% 35.55/5.00  --dbg_backtrace                         false
% 35.55/5.00  --dbg_dump_prop_clauses                 false
% 35.55/5.00  --dbg_dump_prop_clauses_file            -
% 35.55/5.00  --dbg_out_stat                          false
% 35.55/5.00  
% 35.55/5.00  
% 35.55/5.00  
% 35.55/5.00  
% 35.55/5.00  ------ Proving...
% 35.55/5.00  
% 35.55/5.00  
% 35.55/5.00  % SZS status Theorem for theBenchmark.p
% 35.55/5.00  
% 35.55/5.00  % SZS output start CNFRefutation for theBenchmark.p
% 35.55/5.00  
% 35.55/5.00  fof(f5,axiom,(
% 35.55/5.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 35.55/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.55/5.00  
% 35.55/5.00  fof(f15,plain,(
% 35.55/5.00    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 35.55/5.00    inference(ennf_transformation,[],[f5])).
% 35.55/5.00  
% 35.55/5.00  fof(f52,plain,(
% 35.55/5.00    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 35.55/5.00    inference(cnf_transformation,[],[f15])).
% 35.55/5.00  
% 35.55/5.00  fof(f4,axiom,(
% 35.55/5.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 35.55/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.55/5.00  
% 35.55/5.00  fof(f51,plain,(
% 35.55/5.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 35.55/5.00    inference(cnf_transformation,[],[f4])).
% 35.55/5.00  
% 35.55/5.00  fof(f84,plain,(
% 35.55/5.00    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 35.55/5.00    inference(definition_unfolding,[],[f52,f51])).
% 35.55/5.00  
% 35.55/5.00  fof(f6,axiom,(
% 35.55/5.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 35.55/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.55/5.00  
% 35.55/5.00  fof(f28,plain,(
% 35.55/5.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 35.55/5.00    inference(nnf_transformation,[],[f6])).
% 35.55/5.00  
% 35.55/5.00  fof(f54,plain,(
% 35.55/5.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 35.55/5.00    inference(cnf_transformation,[],[f28])).
% 35.55/5.00  
% 35.55/5.00  fof(f2,axiom,(
% 35.55/5.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 35.55/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.55/5.00  
% 35.55/5.00  fof(f26,plain,(
% 35.55/5.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.55/5.00    inference(nnf_transformation,[],[f2])).
% 35.55/5.00  
% 35.55/5.00  fof(f27,plain,(
% 35.55/5.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 35.55/5.00    inference(flattening,[],[f26])).
% 35.55/5.00  
% 35.55/5.00  fof(f47,plain,(
% 35.55/5.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 35.55/5.00    inference(cnf_transformation,[],[f27])).
% 35.55/5.00  
% 35.55/5.00  fof(f88,plain,(
% 35.55/5.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 35.55/5.00    inference(equality_resolution,[],[f47])).
% 35.55/5.00  
% 35.55/5.00  fof(f12,conjecture,(
% 35.55/5.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 35.55/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.55/5.00  
% 35.55/5.00  fof(f13,negated_conjecture,(
% 35.55/5.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 35.55/5.00    inference(negated_conjecture,[],[f12])).
% 35.55/5.00  
% 35.55/5.00  fof(f21,plain,(
% 35.55/5.00    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~v3_pre_topc(X3,X2) & X1 = X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,X0)) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 35.55/5.00    inference(ennf_transformation,[],[f13])).
% 35.55/5.00  
% 35.55/5.00  fof(f22,plain,(
% 35.55/5.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 35.55/5.00    inference(flattening,[],[f21])).
% 35.55/5.00  
% 35.55/5.00  fof(f44,plain,(
% 35.55/5.00    ( ! [X2,X1] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) => (~v3_pre_topc(sK9,X2) & sK9 = X1 & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(X2))))) )),
% 35.55/5.00    introduced(choice_axiom,[])).
% 35.55/5.00  
% 35.55/5.00  fof(f43,plain,(
% 35.55/5.00    ( ! [X0,X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) => (? [X3] : (~v3_pre_topc(X3,sK8) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK8)))) & v3_pre_topc(X1,X0) & m1_pre_topc(sK8,X0))) )),
% 35.55/5.00    introduced(choice_axiom,[])).
% 35.55/5.00  
% 35.55/5.00  fof(f42,plain,(
% 35.55/5.00    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & sK7 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(sK7,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 35.55/5.00    introduced(choice_axiom,[])).
% 35.55/5.00  
% 35.55/5.00  fof(f41,plain,(
% 35.55/5.00    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,sK6) & m1_pre_topc(X2,sK6)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6))),
% 35.55/5.00    introduced(choice_axiom,[])).
% 35.55/5.00  
% 35.55/5.00  fof(f45,plain,(
% 35.55/5.00    (((~v3_pre_topc(sK9,sK8) & sK7 = sK9 & m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))) & v3_pre_topc(sK7,sK6) & m1_pre_topc(sK8,sK6)) & m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))) & l1_pre_topc(sK6)),
% 35.55/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f22,f44,f43,f42,f41])).
% 35.55/5.00  
% 35.55/5.00  fof(f77,plain,(
% 35.55/5.00    m1_pre_topc(sK8,sK6)),
% 35.55/5.00    inference(cnf_transformation,[],[f45])).
% 35.55/5.00  
% 35.55/5.00  fof(f10,axiom,(
% 35.55/5.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 35.55/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.55/5.00  
% 35.55/5.00  fof(f19,plain,(
% 35.55/5.00    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 35.55/5.00    inference(ennf_transformation,[],[f10])).
% 35.55/5.00  
% 35.55/5.00  fof(f70,plain,(
% 35.55/5.00    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 35.55/5.00    inference(cnf_transformation,[],[f19])).
% 35.55/5.00  
% 35.55/5.00  fof(f75,plain,(
% 35.55/5.00    l1_pre_topc(sK6)),
% 35.55/5.00    inference(cnf_transformation,[],[f45])).
% 35.55/5.00  
% 35.55/5.00  fof(f9,axiom,(
% 35.55/5.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 35.55/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.55/5.00  
% 35.55/5.00  fof(f18,plain,(
% 35.55/5.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 35.55/5.00    inference(ennf_transformation,[],[f9])).
% 35.55/5.00  
% 35.55/5.00  fof(f69,plain,(
% 35.55/5.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 35.55/5.00    inference(cnf_transformation,[],[f18])).
% 35.55/5.00  
% 35.55/5.00  fof(f7,axiom,(
% 35.55/5.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 35.55/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.55/5.00  
% 35.55/5.00  fof(f16,plain,(
% 35.55/5.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 35.55/5.00    inference(ennf_transformation,[],[f7])).
% 35.55/5.00  
% 35.55/5.00  fof(f55,plain,(
% 35.55/5.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 35.55/5.00    inference(cnf_transformation,[],[f16])).
% 35.55/5.00  
% 35.55/5.00  fof(f79,plain,(
% 35.55/5.00    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))),
% 35.55/5.00    inference(cnf_transformation,[],[f45])).
% 35.55/5.00  
% 35.55/5.00  fof(f53,plain,(
% 35.55/5.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 35.55/5.00    inference(cnf_transformation,[],[f28])).
% 35.55/5.00  
% 35.55/5.00  fof(f3,axiom,(
% 35.55/5.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 35.55/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.55/5.00  
% 35.55/5.00  fof(f14,plain,(
% 35.55/5.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 35.55/5.00    inference(ennf_transformation,[],[f3])).
% 35.55/5.00  
% 35.55/5.00  fof(f50,plain,(
% 35.55/5.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 35.55/5.00    inference(cnf_transformation,[],[f14])).
% 35.55/5.00  
% 35.55/5.00  fof(f83,plain,(
% 35.55/5.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 35.55/5.00    inference(definition_unfolding,[],[f50,f51])).
% 35.55/5.00  
% 35.55/5.00  fof(f11,axiom,(
% 35.55/5.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 35.55/5.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 35.55/5.00  
% 35.55/5.00  fof(f20,plain,(
% 35.55/5.00    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 35.55/5.00    inference(ennf_transformation,[],[f11])).
% 35.55/5.00  
% 35.55/5.00  fof(f37,plain,(
% 35.55/5.00    ! [X0] : (! [X1] : (! [X2] : (((v3_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 35.55/5.00    inference(nnf_transformation,[],[f20])).
% 35.55/5.00  
% 35.55/5.00  fof(f38,plain,(
% 35.55/5.00    ! [X0] : (! [X1] : (! [X2] : (((v3_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 35.55/5.00    inference(rectify,[],[f37])).
% 35.55/5.00  
% 35.55/5.00  fof(f39,plain,(
% 35.55/5.00    ! [X2,X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2),k2_struct_0(X1)) = X2 & v3_pre_topc(sK5(X0,X1,X2),X0) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 35.55/5.00    introduced(choice_axiom,[])).
% 35.55/5.00  
% 35.55/5.00  fof(f40,plain,(
% 35.55/5.00    ! [X0] : (! [X1] : (! [X2] : (((v3_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((k9_subset_1(u1_struct_0(X1),sK5(X0,X1,X2),k2_struct_0(X1)) = X2 & v3_pre_topc(sK5(X0,X1,X2),X0) & m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~v3_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 35.55/5.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f38,f39])).
% 35.55/5.00  
% 35.55/5.00  fof(f74,plain,(
% 35.55/5.00    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X1) | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 35.55/5.00    inference(cnf_transformation,[],[f40])).
% 35.55/5.00  
% 35.55/5.00  fof(f90,plain,(
% 35.55/5.00    ( ! [X0,X3,X1] : (v3_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 35.55/5.00    inference(equality_resolution,[],[f74])).
% 35.55/5.00  
% 35.55/5.00  fof(f81,plain,(
% 35.55/5.00    ~v3_pre_topc(sK9,sK8)),
% 35.55/5.00    inference(cnf_transformation,[],[f45])).
% 35.55/5.00  
% 35.55/5.00  fof(f78,plain,(
% 35.55/5.00    v3_pre_topc(sK7,sK6)),
% 35.55/5.00    inference(cnf_transformation,[],[f45])).
% 35.55/5.00  
% 35.55/5.00  fof(f80,plain,(
% 35.55/5.00    sK7 = sK9),
% 35.55/5.00    inference(cnf_transformation,[],[f45])).
% 35.55/5.00  
% 35.55/5.00  fof(f85,plain,(
% 35.55/5.00    v3_pre_topc(sK9,sK6)),
% 35.55/5.00    inference(definition_unfolding,[],[f78,f80])).
% 35.55/5.00  
% 35.55/5.00  fof(f76,plain,(
% 35.55/5.00    m1_subset_1(sK7,k1_zfmisc_1(u1_struct_0(sK6)))),
% 35.55/5.00    inference(cnf_transformation,[],[f45])).
% 35.55/5.00  
% 35.55/5.00  fof(f86,plain,(
% 35.55/5.00    m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6)))),
% 35.55/5.00    inference(definition_unfolding,[],[f76,f80])).
% 35.55/5.00  
% 35.55/5.00  cnf(c_3000,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_79130,plain,
% 35.55/5.00      ( X0 != X1 | sK9 != X1 | sK9 = X0 ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_3000]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_79935,plain,
% 35.55/5.00      ( X0 != sK9 | sK9 = X0 | sK9 != sK9 ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_79130]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_80215,plain,
% 35.55/5.00      ( k4_xboole_0(sK9,k4_xboole_0(sK9,X0)) != sK9
% 35.55/5.00      | sK9 = k4_xboole_0(sK9,k4_xboole_0(sK9,X0))
% 35.55/5.00      | sK9 != sK9 ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_79935]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_126254,plain,
% 35.55/5.00      ( k4_xboole_0(sK9,k4_xboole_0(sK9,k2_struct_0(sK8))) != sK9
% 35.55/5.00      | sK9 = k4_xboole_0(sK9,k4_xboole_0(sK9,k2_struct_0(sK8)))
% 35.55/5.00      | sK9 != sK9 ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_80215]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_3005,plain,
% 35.55/5.00      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 35.55/5.00      theory(equality) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_78048,plain,
% 35.55/5.00      ( ~ m1_subset_1(X0,X1)
% 35.55/5.00      | m1_subset_1(k9_subset_1(u1_struct_0(sK8),X2,k2_struct_0(sK8)),k1_zfmisc_1(u1_struct_0(sK8)))
% 35.55/5.00      | k9_subset_1(u1_struct_0(sK8),X2,k2_struct_0(sK8)) != X0
% 35.55/5.00      | k1_zfmisc_1(u1_struct_0(sK8)) != X1 ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_3005]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_78213,plain,
% 35.55/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 35.55/5.00      | m1_subset_1(k9_subset_1(u1_struct_0(sK8),X1,k2_struct_0(sK8)),k1_zfmisc_1(u1_struct_0(sK8)))
% 35.55/5.00      | k9_subset_1(u1_struct_0(sK8),X1,k2_struct_0(sK8)) != X0
% 35.55/5.00      | k1_zfmisc_1(u1_struct_0(sK8)) != k1_zfmisc_1(u1_struct_0(sK8)) ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_78048]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_97438,plain,
% 35.55/5.00      ( m1_subset_1(k9_subset_1(u1_struct_0(sK8),X0,k2_struct_0(sK8)),k1_zfmisc_1(u1_struct_0(sK8)))
% 35.55/5.00      | ~ m1_subset_1(k4_xboole_0(X0,k4_xboole_0(X0,k2_struct_0(sK8))),k1_zfmisc_1(u1_struct_0(sK8)))
% 35.55/5.00      | k9_subset_1(u1_struct_0(sK8),X0,k2_struct_0(sK8)) != k4_xboole_0(X0,k4_xboole_0(X0,k2_struct_0(sK8)))
% 35.55/5.00      | k1_zfmisc_1(u1_struct_0(sK8)) != k1_zfmisc_1(u1_struct_0(sK8)) ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_78213]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_125470,plain,
% 35.55/5.00      ( m1_subset_1(k9_subset_1(u1_struct_0(sK8),sK9,k2_struct_0(sK8)),k1_zfmisc_1(u1_struct_0(sK8)))
% 35.55/5.00      | ~ m1_subset_1(k4_xboole_0(sK9,k4_xboole_0(sK9,k2_struct_0(sK8))),k1_zfmisc_1(u1_struct_0(sK8)))
% 35.55/5.00      | k9_subset_1(u1_struct_0(sK8),sK9,k2_struct_0(sK8)) != k4_xboole_0(sK9,k4_xboole_0(sK9,k2_struct_0(sK8)))
% 35.55/5.00      | k1_zfmisc_1(u1_struct_0(sK8)) != k1_zfmisc_1(u1_struct_0(sK8)) ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_97438]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_85852,plain,
% 35.55/5.00      ( ~ m1_subset_1(X0,X1)
% 35.55/5.00      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK8)))
% 35.55/5.00      | X2 != X0
% 35.55/5.00      | k1_zfmisc_1(u1_struct_0(sK8)) != X1 ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_3005]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_96898,plain,
% 35.55/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 35.55/5.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK8)))
% 35.55/5.00      | X1 != X0
% 35.55/5.00      | k1_zfmisc_1(u1_struct_0(sK8)) != k1_zfmisc_1(u1_struct_0(sK8)) ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_85852]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_117474,plain,
% 35.55/5.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK8)))
% 35.55/5.00      | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
% 35.55/5.00      | X0 != sK9
% 35.55/5.00      | k1_zfmisc_1(u1_struct_0(sK8)) != k1_zfmisc_1(u1_struct_0(sK8)) ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_96898]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_124239,plain,
% 35.55/5.00      ( m1_subset_1(k4_xboole_0(sK9,k4_xboole_0(sK9,X0)),k1_zfmisc_1(u1_struct_0(sK8)))
% 35.55/5.00      | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
% 35.55/5.00      | k4_xboole_0(sK9,k4_xboole_0(sK9,X0)) != sK9
% 35.55/5.00      | k1_zfmisc_1(u1_struct_0(sK8)) != k1_zfmisc_1(u1_struct_0(sK8)) ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_117474]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_125469,plain,
% 35.55/5.00      ( m1_subset_1(k4_xboole_0(sK9,k4_xboole_0(sK9,k2_struct_0(sK8))),k1_zfmisc_1(u1_struct_0(sK8)))
% 35.55/5.00      | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8)))
% 35.55/5.00      | k4_xboole_0(sK9,k4_xboole_0(sK9,k2_struct_0(sK8))) != sK9
% 35.55/5.00      | k1_zfmisc_1(u1_struct_0(sK8)) != k1_zfmisc_1(u1_struct_0(sK8)) ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_124239]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_5,plain,
% 35.55/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 35.55/5.00      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 35.55/5.00      inference(cnf_transformation,[],[f84]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_6,plain,
% 35.55/5.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 35.55/5.00      inference(cnf_transformation,[],[f54]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_258,plain,
% 35.55/5.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 35.55/5.00      inference(prop_impl,[status(thm)],[c_6]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_259,plain,
% 35.55/5.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 35.55/5.00      inference(renaming,[status(thm)],[c_258]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_319,plain,
% 35.55/5.00      ( ~ r1_tarski(X0,X1)
% 35.55/5.00      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 35.55/5.00      inference(bin_hyper_res,[status(thm)],[c_5,c_259]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_86540,plain,
% 35.55/5.00      ( ~ r1_tarski(k2_struct_0(sK8),u1_struct_0(sK8))
% 35.55/5.00      | k4_xboole_0(X0,k4_xboole_0(X0,k2_struct_0(sK8))) = k9_subset_1(u1_struct_0(sK8),X0,k2_struct_0(sK8)) ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_319]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_105948,plain,
% 35.55/5.00      ( ~ r1_tarski(k2_struct_0(sK8),u1_struct_0(sK8))
% 35.55/5.00      | k4_xboole_0(sK9,k4_xboole_0(sK9,k2_struct_0(sK8))) = k9_subset_1(u1_struct_0(sK8),sK9,k2_struct_0(sK8)) ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_86540]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_2999,plain,( X0 = X0 ),theory(equality) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_101743,plain,
% 35.55/5.00      ( k9_subset_1(u1_struct_0(sK8),sK9,k2_struct_0(sK8)) = k9_subset_1(u1_struct_0(sK8),sK9,k2_struct_0(sK8)) ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_2999]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_82258,plain,
% 35.55/5.00      ( X0 != k4_xboole_0(sK9,k4_xboole_0(sK9,X1))
% 35.55/5.00      | sK9 = X0
% 35.55/5.00      | sK9 != k4_xboole_0(sK9,k4_xboole_0(sK9,X1)) ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_79130]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_97453,plain,
% 35.55/5.00      ( k9_subset_1(u1_struct_0(sK8),sK9,k2_struct_0(sK8)) != k4_xboole_0(sK9,k4_xboole_0(sK9,k2_struct_0(sK8)))
% 35.55/5.00      | sK9 = k9_subset_1(u1_struct_0(sK8),sK9,k2_struct_0(sK8))
% 35.55/5.00      | sK9 != k4_xboole_0(sK9,k4_xboole_0(sK9,k2_struct_0(sK8))) ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_82258]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_78496,plain,
% 35.55/5.00      ( X0 != X1
% 35.55/5.00      | k9_subset_1(u1_struct_0(sK8),X2,k2_struct_0(sK8)) != X1
% 35.55/5.00      | k9_subset_1(u1_struct_0(sK8),X2,k2_struct_0(sK8)) = X0 ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_3000]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_79445,plain,
% 35.55/5.00      ( X0 != k9_subset_1(u1_struct_0(sK8),X1,k2_struct_0(sK8))
% 35.55/5.00      | k9_subset_1(u1_struct_0(sK8),X1,k2_struct_0(sK8)) = X0
% 35.55/5.00      | k9_subset_1(u1_struct_0(sK8),X1,k2_struct_0(sK8)) != k9_subset_1(u1_struct_0(sK8),X1,k2_struct_0(sK8)) ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_78496]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_81287,plain,
% 35.55/5.00      ( k9_subset_1(u1_struct_0(sK8),X0,k2_struct_0(sK8)) != k9_subset_1(u1_struct_0(sK8),X0,k2_struct_0(sK8))
% 35.55/5.00      | k9_subset_1(u1_struct_0(sK8),X0,k2_struct_0(sK8)) = k4_xboole_0(X0,k4_xboole_0(X0,k2_struct_0(sK8)))
% 35.55/5.00      | k4_xboole_0(X0,k4_xboole_0(X0,k2_struct_0(sK8))) != k9_subset_1(u1_struct_0(sK8),X0,k2_struct_0(sK8)) ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_79445]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_97451,plain,
% 35.55/5.00      ( k9_subset_1(u1_struct_0(sK8),sK9,k2_struct_0(sK8)) != k9_subset_1(u1_struct_0(sK8),sK9,k2_struct_0(sK8))
% 35.55/5.00      | k9_subset_1(u1_struct_0(sK8),sK9,k2_struct_0(sK8)) = k4_xboole_0(sK9,k4_xboole_0(sK9,k2_struct_0(sK8)))
% 35.55/5.00      | k4_xboole_0(sK9,k4_xboole_0(sK9,k2_struct_0(sK8))) != k9_subset_1(u1_struct_0(sK8),sK9,k2_struct_0(sK8)) ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_81287]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_3002,plain,
% 35.55/5.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 35.55/5.00      theory(equality) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_5708,plain,
% 35.55/5.00      ( ~ r1_tarski(X0,X1)
% 35.55/5.00      | r1_tarski(X2,u1_struct_0(sK8))
% 35.55/5.00      | X2 != X0
% 35.55/5.00      | u1_struct_0(sK8) != X1 ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_3002]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_8530,plain,
% 35.55/5.00      ( r1_tarski(X0,u1_struct_0(sK8))
% 35.55/5.00      | ~ r1_tarski(X1,k2_struct_0(sK8))
% 35.55/5.00      | X0 != X1
% 35.55/5.00      | u1_struct_0(sK8) != k2_struct_0(sK8) ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_5708]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_15625,plain,
% 35.55/5.00      ( r1_tarski(X0,u1_struct_0(sK8))
% 35.55/5.00      | ~ r1_tarski(k2_struct_0(sK8),k2_struct_0(sK8))
% 35.55/5.00      | X0 != k2_struct_0(sK8)
% 35.55/5.00      | u1_struct_0(sK8) != k2_struct_0(sK8) ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_8530]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_26739,plain,
% 35.55/5.00      ( r1_tarski(k2_struct_0(sK8),u1_struct_0(sK8))
% 35.55/5.00      | ~ r1_tarski(k2_struct_0(sK8),k2_struct_0(sK8))
% 35.55/5.00      | u1_struct_0(sK8) != k2_struct_0(sK8)
% 35.55/5.00      | k2_struct_0(sK8) != k2_struct_0(sK8) ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_15625]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_13810,plain,
% 35.55/5.00      ( k2_struct_0(sK8) = k2_struct_0(sK8) ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_2999]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_3,plain,
% 35.55/5.00      ( r1_tarski(X0,X0) ),
% 35.55/5.00      inference(cnf_transformation,[],[f88]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_5416,plain,
% 35.55/5.00      ( r1_tarski(k2_struct_0(X0),k2_struct_0(X0)) ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_3]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_10714,plain,
% 35.55/5.00      ( r1_tarski(k2_struct_0(sK8),k2_struct_0(sK8)) ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_5416]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_4983,plain,
% 35.55/5.00      ( k1_zfmisc_1(u1_struct_0(sK8)) = k1_zfmisc_1(u1_struct_0(sK8)) ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_2999]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_31,negated_conjecture,
% 35.55/5.00      ( m1_pre_topc(sK8,sK6) ),
% 35.55/5.00      inference(cnf_transformation,[],[f77]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_3668,plain,
% 35.55/5.00      ( m1_pre_topc(sK8,sK6) = iProver_top ),
% 35.55/5.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_23,plain,
% 35.55/5.00      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 35.55/5.00      inference(cnf_transformation,[],[f70]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_3676,plain,
% 35.55/5.00      ( m1_pre_topc(X0,X1) != iProver_top
% 35.55/5.00      | l1_pre_topc(X1) != iProver_top
% 35.55/5.00      | l1_pre_topc(X0) = iProver_top ),
% 35.55/5.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_4617,plain,
% 35.55/5.00      ( l1_pre_topc(sK6) != iProver_top
% 35.55/5.00      | l1_pre_topc(sK8) = iProver_top ),
% 35.55/5.00      inference(superposition,[status(thm)],[c_3668,c_3676]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_33,negated_conjecture,
% 35.55/5.00      ( l1_pre_topc(sK6) ),
% 35.55/5.00      inference(cnf_transformation,[],[f75]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_34,plain,
% 35.55/5.00      ( l1_pre_topc(sK6) = iProver_top ),
% 35.55/5.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_603,plain,
% 35.55/5.00      ( ~ l1_pre_topc(X0) | l1_pre_topc(X1) | sK6 != X0 | sK8 != X1 ),
% 35.55/5.00      inference(resolution_lifted,[status(thm)],[c_23,c_31]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_604,plain,
% 35.55/5.00      ( ~ l1_pre_topc(sK6) | l1_pre_topc(sK8) ),
% 35.55/5.00      inference(unflattening,[status(thm)],[c_603]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_605,plain,
% 35.55/5.00      ( l1_pre_topc(sK6) != iProver_top
% 35.55/5.00      | l1_pre_topc(sK8) = iProver_top ),
% 35.55/5.00      inference(predicate_to_equality,[status(thm)],[c_604]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_4818,plain,
% 35.55/5.00      ( l1_pre_topc(sK8) = iProver_top ),
% 35.55/5.00      inference(global_propositional_subsumption,
% 35.55/5.00                [status(thm)],
% 35.55/5.00                [c_4617,c_34,c_605]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_22,plain,
% 35.55/5.00      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 35.55/5.00      inference(cnf_transformation,[],[f69]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_8,plain,
% 35.55/5.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 35.55/5.00      inference(cnf_transformation,[],[f55]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_433,plain,
% 35.55/5.00      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 35.55/5.00      inference(resolution,[status(thm)],[c_22,c_8]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_3664,plain,
% 35.55/5.00      ( u1_struct_0(X0) = k2_struct_0(X0)
% 35.55/5.00      | l1_pre_topc(X0) != iProver_top ),
% 35.55/5.00      inference(predicate_to_equality,[status(thm)],[c_433]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_4822,plain,
% 35.55/5.00      ( u1_struct_0(sK8) = k2_struct_0(sK8) ),
% 35.55/5.00      inference(superposition,[status(thm)],[c_4818,c_3664]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_29,negated_conjecture,
% 35.55/5.00      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) ),
% 35.55/5.00      inference(cnf_transformation,[],[f79]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_3670,plain,
% 35.55/5.00      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK8))) = iProver_top ),
% 35.55/5.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_7,plain,
% 35.55/5.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 35.55/5.00      inference(cnf_transformation,[],[f53]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_3687,plain,
% 35.55/5.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 35.55/5.00      | r1_tarski(X0,X1) = iProver_top ),
% 35.55/5.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_4048,plain,
% 35.55/5.00      ( r1_tarski(sK9,u1_struct_0(sK8)) = iProver_top ),
% 35.55/5.00      inference(superposition,[status(thm)],[c_3670,c_3687]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_4,plain,
% 35.55/5.00      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 35.55/5.00      inference(cnf_transformation,[],[f83]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_3689,plain,
% 35.55/5.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 35.55/5.00      | r1_tarski(X0,X1) != iProver_top ),
% 35.55/5.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_4188,plain,
% 35.55/5.00      ( k4_xboole_0(sK9,k4_xboole_0(sK9,u1_struct_0(sK8))) = sK9 ),
% 35.55/5.00      inference(superposition,[status(thm)],[c_4048,c_3689]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_4882,plain,
% 35.55/5.00      ( k4_xboole_0(sK9,k4_xboole_0(sK9,k2_struct_0(sK8))) = sK9 ),
% 35.55/5.00      inference(demodulation,[status(thm)],[c_4822,c_4188]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_3010,plain,
% 35.55/5.00      ( ~ v3_pre_topc(X0,X1) | v3_pre_topc(X2,X3) | X2 != X0 | X3 != X1 ),
% 35.55/5.00      theory(equality) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_3728,plain,
% 35.55/5.00      ( ~ v3_pre_topc(X0,X1)
% 35.55/5.00      | v3_pre_topc(sK9,sK8)
% 35.55/5.00      | sK8 != X1
% 35.55/5.00      | sK9 != X0 ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_3010]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_3736,plain,
% 35.55/5.00      ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(X0),X1,k2_struct_0(X0)),X0)
% 35.55/5.00      | v3_pre_topc(sK9,sK8)
% 35.55/5.00      | sK8 != X0
% 35.55/5.00      | sK9 != k9_subset_1(u1_struct_0(X0),X1,k2_struct_0(X0)) ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_3728]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_3757,plain,
% 35.55/5.00      ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(sK8),X0,k2_struct_0(sK8)),sK8)
% 35.55/5.00      | v3_pre_topc(sK9,sK8)
% 35.55/5.00      | sK8 != sK8
% 35.55/5.00      | sK9 != k9_subset_1(u1_struct_0(sK8),X0,k2_struct_0(sK8)) ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_3736]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_4305,plain,
% 35.55/5.00      ( ~ v3_pre_topc(k9_subset_1(u1_struct_0(sK8),sK9,k2_struct_0(sK8)),sK8)
% 35.55/5.00      | v3_pre_topc(sK9,sK8)
% 35.55/5.00      | sK8 != sK8
% 35.55/5.00      | sK9 != k9_subset_1(u1_struct_0(sK8),sK9,k2_struct_0(sK8)) ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_3757]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_24,plain,
% 35.55/5.00      ( ~ v3_pre_topc(X0,X1)
% 35.55/5.00      | v3_pre_topc(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),X2)
% 35.55/5.00      | ~ m1_pre_topc(X2,X1)
% 35.55/5.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 35.55/5.00      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X2),X0,k2_struct_0(X2)),k1_zfmisc_1(u1_struct_0(X2)))
% 35.55/5.00      | ~ l1_pre_topc(X1) ),
% 35.55/5.00      inference(cnf_transformation,[],[f90]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_4086,plain,
% 35.55/5.00      ( v3_pre_topc(k9_subset_1(u1_struct_0(X0),sK9,k2_struct_0(X0)),X0)
% 35.55/5.00      | ~ v3_pre_topc(sK9,sK6)
% 35.55/5.00      | ~ m1_pre_topc(X0,sK6)
% 35.55/5.00      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),sK9,k2_struct_0(X0)),k1_zfmisc_1(u1_struct_0(X0)))
% 35.55/5.00      | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6)))
% 35.55/5.00      | ~ l1_pre_topc(sK6) ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_24]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_4304,plain,
% 35.55/5.00      ( v3_pre_topc(k9_subset_1(u1_struct_0(sK8),sK9,k2_struct_0(sK8)),sK8)
% 35.55/5.00      | ~ v3_pre_topc(sK9,sK6)
% 35.55/5.00      | ~ m1_pre_topc(sK8,sK6)
% 35.55/5.00      | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK8),sK9,k2_struct_0(sK8)),k1_zfmisc_1(u1_struct_0(sK8)))
% 35.55/5.00      | ~ m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6)))
% 35.55/5.00      | ~ l1_pre_topc(sK6) ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_4086]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_3973,plain,
% 35.55/5.00      ( sK9 = sK9 ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_2999]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_3785,plain,
% 35.55/5.00      ( sK8 = sK8 ),
% 35.55/5.00      inference(instantiation,[status(thm)],[c_2999]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_28,negated_conjecture,
% 35.55/5.00      ( ~ v3_pre_topc(sK9,sK8) ),
% 35.55/5.00      inference(cnf_transformation,[],[f81]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_30,negated_conjecture,
% 35.55/5.00      ( v3_pre_topc(sK9,sK6) ),
% 35.55/5.00      inference(cnf_transformation,[],[f85]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(c_32,negated_conjecture,
% 35.55/5.00      ( m1_subset_1(sK9,k1_zfmisc_1(u1_struct_0(sK6))) ),
% 35.55/5.00      inference(cnf_transformation,[],[f86]) ).
% 35.55/5.00  
% 35.55/5.00  cnf(contradiction,plain,
% 35.55/5.00      ( $false ),
% 35.55/5.00      inference(minisat,
% 35.55/5.00                [status(thm)],
% 35.55/5.00                [c_126254,c_125470,c_125469,c_105948,c_101743,c_97453,
% 35.55/5.00                 c_97451,c_26739,c_13810,c_10714,c_4983,c_4882,c_4822,
% 35.55/5.00                 c_4305,c_4304,c_3973,c_3785,c_28,c_29,c_30,c_31,c_32,
% 35.55/5.00                 c_33]) ).
% 35.55/5.00  
% 35.55/5.00  
% 35.55/5.00  % SZS output end CNFRefutation for theBenchmark.p
% 35.55/5.00  
% 35.55/5.00  ------                               Statistics
% 35.55/5.00  
% 35.55/5.00  ------ General
% 35.55/5.00  
% 35.55/5.00  abstr_ref_over_cycles:                  0
% 35.55/5.00  abstr_ref_under_cycles:                 0
% 35.55/5.00  gc_basic_clause_elim:                   0
% 35.55/5.00  forced_gc_time:                         0
% 35.55/5.00  parsing_time:                           0.013
% 35.55/5.00  unif_index_cands_time:                  0.
% 35.55/5.00  unif_index_add_time:                    0.
% 35.55/5.00  orderings_time:                         0.
% 35.55/5.00  out_proof_time:                         0.018
% 35.55/5.00  total_time:                             4.283
% 35.55/5.00  num_of_symbols:                         53
% 35.55/5.00  num_of_terms:                           61492
% 35.55/5.00  
% 35.55/5.00  ------ Preprocessing
% 35.55/5.00  
% 35.55/5.00  num_of_splits:                          0
% 35.55/5.00  num_of_split_atoms:                     0
% 35.55/5.00  num_of_reused_defs:                     0
% 35.55/5.00  num_eq_ax_congr_red:                    48
% 35.55/5.00  num_of_sem_filtered_clauses:            1
% 35.55/5.00  num_of_subtypes:                        0
% 35.55/5.00  monotx_restored_types:                  0
% 35.55/5.00  sat_num_of_epr_types:                   0
% 35.55/5.00  sat_num_of_non_cyclic_types:            0
% 35.55/5.00  sat_guarded_non_collapsed_types:        0
% 35.55/5.00  num_pure_diseq_elim:                    0
% 35.55/5.00  simp_replaced_by:                       0
% 35.55/5.00  res_preprocessed:                       151
% 35.55/5.00  prep_upred:                             0
% 35.55/5.00  prep_unflattend:                        140
% 35.55/5.00  smt_new_axioms:                         0
% 35.55/5.00  pred_elim_cands:                        7
% 35.55/5.00  pred_elim:                              2
% 35.55/5.00  pred_elim_cl:                           2
% 35.55/5.00  pred_elim_cycles:                       6
% 35.55/5.00  merged_defs:                            8
% 35.55/5.00  merged_defs_ncl:                        0
% 35.55/5.00  bin_hyper_res:                          9
% 35.55/5.00  prep_cycles:                            4
% 35.55/5.00  pred_elim_time:                         0.046
% 35.55/5.00  splitting_time:                         0.
% 35.55/5.00  sem_filter_time:                        0.
% 35.55/5.00  monotx_time:                            0.001
% 35.55/5.00  subtype_inf_time:                       0.
% 35.55/5.00  
% 35.55/5.00  ------ Problem properties
% 35.55/5.00  
% 35.55/5.00  clauses:                                31
% 35.55/5.00  conjectures:                            6
% 35.55/5.00  epr:                                    9
% 35.55/5.00  horn:                                   27
% 35.55/5.00  ground:                                 6
% 35.55/5.00  unary:                                  8
% 35.55/5.00  binary:                                 6
% 35.55/5.00  lits:                                   92
% 35.55/5.00  lits_eq:                                9
% 35.55/5.00  fd_pure:                                0
% 35.55/5.00  fd_pseudo:                              0
% 35.55/5.00  fd_cond:                                0
% 35.55/5.00  fd_pseudo_cond:                         1
% 35.55/5.00  ac_symbols:                             0
% 35.55/5.00  
% 35.55/5.00  ------ Propositional Solver
% 35.55/5.00  
% 35.55/5.00  prop_solver_calls:                      52
% 35.55/5.00  prop_fast_solver_calls:                 8939
% 35.55/5.00  smt_solver_calls:                       0
% 35.55/5.00  smt_fast_solver_calls:                  0
% 35.55/5.00  prop_num_of_clauses:                    50843
% 35.55/5.00  prop_preprocess_simplified:             75542
% 35.55/5.00  prop_fo_subsumed:                       287
% 35.55/5.00  prop_solver_time:                       0.
% 35.55/5.00  smt_solver_time:                        0.
% 35.55/5.00  smt_fast_solver_time:                   0.
% 35.55/5.00  prop_fast_solver_time:                  0.
% 35.55/5.00  prop_unsat_core_time:                   0.008
% 35.55/5.00  
% 35.55/5.00  ------ QBF
% 35.55/5.00  
% 35.55/5.00  qbf_q_res:                              0
% 35.55/5.00  qbf_num_tautologies:                    0
% 35.55/5.00  qbf_prep_cycles:                        0
% 35.55/5.00  
% 35.55/5.00  ------ BMC1
% 35.55/5.00  
% 35.55/5.00  bmc1_current_bound:                     -1
% 35.55/5.00  bmc1_last_solved_bound:                 -1
% 35.55/5.00  bmc1_unsat_core_size:                   -1
% 35.55/5.00  bmc1_unsat_core_parents_size:           -1
% 35.55/5.00  bmc1_merge_next_fun:                    0
% 35.55/5.00  bmc1_unsat_core_clauses_time:           0.
% 35.55/5.00  
% 35.55/5.00  ------ Instantiation
% 35.55/5.00  
% 35.55/5.00  inst_num_of_clauses:                    5448
% 35.55/5.00  inst_num_in_passive:                    2422
% 35.55/5.00  inst_num_in_active:                     5231
% 35.55/5.00  inst_num_in_unprocessed:                327
% 35.55/5.00  inst_num_of_loops:                      5737
% 35.55/5.00  inst_num_of_learning_restarts:          1
% 35.55/5.00  inst_num_moves_active_passive:          487
% 35.55/5.00  inst_lit_activity:                      0
% 35.55/5.00  inst_lit_activity_moves:                1
% 35.55/5.00  inst_num_tautologies:                   0
% 35.55/5.00  inst_num_prop_implied:                  0
% 35.55/5.00  inst_num_existing_simplified:           0
% 35.55/5.00  inst_num_eq_res_simplified:             0
% 35.55/5.00  inst_num_child_elim:                    0
% 35.55/5.00  inst_num_of_dismatching_blockings:      10598
% 35.55/5.00  inst_num_of_non_proper_insts:           17561
% 35.55/5.00  inst_num_of_duplicates:                 0
% 35.55/5.00  inst_inst_num_from_inst_to_res:         0
% 35.55/5.00  inst_dismatching_checking_time:         0.
% 35.55/5.00  
% 35.55/5.00  ------ Resolution
% 35.55/5.00  
% 35.55/5.00  res_num_of_clauses:                     43
% 35.55/5.00  res_num_in_passive:                     43
% 35.55/5.00  res_num_in_active:                      0
% 35.55/5.00  res_num_of_loops:                       155
% 35.55/5.00  res_forward_subset_subsumed:            1481
% 35.55/5.00  res_backward_subset_subsumed:           0
% 35.55/5.00  res_forward_subsumed:                   0
% 35.55/5.00  res_backward_subsumed:                  0
% 35.55/5.00  res_forward_subsumption_resolution:     0
% 35.55/5.00  res_backward_subsumption_resolution:    0
% 35.55/5.00  res_clause_to_clause_subsumption:       22237
% 35.55/5.00  res_orphan_elimination:                 0
% 35.55/5.00  res_tautology_del:                      1333
% 35.55/5.00  res_num_eq_res_simplified:              0
% 35.55/5.00  res_num_sel_changes:                    0
% 35.55/5.00  res_moves_from_active_to_pass:          0
% 35.55/5.00  
% 35.55/5.00  ------ Superposition
% 35.55/5.00  
% 35.55/5.00  sup_time_total:                         0.
% 35.55/5.00  sup_time_generating:                    0.
% 35.55/5.00  sup_time_sim_full:                      0.
% 35.55/5.00  sup_time_sim_immed:                     0.
% 35.55/5.00  
% 35.55/5.00  sup_num_of_clauses:                     3166
% 35.55/5.00  sup_num_in_active:                      996
% 35.55/5.00  sup_num_in_passive:                     2170
% 35.55/5.00  sup_num_of_loops:                       1146
% 35.55/5.00  sup_fw_superposition:                   4435
% 35.55/5.00  sup_bw_superposition:                   1546
% 35.55/5.00  sup_immediate_simplified:               1639
% 35.55/5.00  sup_given_eliminated:                   27
% 35.55/5.00  comparisons_done:                       0
% 35.55/5.00  comparisons_avoided:                    221
% 35.55/5.00  
% 35.55/5.00  ------ Simplifications
% 35.55/5.00  
% 35.55/5.00  
% 35.55/5.00  sim_fw_subset_subsumed:                 150
% 35.55/5.00  sim_bw_subset_subsumed:                 87
% 35.55/5.00  sim_fw_subsumed:                        313
% 35.55/5.00  sim_bw_subsumed:                        183
% 35.55/5.00  sim_fw_subsumption_res:                 0
% 35.55/5.00  sim_bw_subsumption_res:                 0
% 35.55/5.00  sim_tautology_del:                      241
% 35.55/5.00  sim_eq_tautology_del:                   37
% 35.55/5.00  sim_eq_res_simp:                        0
% 35.55/5.00  sim_fw_demodulated:                     321
% 35.55/5.00  sim_bw_demodulated:                     12
% 35.55/5.00  sim_light_normalised:                   1048
% 35.55/5.00  sim_joinable_taut:                      0
% 35.55/5.00  sim_joinable_simp:                      0
% 35.55/5.00  sim_ac_normalised:                      0
% 35.55/5.00  sim_smt_subsumption:                    0
% 35.55/5.00  
%------------------------------------------------------------------------------
