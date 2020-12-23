%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:49 EST 2020

% Result     : Theorem 4.12s
% Output     : CNFRefutation 4.12s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 465 expanded)
%              Number of clauses        :   69 ( 119 expanded)
%              Number of leaves         :   14 ( 102 expanded)
%              Depth                    :   21
%              Number of atoms          :  388 (2710 expanded)
%              Number of equality atoms :  116 ( 157 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v3_pre_topc(X1,X0) )
           => ( v5_tops_1(X1,X0)
            <=> v6_tops_1(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v4_pre_topc(X1,X0)
                & v3_pre_topc(X1,X0) )
             => ( v5_tops_1(X1,X0)
              <=> v6_tops_1(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v5_tops_1(X1,X0)
          <~> v6_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v5_tops_1(X1,X0)
          <~> v6_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f55,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v6_tops_1(X1,X0)
            | ~ v5_tops_1(X1,X0) )
          & ( v6_tops_1(X1,X0)
            | v5_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f56,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v6_tops_1(X1,X0)
            | ~ v5_tops_1(X1,X0) )
          & ( v6_tops_1(X1,X0)
            | v5_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f55])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v6_tops_1(X1,X0)
            | ~ v5_tops_1(X1,X0) )
          & ( v6_tops_1(X1,X0)
            | v5_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ v6_tops_1(sK2,X0)
          | ~ v5_tops_1(sK2,X0) )
        & ( v6_tops_1(sK2,X0)
          | v5_tops_1(sK2,X0) )
        & v4_pre_topc(sK2,X0)
        & v3_pre_topc(sK2,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v6_tops_1(X1,X0)
              | ~ v5_tops_1(X1,X0) )
            & ( v6_tops_1(X1,X0)
              | v5_tops_1(X1,X0) )
            & v4_pre_topc(X1,X0)
            & v3_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v6_tops_1(X1,sK1)
            | ~ v5_tops_1(X1,sK1) )
          & ( v6_tops_1(X1,sK1)
            | v5_tops_1(X1,sK1) )
          & v4_pre_topc(X1,sK1)
          & v3_pre_topc(X1,sK1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ( ~ v6_tops_1(sK2,sK1)
      | ~ v5_tops_1(sK2,sK1) )
    & ( v6_tops_1(sK2,sK1)
      | v5_tops_1(sK2,sK1) )
    & v4_pre_topc(sK2,sK1)
    & v3_pre_topc(sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f56,f58,f57])).

fof(f90,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f59])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f91,plain,(
    v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f89,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f98,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f67,f69])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => k2_pre_topc(X0,X1) = X1 ) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = X1
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f92,plain,(
    v4_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f94,plain,
    ( ~ v6_tops_1(sK2,sK1)
    | ~ v5_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_tops_1(X1,X0)
              | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 )
            & ( k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
              | ~ v5_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v5_tops_1(X1,X0)
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_tops_1(X1,X0)
              | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 )
            & ( k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
              | ~ v6_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v6_tops_1(X1,X0)
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_18955,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_26,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_31,negated_conjecture,
    ( v3_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_442,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_31])).

cnf(c_443,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_tops_1(sK1,X0))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_442])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_447,plain,
    ( r1_tarski(sK2,k1_tops_1(sK1,X0))
    | ~ r1_tarski(sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_443,c_33,c_32])).

cnf(c_448,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(sK2,X0)
    | r1_tarski(sK2,k1_tops_1(sK1,X0)) ),
    inference(renaming,[status(thm)],[c_447])).

cnf(c_18948,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_448])).

cnf(c_19295,plain,
    ( r1_tarski(sK2,k1_tops_1(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_18955,c_18948])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2555,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2556,plain,
    ( r1_tarski(sK2,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2555])).

cnf(c_3878,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3877,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | r1_tarski(sK2,k1_tops_1(sK1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_448])).

cnf(c_3926,plain,
    ( r1_tarski(sK2,k1_tops_1(sK1,sK2)) = iProver_top
    | r1_tarski(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3878,c_3877])).

cnf(c_19312,plain,
    ( r1_tarski(sK2,k1_tops_1(sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19295,c_2556,c_3926])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_18963,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_19864,plain,
    ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_tops_1(sK1,sK2))) = sK2 ),
    inference(superposition,[status(thm)],[c_19312,c_18963])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_18958,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_19547,plain,
    ( r1_tarski(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_18955,c_18958])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_16,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_250,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_251,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_250])).

cnf(c_310,plain,
    ( ~ r1_tarski(X0,X1)
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_13,c_251])).

cnf(c_18952,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_310])).

cnf(c_19607,plain,
    ( k7_subset_1(u1_struct_0(sK1),sK2,X0) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[status(thm)],[c_19547,c_18952])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_467,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_33])).

cnf(c_468,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k7_subset_1(u1_struct_0(sK1),X0,k2_tops_1(sK1,X0)) = k1_tops_1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_467])).

cnf(c_18947,plain,
    ( k7_subset_1(u1_struct_0(sK1),X0,k2_tops_1(sK1,X0)) = k1_tops_1(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_468])).

cnf(c_19156,plain,
    ( k7_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k1_tops_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_18955,c_18947])).

cnf(c_19613,plain,
    ( k4_xboole_0(sK2,k2_tops_1(sK1,sK2)) = k1_tops_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_19607,c_19156])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_479,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_33])).

cnf(c_480,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X0),k1_tops_1(sK1,X0)) = k2_tops_1(sK1,X0) ),
    inference(unflattening,[status(thm)],[c_479])).

cnf(c_18946,plain,
    ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X0),k1_tops_1(sK1,X0)) = k2_tops_1(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_480])).

cnf(c_19179,plain,
    ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_18955,c_18946])).

cnf(c_20,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_30,negated_conjecture,
    ( v4_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_433,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_30])).

cnf(c_434,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k2_pre_topc(sK1,sK2) = sK2 ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_436,plain,
    ( k2_pre_topc(sK1,sK2) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_434,c_33,c_32])).

cnf(c_19180,plain,
    ( k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
    inference(light_normalisation,[status(thm)],[c_19179,c_436])).

cnf(c_19614,plain,
    ( k4_xboole_0(sK2,k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
    inference(superposition,[status(thm)],[c_19607,c_19180])).

cnf(c_19880,plain,
    ( k1_tops_1(sK1,sK2) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_19864,c_19613,c_19614])).

cnf(c_28,negated_conjecture,
    ( ~ v6_tops_1(sK2,sK1)
    | ~ v5_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_252,plain,
    ( ~ v6_tops_1(sK2,sK1)
    | ~ v5_tops_1(sK2,sK1) ),
    inference(prop_impl,[status(thm)],[c_28])).

cnf(c_21,plain,
    ( v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) != X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_536,plain,
    ( v5_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k1_tops_1(X1,X0)) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_33])).

cnf(c_537,plain,
    ( v5_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,k1_tops_1(sK1,X0)) != X0 ),
    inference(unflattening,[status(thm)],[c_536])).

cnf(c_589,plain,
    ( ~ v6_tops_1(sK2,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,k1_tops_1(sK1,X0)) != X0
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_252,c_537])).

cnf(c_590,plain,
    ( ~ v6_tops_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k2_pre_topc(sK1,k1_tops_1(sK1,sK2)) != sK2 ),
    inference(unflattening,[status(thm)],[c_589])).

cnf(c_592,plain,
    ( ~ v6_tops_1(sK2,sK1)
    | k2_pre_topc(sK1,k1_tops_1(sK1,sK2)) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_590,c_32])).

cnf(c_23,plain,
    ( v6_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_506,plain,
    ( v6_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_33])).

cnf(c_507,plain,
    ( v6_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,k2_pre_topc(sK1,X0)) != X0 ),
    inference(unflattening,[status(thm)],[c_506])).

cnf(c_622,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,k2_pre_topc(sK1,X0)) != X0
    | k2_pre_topc(sK1,k1_tops_1(sK1,sK2)) != sK2
    | sK1 != sK1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_592,c_507])).

cnf(c_623,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,k2_pre_topc(sK1,sK2)) != sK2
    | k2_pre_topc(sK1,k1_tops_1(sK1,sK2)) != sK2 ),
    inference(unflattening,[status(thm)],[c_622])).

cnf(c_715,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,sK2)) != sK2
    | k2_pre_topc(sK1,k1_tops_1(sK1,sK2)) != sK2 ),
    inference(prop_impl,[status(thm)],[c_32,c_623])).

cnf(c_19035,plain,
    ( k1_tops_1(sK1,sK2) != sK2
    | k2_pre_topc(sK1,k1_tops_1(sK1,sK2)) != sK2 ),
    inference(light_normalisation,[status(thm)],[c_715,c_436])).

cnf(c_20140,plain,
    ( k2_pre_topc(sK1,sK2) != sK2
    | sK2 != sK2 ),
    inference(demodulation,[status(thm)],[c_19880,c_19035])).

cnf(c_20141,plain,
    ( k2_pre_topc(sK1,sK2) != sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_20140])).

cnf(c_20143,plain,
    ( sK2 != sK2 ),
    inference(light_normalisation,[status(thm)],[c_20141,c_436])).

cnf(c_20144,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_20143])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:37:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 4.12/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.12/0.99  
% 4.12/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.12/0.99  
% 4.12/0.99  ------  iProver source info
% 4.12/0.99  
% 4.12/0.99  git: date: 2020-06-30 10:37:57 +0100
% 4.12/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.12/0.99  git: non_committed_changes: false
% 4.12/0.99  git: last_make_outside_of_git: false
% 4.12/0.99  
% 4.12/0.99  ------ 
% 4.12/0.99  ------ Parsing...
% 4.12/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  ------ Proving...
% 4.12/0.99  ------ Problem Properties 
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  clauses                                 26
% 4.12/0.99  conjectures                             2
% 4.12/0.99  EPR                                     4
% 4.12/0.99  Horn                                    24
% 4.12/0.99  unary                                   8
% 4.12/0.99  binary                                  13
% 4.12/0.99  lits                                    50
% 4.12/0.99  lits eq                                 14
% 4.12/0.99  fd_pure                                 0
% 4.12/0.99  fd_pseudo                               0
% 4.12/0.99  fd_cond                                 0
% 4.12/0.99  fd_pseudo_cond                          1
% 4.12/0.99  AC symbols                              0
% 4.12/0.99  
% 4.12/0.99  ------ Input Options Time Limit: Unbounded
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 4.12/0.99  Current options:
% 4.12/0.99  ------ 
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.12/0.99  
% 4.12/0.99  ------ Proving...
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  % SZS status Theorem for theBenchmark.p
% 4.12/0.99  
% 4.12/0.99   Resolution empty clause
% 4.12/0.99  
% 4.12/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 4.12/0.99  
% 4.12/0.99  fof(f23,conjecture,(
% 4.12/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0)) => (v5_tops_1(X1,X0) <=> v6_tops_1(X1,X0)))))),
% 4.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.12/0.99  
% 4.12/0.99  fof(f24,negated_conjecture,(
% 4.12/0.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0)) => (v5_tops_1(X1,X0) <=> v6_tops_1(X1,X0)))))),
% 4.12/0.99    inference(negated_conjecture,[],[f23])).
% 4.12/0.99  
% 4.12/0.99  fof(f44,plain,(
% 4.12/0.99    ? [X0] : (? [X1] : (((v5_tops_1(X1,X0) <~> v6_tops_1(X1,X0)) & (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 4.12/0.99    inference(ennf_transformation,[],[f24])).
% 4.12/0.99  
% 4.12/0.99  fof(f45,plain,(
% 4.12/0.99    ? [X0] : (? [X1] : ((v5_tops_1(X1,X0) <~> v6_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 4.12/0.99    inference(flattening,[],[f44])).
% 4.12/0.99  
% 4.12/0.99  fof(f55,plain,(
% 4.12/0.99    ? [X0] : (? [X1] : (((~v6_tops_1(X1,X0) | ~v5_tops_1(X1,X0)) & (v6_tops_1(X1,X0) | v5_tops_1(X1,X0))) & v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 4.12/0.99    inference(nnf_transformation,[],[f45])).
% 4.12/0.99  
% 4.12/0.99  fof(f56,plain,(
% 4.12/0.99    ? [X0] : (? [X1] : ((~v6_tops_1(X1,X0) | ~v5_tops_1(X1,X0)) & (v6_tops_1(X1,X0) | v5_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 4.12/0.99    inference(flattening,[],[f55])).
% 4.12/0.99  
% 4.12/0.99  fof(f58,plain,(
% 4.12/0.99    ( ! [X0] : (? [X1] : ((~v6_tops_1(X1,X0) | ~v5_tops_1(X1,X0)) & (v6_tops_1(X1,X0) | v5_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((~v6_tops_1(sK2,X0) | ~v5_tops_1(sK2,X0)) & (v6_tops_1(sK2,X0) | v5_tops_1(sK2,X0)) & v4_pre_topc(sK2,X0) & v3_pre_topc(sK2,X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 4.12/0.99    introduced(choice_axiom,[])).
% 4.12/0.99  
% 4.12/0.99  fof(f57,plain,(
% 4.12/0.99    ? [X0] : (? [X1] : ((~v6_tops_1(X1,X0) | ~v5_tops_1(X1,X0)) & (v6_tops_1(X1,X0) | v5_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((~v6_tops_1(X1,sK1) | ~v5_tops_1(X1,sK1)) & (v6_tops_1(X1,sK1) | v5_tops_1(X1,sK1)) & v4_pre_topc(X1,sK1) & v3_pre_topc(X1,sK1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1))),
% 4.12/0.99    introduced(choice_axiom,[])).
% 4.12/0.99  
% 4.12/0.99  fof(f59,plain,(
% 4.12/0.99    ((~v6_tops_1(sK2,sK1) | ~v5_tops_1(sK2,sK1)) & (v6_tops_1(sK2,sK1) | v5_tops_1(sK2,sK1)) & v4_pre_topc(sK2,sK1) & v3_pre_topc(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1)),
% 4.12/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f56,f58,f57])).
% 4.12/0.99  
% 4.12/0.99  fof(f90,plain,(
% 4.12/0.99    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 4.12/0.99    inference(cnf_transformation,[],[f59])).
% 4.12/0.99  
% 4.12/0.99  fof(f21,axiom,(
% 4.12/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 4.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.12/0.99  
% 4.12/0.99  fof(f41,plain,(
% 4.12/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.12/0.99    inference(ennf_transformation,[],[f21])).
% 4.12/0.99  
% 4.12/0.99  fof(f42,plain,(
% 4.12/0.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.12/0.99    inference(flattening,[],[f41])).
% 4.12/0.99  
% 4.12/0.99  fof(f87,plain,(
% 4.12/0.99    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.12/0.99    inference(cnf_transformation,[],[f42])).
% 4.12/0.99  
% 4.12/0.99  fof(f91,plain,(
% 4.12/0.99    v3_pre_topc(sK2,sK1)),
% 4.12/0.99    inference(cnf_transformation,[],[f59])).
% 4.12/0.99  
% 4.12/0.99  fof(f89,plain,(
% 4.12/0.99    l1_pre_topc(sK1)),
% 4.12/0.99    inference(cnf_transformation,[],[f59])).
% 4.12/0.99  
% 4.12/0.99  fof(f3,axiom,(
% 4.12/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.12/0.99  
% 4.12/0.99  fof(f50,plain,(
% 4.12/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.12/0.99    inference(nnf_transformation,[],[f3])).
% 4.12/0.99  
% 4.12/0.99  fof(f51,plain,(
% 4.12/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.12/0.99    inference(flattening,[],[f50])).
% 4.12/0.99  
% 4.12/0.99  fof(f64,plain,(
% 4.12/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 4.12/0.99    inference(cnf_transformation,[],[f51])).
% 4.12/0.99  
% 4.12/0.99  fof(f98,plain,(
% 4.12/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.12/0.99    inference(equality_resolution,[],[f64])).
% 4.12/0.99  
% 4.12/0.99  fof(f4,axiom,(
% 4.12/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 4.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.12/0.99  
% 4.12/0.99  fof(f27,plain,(
% 4.12/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 4.12/0.99    inference(ennf_transformation,[],[f4])).
% 4.12/0.99  
% 4.12/0.99  fof(f67,plain,(
% 4.12/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 4.12/0.99    inference(cnf_transformation,[],[f27])).
% 4.12/0.99  
% 4.12/0.99  fof(f6,axiom,(
% 4.12/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.12/0.99  
% 4.12/0.99  fof(f69,plain,(
% 4.12/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 4.12/0.99    inference(cnf_transformation,[],[f6])).
% 4.12/0.99  
% 4.12/0.99  fof(f96,plain,(
% 4.12/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 4.12/0.99    inference(definition_unfolding,[],[f67,f69])).
% 4.12/0.99  
% 4.12/0.99  fof(f14,axiom,(
% 4.12/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 4.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.12/0.99  
% 4.12/0.99  fof(f52,plain,(
% 4.12/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 4.12/0.99    inference(nnf_transformation,[],[f14])).
% 4.12/0.99  
% 4.12/0.99  fof(f77,plain,(
% 4.12/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 4.12/0.99    inference(cnf_transformation,[],[f52])).
% 4.12/0.99  
% 4.12/0.99  fof(f11,axiom,(
% 4.12/0.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 4.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.12/0.99  
% 4.12/0.99  fof(f30,plain,(
% 4.12/0.99    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.12/0.99    inference(ennf_transformation,[],[f11])).
% 4.12/0.99  
% 4.12/0.99  fof(f74,plain,(
% 4.12/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.12/0.99    inference(cnf_transformation,[],[f30])).
% 4.12/0.99  
% 4.12/0.99  fof(f78,plain,(
% 4.12/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 4.12/0.99    inference(cnf_transformation,[],[f52])).
% 4.12/0.99  
% 4.12/0.99  fof(f22,axiom,(
% 4.12/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 4.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.12/0.99  
% 4.12/0.99  fof(f43,plain,(
% 4.12/0.99    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.12/0.99    inference(ennf_transformation,[],[f22])).
% 4.12/0.99  
% 4.12/0.99  fof(f88,plain,(
% 4.12/0.99    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.12/0.99    inference(cnf_transformation,[],[f43])).
% 4.12/0.99  
% 4.12/0.99  fof(f20,axiom,(
% 4.12/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 4.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.12/0.99  
% 4.12/0.99  fof(f40,plain,(
% 4.12/0.99    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.12/0.99    inference(ennf_transformation,[],[f20])).
% 4.12/0.99  
% 4.12/0.99  fof(f86,plain,(
% 4.12/0.99    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.12/0.99    inference(cnf_transformation,[],[f40])).
% 4.12/0.99  
% 4.12/0.99  fof(f17,axiom,(
% 4.12/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 4.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.12/0.99  
% 4.12/0.99  fof(f25,plain,(
% 4.12/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1)))),
% 4.12/0.99    inference(pure_predicate_removal,[],[f17])).
% 4.12/0.99  
% 4.12/0.99  fof(f36,plain,(
% 4.12/0.99    ! [X0] : (! [X1] : ((k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.12/0.99    inference(ennf_transformation,[],[f25])).
% 4.12/0.99  
% 4.12/0.99  fof(f37,plain,(
% 4.12/0.99    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.12/0.99    inference(flattening,[],[f36])).
% 4.12/0.99  
% 4.12/0.99  fof(f81,plain,(
% 4.12/0.99    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.12/0.99    inference(cnf_transformation,[],[f37])).
% 4.12/0.99  
% 4.12/0.99  fof(f92,plain,(
% 4.12/0.99    v4_pre_topc(sK2,sK1)),
% 4.12/0.99    inference(cnf_transformation,[],[f59])).
% 4.12/0.99  
% 4.12/0.99  fof(f94,plain,(
% 4.12/0.99    ~v6_tops_1(sK2,sK1) | ~v5_tops_1(sK2,sK1)),
% 4.12/0.99    inference(cnf_transformation,[],[f59])).
% 4.12/0.99  
% 4.12/0.99  fof(f18,axiom,(
% 4.12/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 4.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.12/0.99  
% 4.12/0.99  fof(f38,plain,(
% 4.12/0.99    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.12/0.99    inference(ennf_transformation,[],[f18])).
% 4.12/0.99  
% 4.12/0.99  fof(f53,plain,(
% 4.12/0.99    ! [X0] : (! [X1] : (((v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1) & (k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.12/0.99    inference(nnf_transformation,[],[f38])).
% 4.12/0.99  
% 4.12/0.99  fof(f83,plain,(
% 4.12/0.99    ( ! [X0,X1] : (v5_tops_1(X1,X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.12/0.99    inference(cnf_transformation,[],[f53])).
% 4.12/0.99  
% 4.12/0.99  fof(f19,axiom,(
% 4.12/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1)))),
% 4.12/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.12/0.99  
% 4.12/0.99  fof(f39,plain,(
% 4.12/0.99    ! [X0] : (! [X1] : ((v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.12/0.99    inference(ennf_transformation,[],[f19])).
% 4.12/0.99  
% 4.12/0.99  fof(f54,plain,(
% 4.12/0.99    ! [X0] : (! [X1] : (((v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1) & (k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.12/0.99    inference(nnf_transformation,[],[f39])).
% 4.12/0.99  
% 4.12/0.99  fof(f85,plain,(
% 4.12/0.99    ( ! [X0,X1] : (v6_tops_1(X1,X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.12/0.99    inference(cnf_transformation,[],[f54])).
% 4.12/0.99  
% 4.12/0.99  cnf(c_32,negated_conjecture,
% 4.12/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 4.12/0.99      inference(cnf_transformation,[],[f90]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_18955,plain,
% 4.12/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 4.12/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_26,plain,
% 4.12/0.99      ( ~ v3_pre_topc(X0,X1)
% 4.12/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.12/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 4.12/0.99      | ~ r1_tarski(X0,X2)
% 4.12/0.99      | r1_tarski(X0,k1_tops_1(X1,X2))
% 4.12/0.99      | ~ l1_pre_topc(X1) ),
% 4.12/0.99      inference(cnf_transformation,[],[f87]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_31,negated_conjecture,
% 4.12/0.99      ( v3_pre_topc(sK2,sK1) ),
% 4.12/0.99      inference(cnf_transformation,[],[f91]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_442,plain,
% 4.12/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.12/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 4.12/0.99      | ~ r1_tarski(X0,X2)
% 4.12/0.99      | r1_tarski(X0,k1_tops_1(X1,X2))
% 4.12/0.99      | ~ l1_pre_topc(X1)
% 4.12/0.99      | sK1 != X1
% 4.12/0.99      | sK2 != X0 ),
% 4.12/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_31]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_443,plain,
% 4.12/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.12/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.12/0.99      | ~ r1_tarski(sK2,X0)
% 4.12/0.99      | r1_tarski(sK2,k1_tops_1(sK1,X0))
% 4.12/0.99      | ~ l1_pre_topc(sK1) ),
% 4.12/0.99      inference(unflattening,[status(thm)],[c_442]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_33,negated_conjecture,
% 4.12/0.99      ( l1_pre_topc(sK1) ),
% 4.12/0.99      inference(cnf_transformation,[],[f89]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_447,plain,
% 4.12/0.99      ( r1_tarski(sK2,k1_tops_1(sK1,X0))
% 4.12/0.99      | ~ r1_tarski(sK2,X0)
% 4.12/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 4.12/0.99      inference(global_propositional_subsumption,
% 4.12/0.99                [status(thm)],
% 4.12/0.99                [c_443,c_33,c_32]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_448,plain,
% 4.12/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.12/0.99      | ~ r1_tarski(sK2,X0)
% 4.12/0.99      | r1_tarski(sK2,k1_tops_1(sK1,X0)) ),
% 4.12/0.99      inference(renaming,[status(thm)],[c_447]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_18948,plain,
% 4.12/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 4.12/0.99      | r1_tarski(sK2,X0) != iProver_top
% 4.12/0.99      | r1_tarski(sK2,k1_tops_1(sK1,X0)) = iProver_top ),
% 4.12/0.99      inference(predicate_to_equality,[status(thm)],[c_448]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_19295,plain,
% 4.12/0.99      ( r1_tarski(sK2,k1_tops_1(sK1,sK2)) = iProver_top
% 4.12/0.99      | r1_tarski(sK2,sK2) != iProver_top ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_18955,c_18948]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_6,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f98]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_2555,plain,
% 4.12/0.99      ( r1_tarski(sK2,sK2) ),
% 4.12/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_2556,plain,
% 4.12/0.99      ( r1_tarski(sK2,sK2) = iProver_top ),
% 4.12/0.99      inference(predicate_to_equality,[status(thm)],[c_2555]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_3878,plain,
% 4.12/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 4.12/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_3877,plain,
% 4.12/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 4.12/0.99      | r1_tarski(sK2,X0) != iProver_top
% 4.12/0.99      | r1_tarski(sK2,k1_tops_1(sK1,X0)) = iProver_top ),
% 4.12/0.99      inference(predicate_to_equality,[status(thm)],[c_448]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_3926,plain,
% 4.12/0.99      ( r1_tarski(sK2,k1_tops_1(sK1,sK2)) = iProver_top
% 4.12/0.99      | r1_tarski(sK2,sK2) != iProver_top ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_3878,c_3877]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_19312,plain,
% 4.12/0.99      ( r1_tarski(sK2,k1_tops_1(sK1,sK2)) = iProver_top ),
% 4.12/0.99      inference(global_propositional_subsumption,
% 4.12/0.99                [status(thm)],
% 4.12/0.99                [c_19295,c_2556,c_3926]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_7,plain,
% 4.12/0.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 4.12/0.99      inference(cnf_transformation,[],[f96]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_18963,plain,
% 4.12/0.99      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 4.12/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 4.12/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_19864,plain,
% 4.12/0.99      ( k4_xboole_0(sK2,k4_xboole_0(sK2,k1_tops_1(sK1,sK2))) = sK2 ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_19312,c_18963]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_17,plain,
% 4.12/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 4.12/0.99      inference(cnf_transformation,[],[f77]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_18958,plain,
% 4.12/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.12/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 4.12/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_19547,plain,
% 4.12/0.99      ( r1_tarski(sK2,u1_struct_0(sK1)) = iProver_top ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_18955,c_18958]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_13,plain,
% 4.12/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.12/0.99      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 4.12/0.99      inference(cnf_transformation,[],[f74]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_16,plain,
% 4.12/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 4.12/0.99      inference(cnf_transformation,[],[f78]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_250,plain,
% 4.12/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 4.12/0.99      inference(prop_impl,[status(thm)],[c_16]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_251,plain,
% 4.12/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 4.12/0.99      inference(renaming,[status(thm)],[c_250]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_310,plain,
% 4.12/0.99      ( ~ r1_tarski(X0,X1) | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 4.12/0.99      inference(bin_hyper_res,[status(thm)],[c_13,c_251]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_18952,plain,
% 4.12/0.99      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 4.12/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 4.12/0.99      inference(predicate_to_equality,[status(thm)],[c_310]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_19607,plain,
% 4.12/0.99      ( k7_subset_1(u1_struct_0(sK1),sK2,X0) = k4_xboole_0(sK2,X0) ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_19547,c_18952]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_27,plain,
% 4.12/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.12/0.99      | ~ l1_pre_topc(X1)
% 4.12/0.99      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 4.12/0.99      inference(cnf_transformation,[],[f88]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_467,plain,
% 4.12/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.12/0.99      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0)
% 4.12/0.99      | sK1 != X1 ),
% 4.12/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_33]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_468,plain,
% 4.12/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.12/0.99      | k7_subset_1(u1_struct_0(sK1),X0,k2_tops_1(sK1,X0)) = k1_tops_1(sK1,X0) ),
% 4.12/0.99      inference(unflattening,[status(thm)],[c_467]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_18947,plain,
% 4.12/0.99      ( k7_subset_1(u1_struct_0(sK1),X0,k2_tops_1(sK1,X0)) = k1_tops_1(sK1,X0)
% 4.12/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 4.12/0.99      inference(predicate_to_equality,[status(thm)],[c_468]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_19156,plain,
% 4.12/0.99      ( k7_subset_1(u1_struct_0(sK1),sK2,k2_tops_1(sK1,sK2)) = k1_tops_1(sK1,sK2) ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_18955,c_18947]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_19613,plain,
% 4.12/0.99      ( k4_xboole_0(sK2,k2_tops_1(sK1,sK2)) = k1_tops_1(sK1,sK2) ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_19607,c_19156]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_25,plain,
% 4.12/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.12/0.99      | ~ l1_pre_topc(X1)
% 4.12/0.99      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 4.12/0.99      inference(cnf_transformation,[],[f86]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_479,plain,
% 4.12/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.12/0.99      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 4.12/0.99      | sK1 != X1 ),
% 4.12/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_33]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_480,plain,
% 4.12/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.12/0.99      | k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X0),k1_tops_1(sK1,X0)) = k2_tops_1(sK1,X0) ),
% 4.12/0.99      inference(unflattening,[status(thm)],[c_479]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_18946,plain,
% 4.12/0.99      ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,X0),k1_tops_1(sK1,X0)) = k2_tops_1(sK1,X0)
% 4.12/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 4.12/0.99      inference(predicate_to_equality,[status(thm)],[c_480]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_19179,plain,
% 4.12/0.99      ( k7_subset_1(u1_struct_0(sK1),k2_pre_topc(sK1,sK2),k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_18955,c_18946]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_20,plain,
% 4.12/0.99      ( ~ v4_pre_topc(X0,X1)
% 4.12/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.12/0.99      | ~ l1_pre_topc(X1)
% 4.12/0.99      | k2_pre_topc(X1,X0) = X0 ),
% 4.12/0.99      inference(cnf_transformation,[],[f81]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_30,negated_conjecture,
% 4.12/0.99      ( v4_pre_topc(sK2,sK1) ),
% 4.12/0.99      inference(cnf_transformation,[],[f92]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_433,plain,
% 4.12/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.12/0.99      | ~ l1_pre_topc(X1)
% 4.12/0.99      | k2_pre_topc(X1,X0) = X0
% 4.12/0.99      | sK1 != X1
% 4.12/0.99      | sK2 != X0 ),
% 4.12/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_30]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_434,plain,
% 4.12/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.12/0.99      | ~ l1_pre_topc(sK1)
% 4.12/0.99      | k2_pre_topc(sK1,sK2) = sK2 ),
% 4.12/0.99      inference(unflattening,[status(thm)],[c_433]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_436,plain,
% 4.12/0.99      ( k2_pre_topc(sK1,sK2) = sK2 ),
% 4.12/0.99      inference(global_propositional_subsumption,
% 4.12/0.99                [status(thm)],
% 4.12/0.99                [c_434,c_33,c_32]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_19180,plain,
% 4.12/0.99      ( k7_subset_1(u1_struct_0(sK1),sK2,k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
% 4.12/0.99      inference(light_normalisation,[status(thm)],[c_19179,c_436]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_19614,plain,
% 4.12/0.99      ( k4_xboole_0(sK2,k1_tops_1(sK1,sK2)) = k2_tops_1(sK1,sK2) ),
% 4.12/0.99      inference(superposition,[status(thm)],[c_19607,c_19180]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_19880,plain,
% 4.12/0.99      ( k1_tops_1(sK1,sK2) = sK2 ),
% 4.12/0.99      inference(light_normalisation,[status(thm)],[c_19864,c_19613,c_19614]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_28,negated_conjecture,
% 4.12/0.99      ( ~ v6_tops_1(sK2,sK1) | ~ v5_tops_1(sK2,sK1) ),
% 4.12/0.99      inference(cnf_transformation,[],[f94]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_252,plain,
% 4.12/0.99      ( ~ v6_tops_1(sK2,sK1) | ~ v5_tops_1(sK2,sK1) ),
% 4.12/0.99      inference(prop_impl,[status(thm)],[c_28]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_21,plain,
% 4.12/0.99      ( v5_tops_1(X0,X1)
% 4.12/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.12/0.99      | ~ l1_pre_topc(X1)
% 4.12/0.99      | k2_pre_topc(X1,k1_tops_1(X1,X0)) != X0 ),
% 4.12/0.99      inference(cnf_transformation,[],[f83]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_536,plain,
% 4.12/0.99      ( v5_tops_1(X0,X1)
% 4.12/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.12/0.99      | k2_pre_topc(X1,k1_tops_1(X1,X0)) != X0
% 4.12/0.99      | sK1 != X1 ),
% 4.12/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_33]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_537,plain,
% 4.12/0.99      ( v5_tops_1(X0,sK1)
% 4.12/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.12/0.99      | k2_pre_topc(sK1,k1_tops_1(sK1,X0)) != X0 ),
% 4.12/0.99      inference(unflattening,[status(thm)],[c_536]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_589,plain,
% 4.12/0.99      ( ~ v6_tops_1(sK2,sK1)
% 4.12/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.12/0.99      | k2_pre_topc(sK1,k1_tops_1(sK1,X0)) != X0
% 4.12/0.99      | sK1 != sK1
% 4.12/0.99      | sK2 != X0 ),
% 4.12/0.99      inference(resolution_lifted,[status(thm)],[c_252,c_537]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_590,plain,
% 4.12/0.99      ( ~ v6_tops_1(sK2,sK1)
% 4.12/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.12/0.99      | k2_pre_topc(sK1,k1_tops_1(sK1,sK2)) != sK2 ),
% 4.12/0.99      inference(unflattening,[status(thm)],[c_589]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_592,plain,
% 4.12/0.99      ( ~ v6_tops_1(sK2,sK1) | k2_pre_topc(sK1,k1_tops_1(sK1,sK2)) != sK2 ),
% 4.12/0.99      inference(global_propositional_subsumption,[status(thm)],[c_590,c_32]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_23,plain,
% 4.12/0.99      ( v6_tops_1(X0,X1)
% 4.12/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.12/0.99      | ~ l1_pre_topc(X1)
% 4.12/0.99      | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0 ),
% 4.12/0.99      inference(cnf_transformation,[],[f85]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_506,plain,
% 4.12/0.99      ( v6_tops_1(X0,X1)
% 4.12/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.12/0.99      | k1_tops_1(X1,k2_pre_topc(X1,X0)) != X0
% 4.12/0.99      | sK1 != X1 ),
% 4.12/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_33]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_507,plain,
% 4.12/0.99      ( v6_tops_1(X0,sK1)
% 4.12/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.12/0.99      | k1_tops_1(sK1,k2_pre_topc(sK1,X0)) != X0 ),
% 4.12/0.99      inference(unflattening,[status(thm)],[c_506]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_622,plain,
% 4.12/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.12/0.99      | k1_tops_1(sK1,k2_pre_topc(sK1,X0)) != X0
% 4.12/0.99      | k2_pre_topc(sK1,k1_tops_1(sK1,sK2)) != sK2
% 4.12/0.99      | sK1 != sK1
% 4.12/0.99      | sK2 != X0 ),
% 4.12/0.99      inference(resolution_lifted,[status(thm)],[c_592,c_507]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_623,plain,
% 4.12/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 4.12/0.99      | k1_tops_1(sK1,k2_pre_topc(sK1,sK2)) != sK2
% 4.12/0.99      | k2_pre_topc(sK1,k1_tops_1(sK1,sK2)) != sK2 ),
% 4.12/0.99      inference(unflattening,[status(thm)],[c_622]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_715,plain,
% 4.12/0.99      ( k1_tops_1(sK1,k2_pre_topc(sK1,sK2)) != sK2
% 4.12/0.99      | k2_pre_topc(sK1,k1_tops_1(sK1,sK2)) != sK2 ),
% 4.12/0.99      inference(prop_impl,[status(thm)],[c_32,c_623]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_19035,plain,
% 4.12/0.99      ( k1_tops_1(sK1,sK2) != sK2
% 4.12/0.99      | k2_pre_topc(sK1,k1_tops_1(sK1,sK2)) != sK2 ),
% 4.12/0.99      inference(light_normalisation,[status(thm)],[c_715,c_436]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_20140,plain,
% 4.12/0.99      ( k2_pre_topc(sK1,sK2) != sK2 | sK2 != sK2 ),
% 4.12/0.99      inference(demodulation,[status(thm)],[c_19880,c_19035]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_20141,plain,
% 4.12/0.99      ( k2_pre_topc(sK1,sK2) != sK2 ),
% 4.12/0.99      inference(equality_resolution_simp,[status(thm)],[c_20140]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_20143,plain,
% 4.12/0.99      ( sK2 != sK2 ),
% 4.12/0.99      inference(light_normalisation,[status(thm)],[c_20141,c_436]) ).
% 4.12/0.99  
% 4.12/0.99  cnf(c_20144,plain,
% 4.12/0.99      ( $false ),
% 4.12/0.99      inference(equality_resolution_simp,[status(thm)],[c_20143]) ).
% 4.12/0.99  
% 4.12/0.99  
% 4.12/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 4.12/0.99  
% 4.12/0.99  ------                               Statistics
% 4.12/0.99  
% 4.12/0.99  ------ Selected
% 4.12/0.99  
% 4.12/0.99  total_time:                             0.424
% 4.12/0.99  
%------------------------------------------------------------------------------
