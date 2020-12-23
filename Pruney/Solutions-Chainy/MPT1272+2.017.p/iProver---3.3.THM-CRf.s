%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:20 EST 2020

% Result     : Theorem 7.99s
% Output     : CNFRefutation 7.99s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 541 expanded)
%              Number of clauses        :   67 ( 165 expanded)
%              Number of leaves         :   13 ( 132 expanded)
%              Depth                    :   20
%              Number of atoms          :  364 (1977 expanded)
%              Number of equality atoms :   97 ( 183 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tops_1(X1,X0)
             => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          & v3_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),sK2),X0)
        & v3_tops_1(sK2,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
            & v3_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK1),X1),sK1)
          & v3_tops_1(X1,sK1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK1),sK2),sK1)
    & v3_tops_1(sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f46,f55,f54])).

fof(f81,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f56])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f80,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> v2_tops_1(k2_pre_topc(X0,X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tops_1(X1,X0)
              | ~ v2_tops_1(k2_pre_topc(X0,X1),X0) )
            & ( v2_tops_1(k2_pre_topc(X0,X1),X0)
              | ~ v3_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v2_tops_1(k2_pre_topc(X0,X1),X0)
      | ~ v3_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f82,plain,(
    v3_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f56])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f28])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => ( ( r1_tarski(X1,k3_subset_1(X0,X2))
          & r1_tarski(X1,X2) )
       => k1_xboole_0 = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f30])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X1
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v2_tops_1(X1,X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    ~ v1_tops_1(k3_subset_1(u1_struct_0(sK1),sK2),sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1365,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_22,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_485,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) = k1_xboole_0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_486,plain,
    ( ~ v2_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_485])).

cnf(c_18,plain,
    ( ~ v3_tops_1(X0,X1)
    | v2_tops_1(k2_pre_topc(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_24,negated_conjecture,
    ( v3_tops_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_398,plain,
    ( v2_tops_1(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_399,plain,
    ( v2_tops_1(k2_pre_topc(sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_401,plain,
    ( v2_tops_1(k2_pre_topc(sK1,sK2),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_399,c_26,c_25])).

cnf(c_594,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) = k1_xboole_0
    | k2_pre_topc(sK1,sK2) != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_486,c_401])).

cnf(c_595,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,k2_pre_topc(sK1,sK2)) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_594])).

cnf(c_1355,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,sK2)) = k1_xboole_0
    | m1_subset_1(k2_pre_topc(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_595])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_527,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_26])).

cnf(c_528,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_527])).

cnf(c_1531,plain,
    ( m1_subset_1(k2_pre_topc(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_528])).

cnf(c_1852,plain,
    ( k1_tops_1(sK1,k2_pre_topc(sK1,sK2)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1355,c_25,c_595,c_1531])).

cnf(c_20,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(X2,X0),k1_tops_1(X2,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_539,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(X2,X0),k1_tops_1(X2,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_26])).

cnf(c_540,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_539])).

cnf(c_1357,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_540])).

cnf(c_1855,plain,
    ( r1_tarski(X0,k2_pre_topc(sK1,sK2)) != iProver_top
    | r1_tarski(k1_tops_1(sK1,X0),k1_xboole_0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1852,c_1357])).

cnf(c_28,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1532,plain,
    ( m1_subset_1(k2_pre_topc(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1531])).

cnf(c_4868,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r1_tarski(k1_tops_1(sK1,X0),k1_xboole_0) = iProver_top
    | r1_tarski(X0,k2_pre_topc(sK1,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1855,c_28,c_1532])).

cnf(c_4869,plain,
    ( r1_tarski(X0,k2_pre_topc(sK1,sK2)) != iProver_top
    | r1_tarski(k1_tops_1(sK1,X0),k1_xboole_0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4868])).

cnf(c_4880,plain,
    ( r1_tarski(k1_tops_1(sK1,sK2),k1_xboole_0) = iProver_top
    | r1_tarski(sK2,k2_pre_topc(sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1365,c_4869])).

cnf(c_14,plain,
    ( r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_515,plain,
    ( r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_26])).

cnf(c_516,plain,
    ( r1_tarski(X0,k2_pre_topc(sK1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(unflattening,[status(thm)],[c_515])).

cnf(c_1537,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_516])).

cnf(c_1538,plain,
    ( r1_tarski(sK2,k2_pre_topc(sK1,sK2)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1537])).

cnf(c_4911,plain,
    ( r1_tarski(k1_tops_1(sK1,sK2),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4880,c_28,c_1538])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1367,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_10,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1368,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_12,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1366,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2429,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1368,c_1366])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k3_subset_1(X1,X2))
    | r1_tarski(X2,k3_subset_1(X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_212,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_271,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k3_subset_1(X1,X2))
    | r1_tarski(X2,k3_subset_1(X1,X0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_212])).

cnf(c_1361,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k3_subset_1(X1,X2)) != iProver_top
    | r1_tarski(X2,k3_subset_1(X1,X0)) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_271])).

cnf(c_6247,plain,
    ( r1_tarski(X0,k3_subset_1(X1,k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2429,c_1361])).

cnf(c_6259,plain,
    ( r1_tarski(X0,k3_subset_1(X1,k1_xboole_0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6247,c_2429])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,k3_subset_1(X2,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1373,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k3_subset_1(X2,X1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_30483,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6259,c_1373])).

cnf(c_31333,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_30483,c_1368])).

cnf(c_31337,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1367,c_31333])).

cnf(c_31398,plain,
    ( k1_tops_1(sK1,sK2) = k1_xboole_0
    | r1_tarski(k1_tops_1(sK1,sK2),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4911,c_31337])).

cnf(c_21,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_500,plain,
    ( v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,X0) != k1_xboole_0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_26])).

cnf(c_501,plain,
    ( v2_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_500])).

cnf(c_16,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
    | ~ v2_tops_1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_23,negated_conjecture,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK1),sK2),sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_372,plain,
    ( ~ v2_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k3_subset_1(u1_struct_0(X1),X0) != k3_subset_1(u1_struct_0(sK1),sK2)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_23])).

cnf(c_373,plain,
    ( ~ v2_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | k3_subset_1(u1_struct_0(sK1),X0) != k3_subset_1(u1_struct_0(sK1),sK2) ),
    inference(unflattening,[status(thm)],[c_372])).

cnf(c_377,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_tops_1(X0,sK1)
    | k3_subset_1(u1_struct_0(sK1),X0) != k3_subset_1(u1_struct_0(sK1),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_373,c_26])).

cnf(c_378,plain,
    ( ~ v2_tops_1(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_subset_1(u1_struct_0(sK1),X0) != k3_subset_1(u1_struct_0(sK1),sK2) ),
    inference(renaming,[status(thm)],[c_377])).

cnf(c_580,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_tops_1(sK1,X0) != k1_xboole_0
    | k3_subset_1(u1_struct_0(sK1),X0) != k3_subset_1(u1_struct_0(sK1),sK2) ),
    inference(resolution,[status(thm)],[c_501,c_378])).

cnf(c_1356,plain,
    ( k1_tops_1(sK1,X0) != k1_xboole_0
    | k3_subset_1(u1_struct_0(sK1),X0) != k3_subset_1(u1_struct_0(sK1),sK2)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_580])).

cnf(c_3743,plain,
    ( k1_tops_1(sK1,sK2) != k1_xboole_0
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1356])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_31398,c_4880,c_3743,c_1538,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:17:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.99/1.48  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.99/1.48  
% 7.99/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.99/1.48  
% 7.99/1.48  ------  iProver source info
% 7.99/1.48  
% 7.99/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.99/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.99/1.48  git: non_committed_changes: false
% 7.99/1.48  git: last_make_outside_of_git: false
% 7.99/1.48  
% 7.99/1.48  ------ 
% 7.99/1.48  
% 7.99/1.48  ------ Input Options
% 7.99/1.48  
% 7.99/1.48  --out_options                           all
% 7.99/1.48  --tptp_safe_out                         true
% 7.99/1.48  --problem_path                          ""
% 7.99/1.48  --include_path                          ""
% 7.99/1.48  --clausifier                            res/vclausify_rel
% 7.99/1.48  --clausifier_options                    --mode clausify
% 7.99/1.48  --stdin                                 false
% 7.99/1.48  --stats_out                             all
% 7.99/1.48  
% 7.99/1.48  ------ General Options
% 7.99/1.48  
% 7.99/1.48  --fof                                   false
% 7.99/1.48  --time_out_real                         305.
% 7.99/1.48  --time_out_virtual                      -1.
% 7.99/1.48  --symbol_type_check                     false
% 7.99/1.48  --clausify_out                          false
% 7.99/1.48  --sig_cnt_out                           false
% 7.99/1.48  --trig_cnt_out                          false
% 7.99/1.48  --trig_cnt_out_tolerance                1.
% 7.99/1.48  --trig_cnt_out_sk_spl                   false
% 7.99/1.48  --abstr_cl_out                          false
% 7.99/1.48  
% 7.99/1.48  ------ Global Options
% 7.99/1.48  
% 7.99/1.48  --schedule                              default
% 7.99/1.48  --add_important_lit                     false
% 7.99/1.48  --prop_solver_per_cl                    1000
% 7.99/1.48  --min_unsat_core                        false
% 7.99/1.48  --soft_assumptions                      false
% 7.99/1.48  --soft_lemma_size                       3
% 7.99/1.48  --prop_impl_unit_size                   0
% 7.99/1.48  --prop_impl_unit                        []
% 7.99/1.48  --share_sel_clauses                     true
% 7.99/1.48  --reset_solvers                         false
% 7.99/1.48  --bc_imp_inh                            [conj_cone]
% 7.99/1.48  --conj_cone_tolerance                   3.
% 7.99/1.48  --extra_neg_conj                        none
% 7.99/1.48  --large_theory_mode                     true
% 7.99/1.48  --prolific_symb_bound                   200
% 7.99/1.48  --lt_threshold                          2000
% 7.99/1.48  --clause_weak_htbl                      true
% 7.99/1.48  --gc_record_bc_elim                     false
% 7.99/1.48  
% 7.99/1.48  ------ Preprocessing Options
% 7.99/1.48  
% 7.99/1.48  --preprocessing_flag                    true
% 7.99/1.48  --time_out_prep_mult                    0.1
% 7.99/1.48  --splitting_mode                        input
% 7.99/1.48  --splitting_grd                         true
% 7.99/1.48  --splitting_cvd                         false
% 7.99/1.48  --splitting_cvd_svl                     false
% 7.99/1.48  --splitting_nvd                         32
% 7.99/1.48  --sub_typing                            true
% 7.99/1.48  --prep_gs_sim                           true
% 7.99/1.48  --prep_unflatten                        true
% 7.99/1.48  --prep_res_sim                          true
% 7.99/1.48  --prep_upred                            true
% 7.99/1.48  --prep_sem_filter                       exhaustive
% 7.99/1.48  --prep_sem_filter_out                   false
% 7.99/1.48  --pred_elim                             true
% 7.99/1.48  --res_sim_input                         true
% 7.99/1.48  --eq_ax_congr_red                       true
% 7.99/1.48  --pure_diseq_elim                       true
% 7.99/1.48  --brand_transform                       false
% 7.99/1.48  --non_eq_to_eq                          false
% 7.99/1.48  --prep_def_merge                        true
% 7.99/1.48  --prep_def_merge_prop_impl              false
% 7.99/1.48  --prep_def_merge_mbd                    true
% 7.99/1.48  --prep_def_merge_tr_red                 false
% 7.99/1.48  --prep_def_merge_tr_cl                  false
% 7.99/1.48  --smt_preprocessing                     true
% 7.99/1.48  --smt_ac_axioms                         fast
% 7.99/1.48  --preprocessed_out                      false
% 7.99/1.48  --preprocessed_stats                    false
% 7.99/1.48  
% 7.99/1.48  ------ Abstraction refinement Options
% 7.99/1.48  
% 7.99/1.48  --abstr_ref                             []
% 7.99/1.48  --abstr_ref_prep                        false
% 7.99/1.48  --abstr_ref_until_sat                   false
% 7.99/1.48  --abstr_ref_sig_restrict                funpre
% 7.99/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.99/1.48  --abstr_ref_under                       []
% 7.99/1.48  
% 7.99/1.48  ------ SAT Options
% 7.99/1.48  
% 7.99/1.48  --sat_mode                              false
% 7.99/1.48  --sat_fm_restart_options                ""
% 7.99/1.48  --sat_gr_def                            false
% 7.99/1.48  --sat_epr_types                         true
% 7.99/1.48  --sat_non_cyclic_types                  false
% 7.99/1.48  --sat_finite_models                     false
% 7.99/1.48  --sat_fm_lemmas                         false
% 7.99/1.48  --sat_fm_prep                           false
% 7.99/1.48  --sat_fm_uc_incr                        true
% 7.99/1.48  --sat_out_model                         small
% 7.99/1.48  --sat_out_clauses                       false
% 7.99/1.48  
% 7.99/1.48  ------ QBF Options
% 7.99/1.48  
% 7.99/1.48  --qbf_mode                              false
% 7.99/1.48  --qbf_elim_univ                         false
% 7.99/1.48  --qbf_dom_inst                          none
% 7.99/1.48  --qbf_dom_pre_inst                      false
% 7.99/1.48  --qbf_sk_in                             false
% 7.99/1.48  --qbf_pred_elim                         true
% 7.99/1.48  --qbf_split                             512
% 7.99/1.48  
% 7.99/1.48  ------ BMC1 Options
% 7.99/1.48  
% 7.99/1.48  --bmc1_incremental                      false
% 7.99/1.48  --bmc1_axioms                           reachable_all
% 7.99/1.48  --bmc1_min_bound                        0
% 7.99/1.48  --bmc1_max_bound                        -1
% 7.99/1.48  --bmc1_max_bound_default                -1
% 7.99/1.48  --bmc1_symbol_reachability              true
% 7.99/1.48  --bmc1_property_lemmas                  false
% 7.99/1.48  --bmc1_k_induction                      false
% 7.99/1.48  --bmc1_non_equiv_states                 false
% 7.99/1.48  --bmc1_deadlock                         false
% 7.99/1.48  --bmc1_ucm                              false
% 7.99/1.48  --bmc1_add_unsat_core                   none
% 7.99/1.48  --bmc1_unsat_core_children              false
% 7.99/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.99/1.48  --bmc1_out_stat                         full
% 7.99/1.48  --bmc1_ground_init                      false
% 7.99/1.48  --bmc1_pre_inst_next_state              false
% 7.99/1.48  --bmc1_pre_inst_state                   false
% 7.99/1.48  --bmc1_pre_inst_reach_state             false
% 7.99/1.48  --bmc1_out_unsat_core                   false
% 7.99/1.48  --bmc1_aig_witness_out                  false
% 7.99/1.48  --bmc1_verbose                          false
% 7.99/1.48  --bmc1_dump_clauses_tptp                false
% 7.99/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.99/1.48  --bmc1_dump_file                        -
% 7.99/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.99/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.99/1.48  --bmc1_ucm_extend_mode                  1
% 7.99/1.48  --bmc1_ucm_init_mode                    2
% 7.99/1.48  --bmc1_ucm_cone_mode                    none
% 7.99/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.99/1.48  --bmc1_ucm_relax_model                  4
% 7.99/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.99/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.99/1.48  --bmc1_ucm_layered_model                none
% 7.99/1.48  --bmc1_ucm_max_lemma_size               10
% 7.99/1.48  
% 7.99/1.48  ------ AIG Options
% 7.99/1.48  
% 7.99/1.48  --aig_mode                              false
% 7.99/1.48  
% 7.99/1.48  ------ Instantiation Options
% 7.99/1.48  
% 7.99/1.48  --instantiation_flag                    true
% 7.99/1.48  --inst_sos_flag                         false
% 7.99/1.48  --inst_sos_phase                        true
% 7.99/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.99/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.99/1.48  --inst_lit_sel_side                     num_symb
% 7.99/1.48  --inst_solver_per_active                1400
% 7.99/1.48  --inst_solver_calls_frac                1.
% 7.99/1.48  --inst_passive_queue_type               priority_queues
% 7.99/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.99/1.48  --inst_passive_queues_freq              [25;2]
% 7.99/1.48  --inst_dismatching                      true
% 7.99/1.48  --inst_eager_unprocessed_to_passive     true
% 7.99/1.48  --inst_prop_sim_given                   true
% 7.99/1.48  --inst_prop_sim_new                     false
% 7.99/1.48  --inst_subs_new                         false
% 7.99/1.48  --inst_eq_res_simp                      false
% 7.99/1.48  --inst_subs_given                       false
% 7.99/1.48  --inst_orphan_elimination               true
% 7.99/1.48  --inst_learning_loop_flag               true
% 7.99/1.48  --inst_learning_start                   3000
% 7.99/1.48  --inst_learning_factor                  2
% 7.99/1.48  --inst_start_prop_sim_after_learn       3
% 7.99/1.48  --inst_sel_renew                        solver
% 7.99/1.48  --inst_lit_activity_flag                true
% 7.99/1.48  --inst_restr_to_given                   false
% 7.99/1.48  --inst_activity_threshold               500
% 7.99/1.48  --inst_out_proof                        true
% 7.99/1.48  
% 7.99/1.48  ------ Resolution Options
% 7.99/1.48  
% 7.99/1.48  --resolution_flag                       true
% 7.99/1.48  --res_lit_sel                           adaptive
% 7.99/1.48  --res_lit_sel_side                      none
% 7.99/1.48  --res_ordering                          kbo
% 7.99/1.48  --res_to_prop_solver                    active
% 7.99/1.48  --res_prop_simpl_new                    false
% 7.99/1.48  --res_prop_simpl_given                  true
% 7.99/1.48  --res_passive_queue_type                priority_queues
% 7.99/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.99/1.48  --res_passive_queues_freq               [15;5]
% 7.99/1.48  --res_forward_subs                      full
% 7.99/1.48  --res_backward_subs                     full
% 7.99/1.48  --res_forward_subs_resolution           true
% 7.99/1.48  --res_backward_subs_resolution          true
% 7.99/1.48  --res_orphan_elimination                true
% 7.99/1.48  --res_time_limit                        2.
% 7.99/1.48  --res_out_proof                         true
% 7.99/1.48  
% 7.99/1.48  ------ Superposition Options
% 7.99/1.48  
% 7.99/1.48  --superposition_flag                    true
% 7.99/1.48  --sup_passive_queue_type                priority_queues
% 7.99/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.99/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.99/1.48  --demod_completeness_check              fast
% 7.99/1.48  --demod_use_ground                      true
% 7.99/1.48  --sup_to_prop_solver                    passive
% 7.99/1.48  --sup_prop_simpl_new                    true
% 7.99/1.48  --sup_prop_simpl_given                  true
% 7.99/1.48  --sup_fun_splitting                     false
% 7.99/1.48  --sup_smt_interval                      50000
% 7.99/1.48  
% 7.99/1.48  ------ Superposition Simplification Setup
% 7.99/1.48  
% 7.99/1.48  --sup_indices_passive                   []
% 7.99/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.99/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.99/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.99/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.99/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.99/1.48  --sup_full_bw                           [BwDemod]
% 7.99/1.48  --sup_immed_triv                        [TrivRules]
% 7.99/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.99/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.99/1.48  --sup_immed_bw_main                     []
% 7.99/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.99/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.99/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.99/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.99/1.48  
% 7.99/1.48  ------ Combination Options
% 7.99/1.48  
% 7.99/1.48  --comb_res_mult                         3
% 7.99/1.48  --comb_sup_mult                         2
% 7.99/1.48  --comb_inst_mult                        10
% 7.99/1.48  
% 7.99/1.48  ------ Debug Options
% 7.99/1.48  
% 7.99/1.48  --dbg_backtrace                         false
% 7.99/1.48  --dbg_dump_prop_clauses                 false
% 7.99/1.48  --dbg_dump_prop_clauses_file            -
% 7.99/1.48  --dbg_out_stat                          false
% 7.99/1.48  ------ Parsing...
% 7.99/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.99/1.48  
% 7.99/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 7.99/1.48  
% 7.99/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.99/1.48  
% 7.99/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.99/1.48  ------ Proving...
% 7.99/1.48  ------ Problem Properties 
% 7.99/1.48  
% 7.99/1.48  
% 7.99/1.48  clauses                                 21
% 7.99/1.48  conjectures                             1
% 7.99/1.48  EPR                                     0
% 7.99/1.48  Horn                                    21
% 7.99/1.48  unary                                   3
% 7.99/1.48  binary                                  9
% 7.99/1.48  lits                                    56
% 7.99/1.48  lits eq                                 7
% 7.99/1.48  fd_pure                                 0
% 7.99/1.48  fd_pseudo                               0
% 7.99/1.48  fd_cond                                 1
% 7.99/1.48  fd_pseudo_cond                          0
% 7.99/1.48  AC symbols                              0
% 7.99/1.48  
% 7.99/1.48  ------ Schedule dynamic 5 is on 
% 7.99/1.48  
% 7.99/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.99/1.48  
% 7.99/1.48  
% 7.99/1.48  ------ 
% 7.99/1.48  Current options:
% 7.99/1.48  ------ 
% 7.99/1.48  
% 7.99/1.48  ------ Input Options
% 7.99/1.48  
% 7.99/1.48  --out_options                           all
% 7.99/1.48  --tptp_safe_out                         true
% 7.99/1.48  --problem_path                          ""
% 7.99/1.48  --include_path                          ""
% 7.99/1.48  --clausifier                            res/vclausify_rel
% 7.99/1.48  --clausifier_options                    --mode clausify
% 7.99/1.48  --stdin                                 false
% 7.99/1.48  --stats_out                             all
% 7.99/1.48  
% 7.99/1.48  ------ General Options
% 7.99/1.48  
% 7.99/1.48  --fof                                   false
% 7.99/1.48  --time_out_real                         305.
% 7.99/1.48  --time_out_virtual                      -1.
% 7.99/1.48  --symbol_type_check                     false
% 7.99/1.48  --clausify_out                          false
% 7.99/1.48  --sig_cnt_out                           false
% 7.99/1.48  --trig_cnt_out                          false
% 7.99/1.48  --trig_cnt_out_tolerance                1.
% 7.99/1.48  --trig_cnt_out_sk_spl                   false
% 7.99/1.48  --abstr_cl_out                          false
% 7.99/1.48  
% 7.99/1.48  ------ Global Options
% 7.99/1.48  
% 7.99/1.48  --schedule                              default
% 7.99/1.48  --add_important_lit                     false
% 7.99/1.48  --prop_solver_per_cl                    1000
% 7.99/1.48  --min_unsat_core                        false
% 7.99/1.48  --soft_assumptions                      false
% 7.99/1.48  --soft_lemma_size                       3
% 7.99/1.48  --prop_impl_unit_size                   0
% 7.99/1.48  --prop_impl_unit                        []
% 7.99/1.48  --share_sel_clauses                     true
% 7.99/1.48  --reset_solvers                         false
% 7.99/1.48  --bc_imp_inh                            [conj_cone]
% 7.99/1.48  --conj_cone_tolerance                   3.
% 7.99/1.48  --extra_neg_conj                        none
% 7.99/1.48  --large_theory_mode                     true
% 7.99/1.48  --prolific_symb_bound                   200
% 7.99/1.48  --lt_threshold                          2000
% 7.99/1.48  --clause_weak_htbl                      true
% 7.99/1.48  --gc_record_bc_elim                     false
% 7.99/1.48  
% 7.99/1.48  ------ Preprocessing Options
% 7.99/1.48  
% 7.99/1.48  --preprocessing_flag                    true
% 7.99/1.48  --time_out_prep_mult                    0.1
% 7.99/1.48  --splitting_mode                        input
% 7.99/1.48  --splitting_grd                         true
% 7.99/1.48  --splitting_cvd                         false
% 7.99/1.48  --splitting_cvd_svl                     false
% 7.99/1.48  --splitting_nvd                         32
% 7.99/1.48  --sub_typing                            true
% 7.99/1.48  --prep_gs_sim                           true
% 7.99/1.48  --prep_unflatten                        true
% 7.99/1.48  --prep_res_sim                          true
% 7.99/1.48  --prep_upred                            true
% 7.99/1.48  --prep_sem_filter                       exhaustive
% 7.99/1.48  --prep_sem_filter_out                   false
% 7.99/1.48  --pred_elim                             true
% 7.99/1.48  --res_sim_input                         true
% 7.99/1.48  --eq_ax_congr_red                       true
% 7.99/1.48  --pure_diseq_elim                       true
% 7.99/1.48  --brand_transform                       false
% 7.99/1.48  --non_eq_to_eq                          false
% 7.99/1.48  --prep_def_merge                        true
% 7.99/1.48  --prep_def_merge_prop_impl              false
% 7.99/1.48  --prep_def_merge_mbd                    true
% 7.99/1.48  --prep_def_merge_tr_red                 false
% 7.99/1.48  --prep_def_merge_tr_cl                  false
% 7.99/1.48  --smt_preprocessing                     true
% 7.99/1.48  --smt_ac_axioms                         fast
% 7.99/1.48  --preprocessed_out                      false
% 7.99/1.48  --preprocessed_stats                    false
% 7.99/1.48  
% 7.99/1.48  ------ Abstraction refinement Options
% 7.99/1.48  
% 7.99/1.48  --abstr_ref                             []
% 7.99/1.48  --abstr_ref_prep                        false
% 7.99/1.48  --abstr_ref_until_sat                   false
% 7.99/1.48  --abstr_ref_sig_restrict                funpre
% 7.99/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.99/1.48  --abstr_ref_under                       []
% 7.99/1.48  
% 7.99/1.48  ------ SAT Options
% 7.99/1.48  
% 7.99/1.48  --sat_mode                              false
% 7.99/1.48  --sat_fm_restart_options                ""
% 7.99/1.48  --sat_gr_def                            false
% 7.99/1.48  --sat_epr_types                         true
% 7.99/1.48  --sat_non_cyclic_types                  false
% 7.99/1.48  --sat_finite_models                     false
% 7.99/1.48  --sat_fm_lemmas                         false
% 7.99/1.48  --sat_fm_prep                           false
% 7.99/1.48  --sat_fm_uc_incr                        true
% 7.99/1.48  --sat_out_model                         small
% 7.99/1.48  --sat_out_clauses                       false
% 7.99/1.48  
% 7.99/1.48  ------ QBF Options
% 7.99/1.48  
% 7.99/1.48  --qbf_mode                              false
% 7.99/1.48  --qbf_elim_univ                         false
% 7.99/1.48  --qbf_dom_inst                          none
% 7.99/1.48  --qbf_dom_pre_inst                      false
% 7.99/1.48  --qbf_sk_in                             false
% 7.99/1.48  --qbf_pred_elim                         true
% 7.99/1.48  --qbf_split                             512
% 7.99/1.48  
% 7.99/1.48  ------ BMC1 Options
% 7.99/1.48  
% 7.99/1.48  --bmc1_incremental                      false
% 7.99/1.48  --bmc1_axioms                           reachable_all
% 7.99/1.48  --bmc1_min_bound                        0
% 7.99/1.48  --bmc1_max_bound                        -1
% 7.99/1.48  --bmc1_max_bound_default                -1
% 7.99/1.48  --bmc1_symbol_reachability              true
% 7.99/1.48  --bmc1_property_lemmas                  false
% 7.99/1.48  --bmc1_k_induction                      false
% 7.99/1.48  --bmc1_non_equiv_states                 false
% 7.99/1.48  --bmc1_deadlock                         false
% 7.99/1.48  --bmc1_ucm                              false
% 7.99/1.48  --bmc1_add_unsat_core                   none
% 7.99/1.48  --bmc1_unsat_core_children              false
% 7.99/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.99/1.48  --bmc1_out_stat                         full
% 7.99/1.48  --bmc1_ground_init                      false
% 7.99/1.48  --bmc1_pre_inst_next_state              false
% 7.99/1.48  --bmc1_pre_inst_state                   false
% 7.99/1.48  --bmc1_pre_inst_reach_state             false
% 7.99/1.48  --bmc1_out_unsat_core                   false
% 7.99/1.48  --bmc1_aig_witness_out                  false
% 7.99/1.48  --bmc1_verbose                          false
% 7.99/1.48  --bmc1_dump_clauses_tptp                false
% 7.99/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.99/1.48  --bmc1_dump_file                        -
% 7.99/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.99/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.99/1.48  --bmc1_ucm_extend_mode                  1
% 7.99/1.48  --bmc1_ucm_init_mode                    2
% 7.99/1.48  --bmc1_ucm_cone_mode                    none
% 7.99/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.99/1.48  --bmc1_ucm_relax_model                  4
% 7.99/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.99/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.99/1.48  --bmc1_ucm_layered_model                none
% 7.99/1.48  --bmc1_ucm_max_lemma_size               10
% 7.99/1.48  
% 7.99/1.48  ------ AIG Options
% 7.99/1.48  
% 7.99/1.48  --aig_mode                              false
% 7.99/1.48  
% 7.99/1.48  ------ Instantiation Options
% 7.99/1.48  
% 7.99/1.48  --instantiation_flag                    true
% 7.99/1.48  --inst_sos_flag                         false
% 7.99/1.48  --inst_sos_phase                        true
% 7.99/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.99/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.99/1.48  --inst_lit_sel_side                     none
% 7.99/1.48  --inst_solver_per_active                1400
% 7.99/1.48  --inst_solver_calls_frac                1.
% 7.99/1.48  --inst_passive_queue_type               priority_queues
% 7.99/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.99/1.48  --inst_passive_queues_freq              [25;2]
% 7.99/1.48  --inst_dismatching                      true
% 7.99/1.48  --inst_eager_unprocessed_to_passive     true
% 7.99/1.48  --inst_prop_sim_given                   true
% 7.99/1.48  --inst_prop_sim_new                     false
% 7.99/1.48  --inst_subs_new                         false
% 7.99/1.48  --inst_eq_res_simp                      false
% 7.99/1.48  --inst_subs_given                       false
% 7.99/1.48  --inst_orphan_elimination               true
% 7.99/1.48  --inst_learning_loop_flag               true
% 7.99/1.48  --inst_learning_start                   3000
% 7.99/1.48  --inst_learning_factor                  2
% 7.99/1.48  --inst_start_prop_sim_after_learn       3
% 7.99/1.48  --inst_sel_renew                        solver
% 7.99/1.48  --inst_lit_activity_flag                true
% 7.99/1.48  --inst_restr_to_given                   false
% 7.99/1.48  --inst_activity_threshold               500
% 7.99/1.48  --inst_out_proof                        true
% 7.99/1.48  
% 7.99/1.48  ------ Resolution Options
% 7.99/1.48  
% 7.99/1.48  --resolution_flag                       false
% 7.99/1.48  --res_lit_sel                           adaptive
% 7.99/1.48  --res_lit_sel_side                      none
% 7.99/1.48  --res_ordering                          kbo
% 7.99/1.48  --res_to_prop_solver                    active
% 7.99/1.48  --res_prop_simpl_new                    false
% 7.99/1.48  --res_prop_simpl_given                  true
% 7.99/1.48  --res_passive_queue_type                priority_queues
% 7.99/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.99/1.48  --res_passive_queues_freq               [15;5]
% 7.99/1.48  --res_forward_subs                      full
% 7.99/1.48  --res_backward_subs                     full
% 7.99/1.48  --res_forward_subs_resolution           true
% 7.99/1.48  --res_backward_subs_resolution          true
% 7.99/1.48  --res_orphan_elimination                true
% 7.99/1.48  --res_time_limit                        2.
% 7.99/1.48  --res_out_proof                         true
% 7.99/1.48  
% 7.99/1.48  ------ Superposition Options
% 7.99/1.48  
% 7.99/1.48  --superposition_flag                    true
% 7.99/1.48  --sup_passive_queue_type                priority_queues
% 7.99/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.99/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.99/1.48  --demod_completeness_check              fast
% 7.99/1.48  --demod_use_ground                      true
% 7.99/1.48  --sup_to_prop_solver                    passive
% 7.99/1.48  --sup_prop_simpl_new                    true
% 7.99/1.48  --sup_prop_simpl_given                  true
% 7.99/1.48  --sup_fun_splitting                     false
% 7.99/1.48  --sup_smt_interval                      50000
% 7.99/1.48  
% 7.99/1.48  ------ Superposition Simplification Setup
% 7.99/1.48  
% 7.99/1.48  --sup_indices_passive                   []
% 7.99/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.99/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.99/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.99/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.99/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.99/1.48  --sup_full_bw                           [BwDemod]
% 7.99/1.48  --sup_immed_triv                        [TrivRules]
% 7.99/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.99/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.99/1.48  --sup_immed_bw_main                     []
% 7.99/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.99/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.99/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.99/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.99/1.48  
% 7.99/1.48  ------ Combination Options
% 7.99/1.48  
% 7.99/1.48  --comb_res_mult                         3
% 7.99/1.48  --comb_sup_mult                         2
% 7.99/1.48  --comb_inst_mult                        10
% 7.99/1.48  
% 7.99/1.48  ------ Debug Options
% 7.99/1.48  
% 7.99/1.48  --dbg_backtrace                         false
% 7.99/1.48  --dbg_dump_prop_clauses                 false
% 7.99/1.48  --dbg_dump_prop_clauses_file            -
% 7.99/1.48  --dbg_out_stat                          false
% 7.99/1.48  
% 7.99/1.48  
% 7.99/1.48  
% 7.99/1.48  
% 7.99/1.48  ------ Proving...
% 7.99/1.48  
% 7.99/1.48  
% 7.99/1.48  % SZS status Theorem for theBenchmark.p
% 7.99/1.48  
% 7.99/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.99/1.48  
% 7.99/1.48  fof(f20,conjecture,(
% 7.99/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 7.99/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.99/1.48  
% 7.99/1.48  fof(f21,negated_conjecture,(
% 7.99/1.48    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 7.99/1.48    inference(negated_conjecture,[],[f20])).
% 7.99/1.48  
% 7.99/1.48  fof(f45,plain,(
% 7.99/1.48    ? [X0] : (? [X1] : ((~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.99/1.48    inference(ennf_transformation,[],[f21])).
% 7.99/1.48  
% 7.99/1.48  fof(f46,plain,(
% 7.99/1.48    ? [X0] : (? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 7.99/1.48    inference(flattening,[],[f45])).
% 7.99/1.48  
% 7.99/1.48  fof(f55,plain,(
% 7.99/1.48    ( ! [X0] : (? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_tops_1(k3_subset_1(u1_struct_0(X0),sK2),X0) & v3_tops_1(sK2,X0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.99/1.48    introduced(choice_axiom,[])).
% 7.99/1.48  
% 7.99/1.48  fof(f54,plain,(
% 7.99/1.48    ? [X0] : (? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) & v3_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (~v1_tops_1(k3_subset_1(u1_struct_0(sK1),X1),sK1) & v3_tops_1(X1,sK1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1))),
% 7.99/1.48    introduced(choice_axiom,[])).
% 7.99/1.48  
% 7.99/1.48  fof(f56,plain,(
% 7.99/1.48    (~v1_tops_1(k3_subset_1(u1_struct_0(sK1),sK2),sK1) & v3_tops_1(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK1)),
% 7.99/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f46,f55,f54])).
% 7.99/1.48  
% 7.99/1.48  fof(f81,plain,(
% 7.99/1.48    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 7.99/1.48    inference(cnf_transformation,[],[f56])).
% 7.99/1.48  
% 7.99/1.48  fof(f19,axiom,(
% 7.99/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 7.99/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.99/1.48  
% 7.99/1.48  fof(f44,plain,(
% 7.99/1.48    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.99/1.48    inference(ennf_transformation,[],[f19])).
% 7.99/1.48  
% 7.99/1.48  fof(f53,plain,(
% 7.99/1.48    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.99/1.48    inference(nnf_transformation,[],[f44])).
% 7.99/1.48  
% 7.99/1.48  fof(f78,plain,(
% 7.99/1.48    ( ! [X0,X1] : (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.99/1.48    inference(cnf_transformation,[],[f53])).
% 7.99/1.48  
% 7.99/1.48  fof(f80,plain,(
% 7.99/1.48    l1_pre_topc(sK1)),
% 7.99/1.48    inference(cnf_transformation,[],[f56])).
% 7.99/1.48  
% 7.99/1.48  fof(f16,axiom,(
% 7.99/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0))))),
% 7.99/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.99/1.48  
% 7.99/1.48  fof(f40,plain,(
% 7.99/1.48    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) <=> v2_tops_1(k2_pre_topc(X0,X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.99/1.48    inference(ennf_transformation,[],[f16])).
% 7.99/1.48  
% 7.99/1.48  fof(f52,plain,(
% 7.99/1.48    ! [X0] : (! [X1] : (((v3_tops_1(X1,X0) | ~v2_tops_1(k2_pre_topc(X0,X1),X0)) & (v2_tops_1(k2_pre_topc(X0,X1),X0) | ~v3_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.99/1.48    inference(nnf_transformation,[],[f40])).
% 7.99/1.48  
% 7.99/1.48  fof(f74,plain,(
% 7.99/1.48    ( ! [X0,X1] : (v2_tops_1(k2_pre_topc(X0,X1),X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.99/1.48    inference(cnf_transformation,[],[f52])).
% 7.99/1.48  
% 7.99/1.48  fof(f82,plain,(
% 7.99/1.48    v3_tops_1(sK2,sK1)),
% 7.99/1.48    inference(cnf_transformation,[],[f56])).
% 7.99/1.48  
% 7.99/1.48  fof(f13,axiom,(
% 7.99/1.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.99/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.99/1.48  
% 7.99/1.48  fof(f36,plain,(
% 7.99/1.48    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.99/1.48    inference(ennf_transformation,[],[f13])).
% 7.99/1.48  
% 7.99/1.48  fof(f37,plain,(
% 7.99/1.48    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.99/1.48    inference(flattening,[],[f36])).
% 7.99/1.48  
% 7.99/1.48  fof(f70,plain,(
% 7.99/1.48    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.99/1.48    inference(cnf_transformation,[],[f37])).
% 7.99/1.48  
% 7.99/1.48  fof(f18,axiom,(
% 7.99/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 7.99/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.99/1.48  
% 7.99/1.48  fof(f42,plain,(
% 7.99/1.48    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.99/1.48    inference(ennf_transformation,[],[f18])).
% 7.99/1.48  
% 7.99/1.48  fof(f43,plain,(
% 7.99/1.48    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.99/1.48    inference(flattening,[],[f42])).
% 7.99/1.48  
% 7.99/1.48  fof(f77,plain,(
% 7.99/1.48    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.99/1.48    inference(cnf_transformation,[],[f43])).
% 7.99/1.48  
% 7.99/1.48  fof(f14,axiom,(
% 7.99/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 7.99/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.99/1.48  
% 7.99/1.48  fof(f38,plain,(
% 7.99/1.48    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.99/1.48    inference(ennf_transformation,[],[f14])).
% 7.99/1.48  
% 7.99/1.48  fof(f71,plain,(
% 7.99/1.48    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.99/1.48    inference(cnf_transformation,[],[f38])).
% 7.99/1.48  
% 7.99/1.48  fof(f11,axiom,(
% 7.99/1.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.99/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.99/1.48  
% 7.99/1.48  fof(f50,plain,(
% 7.99/1.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.99/1.48    inference(nnf_transformation,[],[f11])).
% 7.99/1.48  
% 7.99/1.48  fof(f69,plain,(
% 7.99/1.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.99/1.48    inference(cnf_transformation,[],[f50])).
% 7.99/1.48  
% 7.99/1.48  fof(f10,axiom,(
% 7.99/1.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.99/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.99/1.48  
% 7.99/1.48  fof(f67,plain,(
% 7.99/1.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.99/1.48    inference(cnf_transformation,[],[f10])).
% 7.99/1.48  
% 7.99/1.48  fof(f68,plain,(
% 7.99/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.99/1.48    inference(cnf_transformation,[],[f50])).
% 7.99/1.48  
% 7.99/1.48  fof(f5,axiom,(
% 7.99/1.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X2)) => r1_tarski(X2,k3_subset_1(X0,X1)))))),
% 7.99/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.99/1.48  
% 7.99/1.48  fof(f28,plain,(
% 7.99/1.48    ! [X0,X1] : (! [X2] : ((r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.99/1.48    inference(ennf_transformation,[],[f5])).
% 7.99/1.48  
% 7.99/1.48  fof(f29,plain,(
% 7.99/1.48    ! [X0,X1] : (! [X2] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.99/1.48    inference(flattening,[],[f28])).
% 7.99/1.48  
% 7.99/1.48  fof(f61,plain,(
% 7.99/1.48    ( ! [X2,X0,X1] : (r1_tarski(X2,k3_subset_1(X0,X1)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.99/1.48    inference(cnf_transformation,[],[f29])).
% 7.99/1.48  
% 7.99/1.48  fof(f6,axiom,(
% 7.99/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => ((r1_tarski(X1,k3_subset_1(X0,X2)) & r1_tarski(X1,X2)) => k1_xboole_0 = X1))),
% 7.99/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.99/1.48  
% 7.99/1.48  fof(f30,plain,(
% 7.99/1.48    ! [X0,X1,X2] : ((k1_xboole_0 = X1 | (~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.99/1.48    inference(ennf_transformation,[],[f6])).
% 7.99/1.48  
% 7.99/1.48  fof(f31,plain,(
% 7.99/1.48    ! [X0,X1,X2] : (k1_xboole_0 = X1 | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.99/1.48    inference(flattening,[],[f30])).
% 7.99/1.48  
% 7.99/1.48  fof(f62,plain,(
% 7.99/1.48    ( ! [X2,X0,X1] : (k1_xboole_0 = X1 | ~r1_tarski(X1,k3_subset_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.99/1.48    inference(cnf_transformation,[],[f31])).
% 7.99/1.48  
% 7.99/1.48  fof(f79,plain,(
% 7.99/1.48    ( ! [X0,X1] : (v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.99/1.48    inference(cnf_transformation,[],[f53])).
% 7.99/1.48  
% 7.99/1.48  fof(f15,axiom,(
% 7.99/1.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 7.99/1.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.99/1.48  
% 7.99/1.48  fof(f39,plain,(
% 7.99/1.48    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.99/1.48    inference(ennf_transformation,[],[f15])).
% 7.99/1.48  
% 7.99/1.48  fof(f51,plain,(
% 7.99/1.48    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.99/1.48    inference(nnf_transformation,[],[f39])).
% 7.99/1.48  
% 7.99/1.48  fof(f72,plain,(
% 7.99/1.48    ( ! [X0,X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.99/1.48    inference(cnf_transformation,[],[f51])).
% 7.99/1.48  
% 7.99/1.48  fof(f83,plain,(
% 7.99/1.48    ~v1_tops_1(k3_subset_1(u1_struct_0(sK1),sK2),sK1)),
% 7.99/1.48    inference(cnf_transformation,[],[f56])).
% 7.99/1.48  
% 7.99/1.48  cnf(c_25,negated_conjecture,
% 7.99/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.99/1.48      inference(cnf_transformation,[],[f81]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_1365,plain,
% 7.99/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 7.99/1.48      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_22,plain,
% 7.99/1.48      ( ~ v2_tops_1(X0,X1)
% 7.99/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.99/1.48      | ~ l1_pre_topc(X1)
% 7.99/1.48      | k1_tops_1(X1,X0) = k1_xboole_0 ),
% 7.99/1.48      inference(cnf_transformation,[],[f78]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_26,negated_conjecture,
% 7.99/1.48      ( l1_pre_topc(sK1) ),
% 7.99/1.48      inference(cnf_transformation,[],[f80]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_485,plain,
% 7.99/1.48      ( ~ v2_tops_1(X0,X1)
% 7.99/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.99/1.48      | k1_tops_1(X1,X0) = k1_xboole_0
% 7.99/1.48      | sK1 != X1 ),
% 7.99/1.48      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_486,plain,
% 7.99/1.48      ( ~ v2_tops_1(X0,sK1)
% 7.99/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.99/1.48      | k1_tops_1(sK1,X0) = k1_xboole_0 ),
% 7.99/1.48      inference(unflattening,[status(thm)],[c_485]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_18,plain,
% 7.99/1.48      ( ~ v3_tops_1(X0,X1)
% 7.99/1.48      | v2_tops_1(k2_pre_topc(X1,X0),X1)
% 7.99/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.99/1.48      | ~ l1_pre_topc(X1) ),
% 7.99/1.48      inference(cnf_transformation,[],[f74]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_24,negated_conjecture,
% 7.99/1.48      ( v3_tops_1(sK2,sK1) ),
% 7.99/1.48      inference(cnf_transformation,[],[f82]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_398,plain,
% 7.99/1.48      ( v2_tops_1(k2_pre_topc(X0,X1),X0)
% 7.99/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.99/1.48      | ~ l1_pre_topc(X0)
% 7.99/1.48      | sK2 != X1
% 7.99/1.48      | sK1 != X0 ),
% 7.99/1.48      inference(resolution_lifted,[status(thm)],[c_18,c_24]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_399,plain,
% 7.99/1.48      ( v2_tops_1(k2_pre_topc(sK1,sK2),sK1)
% 7.99/1.48      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.99/1.48      | ~ l1_pre_topc(sK1) ),
% 7.99/1.48      inference(unflattening,[status(thm)],[c_398]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_401,plain,
% 7.99/1.48      ( v2_tops_1(k2_pre_topc(sK1,sK2),sK1) ),
% 7.99/1.48      inference(global_propositional_subsumption,
% 7.99/1.48                [status(thm)],
% 7.99/1.48                [c_399,c_26,c_25]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_594,plain,
% 7.99/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.99/1.48      | k1_tops_1(sK1,X0) = k1_xboole_0
% 7.99/1.48      | k2_pre_topc(sK1,sK2) != X0
% 7.99/1.48      | sK1 != sK1 ),
% 7.99/1.48      inference(resolution_lifted,[status(thm)],[c_486,c_401]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_595,plain,
% 7.99/1.48      ( ~ m1_subset_1(k2_pre_topc(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.99/1.48      | k1_tops_1(sK1,k2_pre_topc(sK1,sK2)) = k1_xboole_0 ),
% 7.99/1.48      inference(unflattening,[status(thm)],[c_594]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_1355,plain,
% 7.99/1.48      ( k1_tops_1(sK1,k2_pre_topc(sK1,sK2)) = k1_xboole_0
% 7.99/1.48      | m1_subset_1(k2_pre_topc(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 7.99/1.48      inference(predicate_to_equality,[status(thm)],[c_595]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_13,plain,
% 7.99/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.99/1.48      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.99/1.48      | ~ l1_pre_topc(X1) ),
% 7.99/1.48      inference(cnf_transformation,[],[f70]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_527,plain,
% 7.99/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.99/1.48      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.99/1.48      | sK1 != X1 ),
% 7.99/1.48      inference(resolution_lifted,[status(thm)],[c_13,c_26]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_528,plain,
% 7.99/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.99/1.48      | m1_subset_1(k2_pre_topc(sK1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.99/1.48      inference(unflattening,[status(thm)],[c_527]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_1531,plain,
% 7.99/1.48      ( m1_subset_1(k2_pre_topc(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 7.99/1.48      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.99/1.48      inference(instantiation,[status(thm)],[c_528]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_1852,plain,
% 7.99/1.48      ( k1_tops_1(sK1,k2_pre_topc(sK1,sK2)) = k1_xboole_0 ),
% 7.99/1.48      inference(global_propositional_subsumption,
% 7.99/1.48                [status(thm)],
% 7.99/1.48                [c_1355,c_25,c_595,c_1531]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_20,plain,
% 7.99/1.48      ( ~ r1_tarski(X0,X1)
% 7.99/1.48      | r1_tarski(k1_tops_1(X2,X0),k1_tops_1(X2,X1))
% 7.99/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 7.99/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 7.99/1.48      | ~ l1_pre_topc(X2) ),
% 7.99/1.48      inference(cnf_transformation,[],[f77]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_539,plain,
% 7.99/1.48      ( ~ r1_tarski(X0,X1)
% 7.99/1.48      | r1_tarski(k1_tops_1(X2,X0),k1_tops_1(X2,X1))
% 7.99/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 7.99/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 7.99/1.48      | sK1 != X2 ),
% 7.99/1.48      inference(resolution_lifted,[status(thm)],[c_20,c_26]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_540,plain,
% 7.99/1.48      ( ~ r1_tarski(X0,X1)
% 7.99/1.48      | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1))
% 7.99/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.99/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.99/1.48      inference(unflattening,[status(thm)],[c_539]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_1357,plain,
% 7.99/1.48      ( r1_tarski(X0,X1) != iProver_top
% 7.99/1.48      | r1_tarski(k1_tops_1(sK1,X0),k1_tops_1(sK1,X1)) = iProver_top
% 7.99/1.48      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.99/1.48      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 7.99/1.48      inference(predicate_to_equality,[status(thm)],[c_540]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_1855,plain,
% 7.99/1.48      ( r1_tarski(X0,k2_pre_topc(sK1,sK2)) != iProver_top
% 7.99/1.48      | r1_tarski(k1_tops_1(sK1,X0),k1_xboole_0) = iProver_top
% 7.99/1.48      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.99/1.48      | m1_subset_1(k2_pre_topc(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 7.99/1.48      inference(superposition,[status(thm)],[c_1852,c_1357]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_28,plain,
% 7.99/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 7.99/1.48      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_1532,plain,
% 7.99/1.48      ( m1_subset_1(k2_pre_topc(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 7.99/1.48      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 7.99/1.48      inference(predicate_to_equality,[status(thm)],[c_1531]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_4868,plain,
% 7.99/1.48      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 7.99/1.48      | r1_tarski(k1_tops_1(sK1,X0),k1_xboole_0) = iProver_top
% 7.99/1.48      | r1_tarski(X0,k2_pre_topc(sK1,sK2)) != iProver_top ),
% 7.99/1.48      inference(global_propositional_subsumption,
% 7.99/1.48                [status(thm)],
% 7.99/1.48                [c_1855,c_28,c_1532]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_4869,plain,
% 7.99/1.48      ( r1_tarski(X0,k2_pre_topc(sK1,sK2)) != iProver_top
% 7.99/1.48      | r1_tarski(k1_tops_1(sK1,X0),k1_xboole_0) = iProver_top
% 7.99/1.48      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 7.99/1.48      inference(renaming,[status(thm)],[c_4868]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_4880,plain,
% 7.99/1.48      ( r1_tarski(k1_tops_1(sK1,sK2),k1_xboole_0) = iProver_top
% 7.99/1.48      | r1_tarski(sK2,k2_pre_topc(sK1,sK2)) != iProver_top ),
% 7.99/1.48      inference(superposition,[status(thm)],[c_1365,c_4869]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_14,plain,
% 7.99/1.48      ( r1_tarski(X0,k2_pre_topc(X1,X0))
% 7.99/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.99/1.48      | ~ l1_pre_topc(X1) ),
% 7.99/1.48      inference(cnf_transformation,[],[f71]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_515,plain,
% 7.99/1.48      ( r1_tarski(X0,k2_pre_topc(X1,X0))
% 7.99/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.99/1.48      | sK1 != X1 ),
% 7.99/1.48      inference(resolution_lifted,[status(thm)],[c_14,c_26]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_516,plain,
% 7.99/1.48      ( r1_tarski(X0,k2_pre_topc(sK1,X0))
% 7.99/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.99/1.48      inference(unflattening,[status(thm)],[c_515]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_1537,plain,
% 7.99/1.48      ( r1_tarski(sK2,k2_pre_topc(sK1,sK2))
% 7.99/1.48      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 7.99/1.48      inference(instantiation,[status(thm)],[c_516]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_1538,plain,
% 7.99/1.48      ( r1_tarski(sK2,k2_pre_topc(sK1,sK2)) = iProver_top
% 7.99/1.48      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 7.99/1.48      inference(predicate_to_equality,[status(thm)],[c_1537]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_4911,plain,
% 7.99/1.48      ( r1_tarski(k1_tops_1(sK1,sK2),k1_xboole_0) = iProver_top ),
% 7.99/1.48      inference(global_propositional_subsumption,
% 7.99/1.48                [status(thm)],
% 7.99/1.48                [c_4880,c_28,c_1538]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_11,plain,
% 7.99/1.48      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.99/1.48      inference(cnf_transformation,[],[f69]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_1367,plain,
% 7.99/1.48      ( r1_tarski(X0,X1) != iProver_top
% 7.99/1.48      | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 7.99/1.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_10,plain,
% 7.99/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.99/1.48      inference(cnf_transformation,[],[f67]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_1368,plain,
% 7.99/1.48      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.99/1.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_12,plain,
% 7.99/1.48      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.99/1.48      inference(cnf_transformation,[],[f68]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_1366,plain,
% 7.99/1.48      ( r1_tarski(X0,X1) = iProver_top
% 7.99/1.48      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 7.99/1.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_2429,plain,
% 7.99/1.48      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.99/1.48      inference(superposition,[status(thm)],[c_1368,c_1366]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_4,plain,
% 7.99/1.48      ( ~ r1_tarski(X0,k3_subset_1(X1,X2))
% 7.99/1.48      | r1_tarski(X2,k3_subset_1(X1,X0))
% 7.99/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.99/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
% 7.99/1.48      inference(cnf_transformation,[],[f61]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_212,plain,
% 7.99/1.48      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.99/1.48      inference(prop_impl,[status(thm)],[c_11]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_271,plain,
% 7.99/1.48      ( ~ r1_tarski(X0,X1)
% 7.99/1.48      | ~ r1_tarski(X0,k3_subset_1(X1,X2))
% 7.99/1.48      | r1_tarski(X2,k3_subset_1(X1,X0))
% 7.99/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
% 7.99/1.48      inference(bin_hyper_res,[status(thm)],[c_4,c_212]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_1361,plain,
% 7.99/1.48      ( r1_tarski(X0,X1) != iProver_top
% 7.99/1.48      | r1_tarski(X0,k3_subset_1(X1,X2)) != iProver_top
% 7.99/1.48      | r1_tarski(X2,k3_subset_1(X1,X0)) = iProver_top
% 7.99/1.48      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top ),
% 7.99/1.48      inference(predicate_to_equality,[status(thm)],[c_271]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_6247,plain,
% 7.99/1.48      ( r1_tarski(X0,k3_subset_1(X1,k1_xboole_0)) = iProver_top
% 7.99/1.48      | r1_tarski(k1_xboole_0,X1) != iProver_top
% 7.99/1.48      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 7.99/1.48      inference(superposition,[status(thm)],[c_2429,c_1361]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_6259,plain,
% 7.99/1.48      ( r1_tarski(X0,k3_subset_1(X1,k1_xboole_0)) = iProver_top
% 7.99/1.48      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 7.99/1.48      inference(forward_subsumption_resolution,
% 7.99/1.48                [status(thm)],
% 7.99/1.48                [c_6247,c_2429]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_5,plain,
% 7.99/1.48      ( ~ r1_tarski(X0,X1)
% 7.99/1.48      | ~ r1_tarski(X0,k3_subset_1(X2,X1))
% 7.99/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 7.99/1.48      | k1_xboole_0 = X0 ),
% 7.99/1.48      inference(cnf_transformation,[],[f62]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_1373,plain,
% 7.99/1.48      ( k1_xboole_0 = X0
% 7.99/1.48      | r1_tarski(X0,X1) != iProver_top
% 7.99/1.48      | r1_tarski(X0,k3_subset_1(X2,X1)) != iProver_top
% 7.99/1.48      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 7.99/1.48      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_30483,plain,
% 7.99/1.48      ( k1_xboole_0 = X0
% 7.99/1.48      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 7.99/1.48      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.99/1.48      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top ),
% 7.99/1.48      inference(superposition,[status(thm)],[c_6259,c_1373]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_31333,plain,
% 7.99/1.48      ( k1_xboole_0 = X0
% 7.99/1.48      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 7.99/1.48      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 7.99/1.48      inference(forward_subsumption_resolution,
% 7.99/1.48                [status(thm)],
% 7.99/1.48                [c_30483,c_1368]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_31337,plain,
% 7.99/1.48      ( k1_xboole_0 = X0
% 7.99/1.48      | r1_tarski(X0,X1) != iProver_top
% 7.99/1.48      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.99/1.48      inference(superposition,[status(thm)],[c_1367,c_31333]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_31398,plain,
% 7.99/1.48      ( k1_tops_1(sK1,sK2) = k1_xboole_0
% 7.99/1.48      | r1_tarski(k1_tops_1(sK1,sK2),k1_xboole_0) != iProver_top ),
% 7.99/1.48      inference(superposition,[status(thm)],[c_4911,c_31337]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_21,plain,
% 7.99/1.48      ( v2_tops_1(X0,X1)
% 7.99/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.99/1.48      | ~ l1_pre_topc(X1)
% 7.99/1.48      | k1_tops_1(X1,X0) != k1_xboole_0 ),
% 7.99/1.48      inference(cnf_transformation,[],[f79]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_500,plain,
% 7.99/1.48      ( v2_tops_1(X0,X1)
% 7.99/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.99/1.48      | k1_tops_1(X1,X0) != k1_xboole_0
% 7.99/1.48      | sK1 != X1 ),
% 7.99/1.48      inference(resolution_lifted,[status(thm)],[c_21,c_26]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_501,plain,
% 7.99/1.48      ( v2_tops_1(X0,sK1)
% 7.99/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.99/1.48      | k1_tops_1(sK1,X0) != k1_xboole_0 ),
% 7.99/1.48      inference(unflattening,[status(thm)],[c_500]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_16,plain,
% 7.99/1.48      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
% 7.99/1.48      | ~ v2_tops_1(X1,X0)
% 7.99/1.48      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 7.99/1.48      | ~ l1_pre_topc(X0) ),
% 7.99/1.48      inference(cnf_transformation,[],[f72]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_23,negated_conjecture,
% 7.99/1.48      ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK1),sK2),sK1) ),
% 7.99/1.48      inference(cnf_transformation,[],[f83]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_372,plain,
% 7.99/1.48      ( ~ v2_tops_1(X0,X1)
% 7.99/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.99/1.48      | ~ l1_pre_topc(X1)
% 7.99/1.48      | k3_subset_1(u1_struct_0(X1),X0) != k3_subset_1(u1_struct_0(sK1),sK2)
% 7.99/1.48      | sK1 != X1 ),
% 7.99/1.48      inference(resolution_lifted,[status(thm)],[c_16,c_23]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_373,plain,
% 7.99/1.48      ( ~ v2_tops_1(X0,sK1)
% 7.99/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.99/1.48      | ~ l1_pre_topc(sK1)
% 7.99/1.48      | k3_subset_1(u1_struct_0(sK1),X0) != k3_subset_1(u1_struct_0(sK1),sK2) ),
% 7.99/1.48      inference(unflattening,[status(thm)],[c_372]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_377,plain,
% 7.99/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.99/1.48      | ~ v2_tops_1(X0,sK1)
% 7.99/1.48      | k3_subset_1(u1_struct_0(sK1),X0) != k3_subset_1(u1_struct_0(sK1),sK2) ),
% 7.99/1.48      inference(global_propositional_subsumption,
% 7.99/1.48                [status(thm)],
% 7.99/1.48                [c_373,c_26]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_378,plain,
% 7.99/1.48      ( ~ v2_tops_1(X0,sK1)
% 7.99/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.99/1.48      | k3_subset_1(u1_struct_0(sK1),X0) != k3_subset_1(u1_struct_0(sK1),sK2) ),
% 7.99/1.48      inference(renaming,[status(thm)],[c_377]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_580,plain,
% 7.99/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 7.99/1.48      | k1_tops_1(sK1,X0) != k1_xboole_0
% 7.99/1.48      | k3_subset_1(u1_struct_0(sK1),X0) != k3_subset_1(u1_struct_0(sK1),sK2) ),
% 7.99/1.48      inference(resolution,[status(thm)],[c_501,c_378]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_1356,plain,
% 7.99/1.48      ( k1_tops_1(sK1,X0) != k1_xboole_0
% 7.99/1.48      | k3_subset_1(u1_struct_0(sK1),X0) != k3_subset_1(u1_struct_0(sK1),sK2)
% 7.99/1.48      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 7.99/1.48      inference(predicate_to_equality,[status(thm)],[c_580]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(c_3743,plain,
% 7.99/1.48      ( k1_tops_1(sK1,sK2) != k1_xboole_0
% 7.99/1.48      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 7.99/1.48      inference(equality_resolution,[status(thm)],[c_1356]) ).
% 7.99/1.48  
% 7.99/1.48  cnf(contradiction,plain,
% 7.99/1.48      ( $false ),
% 7.99/1.48      inference(minisat,[status(thm)],[c_31398,c_4880,c_3743,c_1538,c_28]) ).
% 7.99/1.48  
% 7.99/1.48  
% 7.99/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.99/1.48  
% 7.99/1.48  ------                               Statistics
% 7.99/1.48  
% 7.99/1.48  ------ General
% 7.99/1.48  
% 7.99/1.48  abstr_ref_over_cycles:                  0
% 7.99/1.48  abstr_ref_under_cycles:                 0
% 7.99/1.48  gc_basic_clause_elim:                   0
% 7.99/1.48  forced_gc_time:                         0
% 7.99/1.48  parsing_time:                           0.01
% 7.99/1.48  unif_index_cands_time:                  0.
% 7.99/1.48  unif_index_add_time:                    0.
% 7.99/1.48  orderings_time:                         0.
% 7.99/1.48  out_proof_time:                         0.012
% 7.99/1.48  total_time:                             0.799
% 7.99/1.48  num_of_symbols:                         48
% 7.99/1.48  num_of_terms:                           29433
% 7.99/1.48  
% 7.99/1.48  ------ Preprocessing
% 7.99/1.48  
% 7.99/1.48  num_of_splits:                          0
% 7.99/1.48  num_of_split_atoms:                     0
% 7.99/1.48  num_of_reused_defs:                     0
% 7.99/1.48  num_eq_ax_congr_red:                    23
% 7.99/1.48  num_of_sem_filtered_clauses:            1
% 7.99/1.48  num_of_subtypes:                        0
% 7.99/1.48  monotx_restored_types:                  0
% 7.99/1.48  sat_num_of_epr_types:                   0
% 7.99/1.48  sat_num_of_non_cyclic_types:            0
% 7.99/1.48  sat_guarded_non_collapsed_types:        0
% 7.99/1.48  num_pure_diseq_elim:                    0
% 7.99/1.48  simp_replaced_by:                       0
% 7.99/1.48  res_preprocessed:                       109
% 7.99/1.48  prep_upred:                             0
% 7.99/1.48  prep_unflattend:                        11
% 7.99/1.48  smt_new_axioms:                         0
% 7.99/1.48  pred_elim_cands:                        3
% 7.99/1.48  pred_elim:                              4
% 7.99/1.48  pred_elim_cl:                           6
% 7.99/1.48  pred_elim_cycles:                       7
% 7.99/1.48  merged_defs:                            8
% 7.99/1.48  merged_defs_ncl:                        0
% 7.99/1.48  bin_hyper_res:                          12
% 7.99/1.48  prep_cycles:                            4
% 7.99/1.48  pred_elim_time:                         0.007
% 7.99/1.48  splitting_time:                         0.
% 7.99/1.48  sem_filter_time:                        0.
% 7.99/1.48  monotx_time:                            0.001
% 7.99/1.48  subtype_inf_time:                       0.
% 7.99/1.48  
% 7.99/1.48  ------ Problem properties
% 7.99/1.48  
% 7.99/1.48  clauses:                                21
% 7.99/1.48  conjectures:                            1
% 7.99/1.48  epr:                                    0
% 7.99/1.48  horn:                                   21
% 7.99/1.48  ground:                                 3
% 7.99/1.48  unary:                                  3
% 7.99/1.48  binary:                                 9
% 7.99/1.48  lits:                                   56
% 7.99/1.48  lits_eq:                                7
% 7.99/1.48  fd_pure:                                0
% 7.99/1.48  fd_pseudo:                              0
% 7.99/1.48  fd_cond:                                1
% 7.99/1.48  fd_pseudo_cond:                         0
% 7.99/1.48  ac_symbols:                             0
% 7.99/1.48  
% 7.99/1.48  ------ Propositional Solver
% 7.99/1.48  
% 7.99/1.48  prop_solver_calls:                      33
% 7.99/1.48  prop_fast_solver_calls:                 1657
% 7.99/1.48  smt_solver_calls:                       0
% 7.99/1.48  smt_fast_solver_calls:                  0
% 7.99/1.48  prop_num_of_clauses:                    11152
% 7.99/1.48  prop_preprocess_simplified:             19040
% 7.99/1.48  prop_fo_subsumed:                       64
% 7.99/1.48  prop_solver_time:                       0.
% 7.99/1.48  smt_solver_time:                        0.
% 7.99/1.48  smt_fast_solver_time:                   0.
% 7.99/1.48  prop_fast_solver_time:                  0.
% 7.99/1.48  prop_unsat_core_time:                   0.001
% 7.99/1.48  
% 7.99/1.48  ------ QBF
% 7.99/1.48  
% 7.99/1.48  qbf_q_res:                              0
% 7.99/1.48  qbf_num_tautologies:                    0
% 7.99/1.48  qbf_prep_cycles:                        0
% 7.99/1.48  
% 7.99/1.48  ------ BMC1
% 7.99/1.48  
% 7.99/1.48  bmc1_current_bound:                     -1
% 7.99/1.48  bmc1_last_solved_bound:                 -1
% 7.99/1.48  bmc1_unsat_core_size:                   -1
% 7.99/1.48  bmc1_unsat_core_parents_size:           -1
% 7.99/1.48  bmc1_merge_next_fun:                    0
% 7.99/1.48  bmc1_unsat_core_clauses_time:           0.
% 7.99/1.48  
% 7.99/1.48  ------ Instantiation
% 7.99/1.48  
% 7.99/1.48  inst_num_of_clauses:                    3104
% 7.99/1.48  inst_num_in_passive:                    1102
% 7.99/1.48  inst_num_in_active:                     1274
% 7.99/1.48  inst_num_in_unprocessed:                728
% 7.99/1.48  inst_num_of_loops:                      1350
% 7.99/1.48  inst_num_of_learning_restarts:          0
% 7.99/1.48  inst_num_moves_active_passive:          75
% 7.99/1.48  inst_lit_activity:                      0
% 7.99/1.48  inst_lit_activity_moves:                3
% 7.99/1.48  inst_num_tautologies:                   0
% 7.99/1.48  inst_num_prop_implied:                  0
% 7.99/1.48  inst_num_existing_simplified:           0
% 7.99/1.48  inst_num_eq_res_simplified:             0
% 7.99/1.48  inst_num_child_elim:                    0
% 7.99/1.48  inst_num_of_dismatching_blockings:      4953
% 7.99/1.48  inst_num_of_non_proper_insts:           3138
% 7.99/1.48  inst_num_of_duplicates:                 0
% 7.99/1.48  inst_inst_num_from_inst_to_res:         0
% 7.99/1.48  inst_dismatching_checking_time:         0.
% 7.99/1.48  
% 7.99/1.48  ------ Resolution
% 7.99/1.48  
% 7.99/1.48  res_num_of_clauses:                     0
% 7.99/1.48  res_num_in_passive:                     0
% 7.99/1.48  res_num_in_active:                      0
% 7.99/1.48  res_num_of_loops:                       113
% 7.99/1.48  res_forward_subset_subsumed:            28
% 7.99/1.48  res_backward_subset_subsumed:           0
% 7.99/1.48  res_forward_subsumed:                   0
% 7.99/1.48  res_backward_subsumed:                  0
% 7.99/1.48  res_forward_subsumption_resolution:     0
% 7.99/1.48  res_backward_subsumption_resolution:    0
% 7.99/1.48  res_clause_to_clause_subsumption:       3757
% 7.99/1.48  res_orphan_elimination:                 0
% 7.99/1.48  res_tautology_del:                      48
% 7.99/1.48  res_num_eq_res_simplified:              0
% 7.99/1.48  res_num_sel_changes:                    0
% 7.99/1.48  res_moves_from_active_to_pass:          0
% 7.99/1.48  
% 7.99/1.48  ------ Superposition
% 7.99/1.48  
% 7.99/1.48  sup_time_total:                         0.
% 7.99/1.48  sup_time_generating:                    0.
% 7.99/1.48  sup_time_sim_full:                      0.
% 7.99/1.48  sup_time_sim_immed:                     0.
% 7.99/1.48  
% 7.99/1.48  sup_num_of_clauses:                     731
% 7.99/1.48  sup_num_in_active:                      266
% 7.99/1.48  sup_num_in_passive:                     465
% 7.99/1.48  sup_num_of_loops:                       269
% 7.99/1.48  sup_fw_superposition:                   747
% 7.99/1.48  sup_bw_superposition:                   284
% 7.99/1.48  sup_immediate_simplified:               228
% 7.99/1.48  sup_given_eliminated:                   0
% 7.99/1.48  comparisons_done:                       0
% 7.99/1.48  comparisons_avoided:                    0
% 7.99/1.48  
% 7.99/1.48  ------ Simplifications
% 7.99/1.48  
% 7.99/1.48  
% 7.99/1.48  sim_fw_subset_subsumed:                 61
% 7.99/1.48  sim_bw_subset_subsumed:                 12
% 7.99/1.48  sim_fw_subsumed:                        106
% 7.99/1.48  sim_bw_subsumed:                        4
% 7.99/1.48  sim_fw_subsumption_res:                 9
% 7.99/1.48  sim_bw_subsumption_res:                 0
% 7.99/1.48  sim_tautology_del:                      13
% 7.99/1.48  sim_eq_tautology_del:                   10
% 7.99/1.48  sim_eq_res_simp:                        0
% 7.99/1.48  sim_fw_demodulated:                     0
% 7.99/1.48  sim_bw_demodulated:                     0
% 7.99/1.48  sim_light_normalised:                   83
% 7.99/1.48  sim_joinable_taut:                      0
% 7.99/1.48  sim_joinable_simp:                      0
% 7.99/1.48  sim_ac_normalised:                      0
% 7.99/1.48  sim_smt_subsumption:                    0
% 7.99/1.48  
%------------------------------------------------------------------------------
