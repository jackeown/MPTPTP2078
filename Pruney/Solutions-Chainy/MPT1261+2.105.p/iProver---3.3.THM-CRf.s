%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:39 EST 2020

% Result     : Theorem 7.12s
% Output     : CNFRefutation 7.12s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 680 expanded)
%              Number of clauses        :   80 ( 243 expanded)
%              Number of leaves         :   13 ( 132 expanded)
%              Depth                    :   24
%              Number of atoms          :  353 (2831 expanded)
%              Number of equality atoms :  154 ( 856 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1)
          | ~ v4_pre_topc(sK1,X0) )
        & ( k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1)
          | v4_pre_topc(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
              | ~ v4_pre_topc(X1,X0) )
            & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1)
            | ~ v4_pre_topc(X1,sK0) )
          & ( k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1)
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f33,f32])).

fof(f53,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f51,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f36])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f16])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f54,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_16,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_154,plain,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_16])).

cnf(c_11,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_339,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_340,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_339])).

cnf(c_386,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,X0) = X0
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_154,c_340])).

cnf(c_387,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_389,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_387,c_17])).

cnf(c_487,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_389])).

cnf(c_488,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(renaming,[status(thm)],[c_487])).

cnf(c_917,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_918,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1291,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_917,c_918])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_150,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_151,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_150])).

cnf(c_191,plain,
    ( ~ r1_tarski(X0,X1)
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_151])).

cnf(c_915,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_191])).

cnf(c_1930,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_1291,c_915])).

cnf(c_1939,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_488,c_1930])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_921,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_189,plain,
    ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
    | ~ r1_tarski(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_151])).

cnf(c_916,plain,
    ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_189])).

cnf(c_2186,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k7_subset_1(X1,X0,X2),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_916,c_918])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | k2_xboole_0(X0,X1) = X1 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_920,plain,
    ( k2_xboole_0(X0,X1) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2675,plain,
    ( k2_xboole_0(k7_subset_1(X0,X1,X2),X0) = X0
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2186,c_920])).

cnf(c_3541,plain,
    ( k2_xboole_0(k7_subset_1(X0,X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_921,c_2675])).

cnf(c_1929,plain,
    ( k7_subset_1(X0,X0,X1) = k4_xboole_0(X0,X1) ),
    inference(superposition,[status(thm)],[c_921,c_915])).

cnf(c_3559,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(light_normalisation,[status(thm)],[c_3541,c_1929])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_5469,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_3559,c_0])).

cnf(c_5591,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_1939,c_5469])).

cnf(c_2181,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_488,c_916])).

cnf(c_22,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1110,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1180,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(instantiation,[status(thm)],[c_1110])).

cnf(c_1181,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1180])).

cnf(c_2524,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2181,c_22,c_1181])).

cnf(c_2525,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_2524])).

cnf(c_2530,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2525,c_918])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_190,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_151])).

cnf(c_483,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_484,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_483])).

cnf(c_515,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_190,c_484])).

cnf(c_911,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_515])).

cnf(c_20085,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1291,c_911])).

cnf(c_20519,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_2530,c_20085])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_315,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_18])).

cnf(c_316,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_315])).

cnf(c_914,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_316])).

cnf(c_1036,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_917,c_914])).

cnf(c_20547,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_20519,c_1036])).

cnf(c_20754,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_5591,c_20547])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_327,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_18])).

cnf(c_328,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_913,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_328])).

cnf(c_1052,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_917,c_913])).

cnf(c_20804,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_20754,c_1052])).

cnf(c_15,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_152,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_15])).

cnf(c_10,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_19,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_287,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_19])).

cnf(c_288,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_287])).

cnf(c_292,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(X0,sK0)
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_288,c_18])).

cnf(c_293,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(renaming,[status(thm)],[c_292])).

cnf(c_397,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,X0) != X0
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_152,c_293])).

cnf(c_398,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_400,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_398,c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20804,c_20754,c_400])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:04:44 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 7.12/1.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.12/1.51  
% 7.12/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.12/1.51  
% 7.12/1.51  ------  iProver source info
% 7.12/1.51  
% 7.12/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.12/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.12/1.51  git: non_committed_changes: false
% 7.12/1.51  git: last_make_outside_of_git: false
% 7.12/1.51  
% 7.12/1.51  ------ 
% 7.12/1.51  
% 7.12/1.51  ------ Input Options
% 7.12/1.51  
% 7.12/1.51  --out_options                           all
% 7.12/1.51  --tptp_safe_out                         true
% 7.12/1.51  --problem_path                          ""
% 7.12/1.51  --include_path                          ""
% 7.12/1.51  --clausifier                            res/vclausify_rel
% 7.12/1.51  --clausifier_options                    --mode clausify
% 7.12/1.51  --stdin                                 false
% 7.12/1.51  --stats_out                             all
% 7.12/1.51  
% 7.12/1.51  ------ General Options
% 7.12/1.51  
% 7.12/1.51  --fof                                   false
% 7.12/1.51  --time_out_real                         305.
% 7.12/1.51  --time_out_virtual                      -1.
% 7.12/1.51  --symbol_type_check                     false
% 7.12/1.51  --clausify_out                          false
% 7.12/1.51  --sig_cnt_out                           false
% 7.12/1.51  --trig_cnt_out                          false
% 7.12/1.51  --trig_cnt_out_tolerance                1.
% 7.12/1.51  --trig_cnt_out_sk_spl                   false
% 7.12/1.51  --abstr_cl_out                          false
% 7.12/1.51  
% 7.12/1.51  ------ Global Options
% 7.12/1.51  
% 7.12/1.51  --schedule                              default
% 7.12/1.51  --add_important_lit                     false
% 7.12/1.51  --prop_solver_per_cl                    1000
% 7.12/1.51  --min_unsat_core                        false
% 7.12/1.51  --soft_assumptions                      false
% 7.12/1.51  --soft_lemma_size                       3
% 7.12/1.51  --prop_impl_unit_size                   0
% 7.12/1.51  --prop_impl_unit                        []
% 7.12/1.51  --share_sel_clauses                     true
% 7.12/1.51  --reset_solvers                         false
% 7.12/1.51  --bc_imp_inh                            [conj_cone]
% 7.12/1.51  --conj_cone_tolerance                   3.
% 7.12/1.51  --extra_neg_conj                        none
% 7.12/1.51  --large_theory_mode                     true
% 7.12/1.51  --prolific_symb_bound                   200
% 7.12/1.51  --lt_threshold                          2000
% 7.12/1.51  --clause_weak_htbl                      true
% 7.12/1.51  --gc_record_bc_elim                     false
% 7.12/1.51  
% 7.12/1.51  ------ Preprocessing Options
% 7.12/1.51  
% 7.12/1.51  --preprocessing_flag                    true
% 7.12/1.51  --time_out_prep_mult                    0.1
% 7.12/1.51  --splitting_mode                        input
% 7.12/1.51  --splitting_grd                         true
% 7.12/1.51  --splitting_cvd                         false
% 7.12/1.51  --splitting_cvd_svl                     false
% 7.12/1.51  --splitting_nvd                         32
% 7.12/1.51  --sub_typing                            true
% 7.12/1.51  --prep_gs_sim                           true
% 7.12/1.51  --prep_unflatten                        true
% 7.12/1.51  --prep_res_sim                          true
% 7.12/1.51  --prep_upred                            true
% 7.12/1.51  --prep_sem_filter                       exhaustive
% 7.12/1.51  --prep_sem_filter_out                   false
% 7.12/1.51  --pred_elim                             true
% 7.12/1.51  --res_sim_input                         true
% 7.12/1.51  --eq_ax_congr_red                       true
% 7.12/1.51  --pure_diseq_elim                       true
% 7.12/1.51  --brand_transform                       false
% 7.12/1.51  --non_eq_to_eq                          false
% 7.12/1.51  --prep_def_merge                        true
% 7.12/1.51  --prep_def_merge_prop_impl              false
% 7.12/1.51  --prep_def_merge_mbd                    true
% 7.12/1.51  --prep_def_merge_tr_red                 false
% 7.12/1.51  --prep_def_merge_tr_cl                  false
% 7.12/1.51  --smt_preprocessing                     true
% 7.12/1.51  --smt_ac_axioms                         fast
% 7.12/1.51  --preprocessed_out                      false
% 7.12/1.51  --preprocessed_stats                    false
% 7.12/1.51  
% 7.12/1.51  ------ Abstraction refinement Options
% 7.12/1.51  
% 7.12/1.51  --abstr_ref                             []
% 7.12/1.51  --abstr_ref_prep                        false
% 7.12/1.51  --abstr_ref_until_sat                   false
% 7.12/1.51  --abstr_ref_sig_restrict                funpre
% 7.12/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.12/1.51  --abstr_ref_under                       []
% 7.12/1.51  
% 7.12/1.51  ------ SAT Options
% 7.12/1.51  
% 7.12/1.51  --sat_mode                              false
% 7.12/1.51  --sat_fm_restart_options                ""
% 7.12/1.51  --sat_gr_def                            false
% 7.12/1.51  --sat_epr_types                         true
% 7.12/1.51  --sat_non_cyclic_types                  false
% 7.12/1.51  --sat_finite_models                     false
% 7.12/1.51  --sat_fm_lemmas                         false
% 7.12/1.51  --sat_fm_prep                           false
% 7.12/1.51  --sat_fm_uc_incr                        true
% 7.12/1.51  --sat_out_model                         small
% 7.12/1.51  --sat_out_clauses                       false
% 7.12/1.51  
% 7.12/1.51  ------ QBF Options
% 7.12/1.51  
% 7.12/1.51  --qbf_mode                              false
% 7.12/1.51  --qbf_elim_univ                         false
% 7.12/1.51  --qbf_dom_inst                          none
% 7.12/1.51  --qbf_dom_pre_inst                      false
% 7.12/1.51  --qbf_sk_in                             false
% 7.12/1.51  --qbf_pred_elim                         true
% 7.12/1.51  --qbf_split                             512
% 7.12/1.51  
% 7.12/1.51  ------ BMC1 Options
% 7.12/1.51  
% 7.12/1.51  --bmc1_incremental                      false
% 7.12/1.51  --bmc1_axioms                           reachable_all
% 7.12/1.51  --bmc1_min_bound                        0
% 7.12/1.51  --bmc1_max_bound                        -1
% 7.12/1.51  --bmc1_max_bound_default                -1
% 7.12/1.51  --bmc1_symbol_reachability              true
% 7.12/1.51  --bmc1_property_lemmas                  false
% 7.12/1.51  --bmc1_k_induction                      false
% 7.12/1.51  --bmc1_non_equiv_states                 false
% 7.12/1.51  --bmc1_deadlock                         false
% 7.12/1.51  --bmc1_ucm                              false
% 7.12/1.51  --bmc1_add_unsat_core                   none
% 7.12/1.51  --bmc1_unsat_core_children              false
% 7.12/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.12/1.51  --bmc1_out_stat                         full
% 7.12/1.51  --bmc1_ground_init                      false
% 7.12/1.51  --bmc1_pre_inst_next_state              false
% 7.12/1.51  --bmc1_pre_inst_state                   false
% 7.12/1.51  --bmc1_pre_inst_reach_state             false
% 7.12/1.51  --bmc1_out_unsat_core                   false
% 7.12/1.51  --bmc1_aig_witness_out                  false
% 7.12/1.51  --bmc1_verbose                          false
% 7.12/1.51  --bmc1_dump_clauses_tptp                false
% 7.12/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.12/1.51  --bmc1_dump_file                        -
% 7.12/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.12/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.12/1.51  --bmc1_ucm_extend_mode                  1
% 7.12/1.51  --bmc1_ucm_init_mode                    2
% 7.12/1.51  --bmc1_ucm_cone_mode                    none
% 7.12/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.12/1.51  --bmc1_ucm_relax_model                  4
% 7.12/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.12/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.12/1.51  --bmc1_ucm_layered_model                none
% 7.12/1.51  --bmc1_ucm_max_lemma_size               10
% 7.12/1.51  
% 7.12/1.51  ------ AIG Options
% 7.12/1.51  
% 7.12/1.51  --aig_mode                              false
% 7.12/1.51  
% 7.12/1.51  ------ Instantiation Options
% 7.12/1.51  
% 7.12/1.51  --instantiation_flag                    true
% 7.12/1.51  --inst_sos_flag                         false
% 7.12/1.51  --inst_sos_phase                        true
% 7.12/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.12/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.12/1.51  --inst_lit_sel_side                     num_symb
% 7.12/1.51  --inst_solver_per_active                1400
% 7.12/1.51  --inst_solver_calls_frac                1.
% 7.12/1.51  --inst_passive_queue_type               priority_queues
% 7.12/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.12/1.51  --inst_passive_queues_freq              [25;2]
% 7.12/1.51  --inst_dismatching                      true
% 7.12/1.51  --inst_eager_unprocessed_to_passive     true
% 7.12/1.51  --inst_prop_sim_given                   true
% 7.12/1.51  --inst_prop_sim_new                     false
% 7.12/1.51  --inst_subs_new                         false
% 7.12/1.51  --inst_eq_res_simp                      false
% 7.12/1.51  --inst_subs_given                       false
% 7.12/1.51  --inst_orphan_elimination               true
% 7.12/1.51  --inst_learning_loop_flag               true
% 7.12/1.51  --inst_learning_start                   3000
% 7.12/1.51  --inst_learning_factor                  2
% 7.12/1.51  --inst_start_prop_sim_after_learn       3
% 7.12/1.51  --inst_sel_renew                        solver
% 7.12/1.51  --inst_lit_activity_flag                true
% 7.12/1.51  --inst_restr_to_given                   false
% 7.12/1.51  --inst_activity_threshold               500
% 7.12/1.51  --inst_out_proof                        true
% 7.12/1.51  
% 7.12/1.51  ------ Resolution Options
% 7.12/1.51  
% 7.12/1.51  --resolution_flag                       true
% 7.12/1.51  --res_lit_sel                           adaptive
% 7.12/1.51  --res_lit_sel_side                      none
% 7.12/1.51  --res_ordering                          kbo
% 7.12/1.51  --res_to_prop_solver                    active
% 7.12/1.51  --res_prop_simpl_new                    false
% 7.12/1.51  --res_prop_simpl_given                  true
% 7.12/1.51  --res_passive_queue_type                priority_queues
% 7.12/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.12/1.51  --res_passive_queues_freq               [15;5]
% 7.12/1.51  --res_forward_subs                      full
% 7.12/1.51  --res_backward_subs                     full
% 7.12/1.51  --res_forward_subs_resolution           true
% 7.12/1.51  --res_backward_subs_resolution          true
% 7.12/1.51  --res_orphan_elimination                true
% 7.12/1.51  --res_time_limit                        2.
% 7.12/1.51  --res_out_proof                         true
% 7.12/1.51  
% 7.12/1.51  ------ Superposition Options
% 7.12/1.51  
% 7.12/1.51  --superposition_flag                    true
% 7.12/1.51  --sup_passive_queue_type                priority_queues
% 7.12/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.12/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.12/1.51  --demod_completeness_check              fast
% 7.12/1.51  --demod_use_ground                      true
% 7.12/1.51  --sup_to_prop_solver                    passive
% 7.12/1.51  --sup_prop_simpl_new                    true
% 7.12/1.51  --sup_prop_simpl_given                  true
% 7.12/1.51  --sup_fun_splitting                     false
% 7.12/1.51  --sup_smt_interval                      50000
% 7.12/1.51  
% 7.12/1.51  ------ Superposition Simplification Setup
% 7.12/1.51  
% 7.12/1.51  --sup_indices_passive                   []
% 7.12/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.12/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.12/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.12/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.12/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.12/1.51  --sup_full_bw                           [BwDemod]
% 7.12/1.51  --sup_immed_triv                        [TrivRules]
% 7.12/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.12/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.12/1.51  --sup_immed_bw_main                     []
% 7.12/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.12/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.12/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.12/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.12/1.51  
% 7.12/1.51  ------ Combination Options
% 7.12/1.51  
% 7.12/1.51  --comb_res_mult                         3
% 7.12/1.51  --comb_sup_mult                         2
% 7.12/1.51  --comb_inst_mult                        10
% 7.12/1.51  
% 7.12/1.51  ------ Debug Options
% 7.12/1.51  
% 7.12/1.51  --dbg_backtrace                         false
% 7.12/1.51  --dbg_dump_prop_clauses                 false
% 7.12/1.51  --dbg_dump_prop_clauses_file            -
% 7.12/1.51  --dbg_out_stat                          false
% 7.12/1.51  ------ Parsing...
% 7.12/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.12/1.51  
% 7.12/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.12/1.51  
% 7.12/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.12/1.51  
% 7.12/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.12/1.51  ------ Proving...
% 7.12/1.51  ------ Problem Properties 
% 7.12/1.51  
% 7.12/1.51  
% 7.12/1.51  clauses                                 16
% 7.12/1.51  conjectures                             1
% 7.12/1.51  EPR                                     2
% 7.12/1.51  Horn                                    15
% 7.12/1.51  unary                                   3
% 7.12/1.51  binary                                  9
% 7.12/1.51  lits                                    33
% 7.12/1.51  lits eq                                 14
% 7.12/1.51  fd_pure                                 0
% 7.12/1.51  fd_pseudo                               0
% 7.12/1.51  fd_cond                                 0
% 7.12/1.51  fd_pseudo_cond                          1
% 7.12/1.51  AC symbols                              0
% 7.12/1.51  
% 7.12/1.51  ------ Schedule dynamic 5 is on 
% 7.12/1.51  
% 7.12/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.12/1.51  
% 7.12/1.51  
% 7.12/1.51  ------ 
% 7.12/1.51  Current options:
% 7.12/1.51  ------ 
% 7.12/1.51  
% 7.12/1.51  ------ Input Options
% 7.12/1.51  
% 7.12/1.51  --out_options                           all
% 7.12/1.51  --tptp_safe_out                         true
% 7.12/1.51  --problem_path                          ""
% 7.12/1.51  --include_path                          ""
% 7.12/1.51  --clausifier                            res/vclausify_rel
% 7.12/1.51  --clausifier_options                    --mode clausify
% 7.12/1.51  --stdin                                 false
% 7.12/1.51  --stats_out                             all
% 7.12/1.51  
% 7.12/1.51  ------ General Options
% 7.12/1.51  
% 7.12/1.51  --fof                                   false
% 7.12/1.51  --time_out_real                         305.
% 7.12/1.51  --time_out_virtual                      -1.
% 7.12/1.51  --symbol_type_check                     false
% 7.12/1.51  --clausify_out                          false
% 7.12/1.51  --sig_cnt_out                           false
% 7.12/1.51  --trig_cnt_out                          false
% 7.12/1.51  --trig_cnt_out_tolerance                1.
% 7.12/1.51  --trig_cnt_out_sk_spl                   false
% 7.12/1.51  --abstr_cl_out                          false
% 7.12/1.51  
% 7.12/1.51  ------ Global Options
% 7.12/1.51  
% 7.12/1.51  --schedule                              default
% 7.12/1.51  --add_important_lit                     false
% 7.12/1.51  --prop_solver_per_cl                    1000
% 7.12/1.51  --min_unsat_core                        false
% 7.12/1.51  --soft_assumptions                      false
% 7.12/1.51  --soft_lemma_size                       3
% 7.12/1.51  --prop_impl_unit_size                   0
% 7.12/1.51  --prop_impl_unit                        []
% 7.12/1.51  --share_sel_clauses                     true
% 7.12/1.51  --reset_solvers                         false
% 7.12/1.51  --bc_imp_inh                            [conj_cone]
% 7.12/1.51  --conj_cone_tolerance                   3.
% 7.12/1.51  --extra_neg_conj                        none
% 7.12/1.51  --large_theory_mode                     true
% 7.12/1.51  --prolific_symb_bound                   200
% 7.12/1.51  --lt_threshold                          2000
% 7.12/1.51  --clause_weak_htbl                      true
% 7.12/1.51  --gc_record_bc_elim                     false
% 7.12/1.51  
% 7.12/1.51  ------ Preprocessing Options
% 7.12/1.51  
% 7.12/1.51  --preprocessing_flag                    true
% 7.12/1.51  --time_out_prep_mult                    0.1
% 7.12/1.51  --splitting_mode                        input
% 7.12/1.51  --splitting_grd                         true
% 7.12/1.51  --splitting_cvd                         false
% 7.12/1.51  --splitting_cvd_svl                     false
% 7.12/1.51  --splitting_nvd                         32
% 7.12/1.51  --sub_typing                            true
% 7.12/1.51  --prep_gs_sim                           true
% 7.12/1.51  --prep_unflatten                        true
% 7.12/1.51  --prep_res_sim                          true
% 7.12/1.51  --prep_upred                            true
% 7.12/1.51  --prep_sem_filter                       exhaustive
% 7.12/1.51  --prep_sem_filter_out                   false
% 7.12/1.51  --pred_elim                             true
% 7.12/1.51  --res_sim_input                         true
% 7.12/1.51  --eq_ax_congr_red                       true
% 7.12/1.51  --pure_diseq_elim                       true
% 7.12/1.51  --brand_transform                       false
% 7.12/1.51  --non_eq_to_eq                          false
% 7.12/1.51  --prep_def_merge                        true
% 7.12/1.51  --prep_def_merge_prop_impl              false
% 7.12/1.51  --prep_def_merge_mbd                    true
% 7.12/1.51  --prep_def_merge_tr_red                 false
% 7.12/1.51  --prep_def_merge_tr_cl                  false
% 7.12/1.51  --smt_preprocessing                     true
% 7.12/1.51  --smt_ac_axioms                         fast
% 7.12/1.51  --preprocessed_out                      false
% 7.12/1.51  --preprocessed_stats                    false
% 7.12/1.51  
% 7.12/1.51  ------ Abstraction refinement Options
% 7.12/1.51  
% 7.12/1.51  --abstr_ref                             []
% 7.12/1.51  --abstr_ref_prep                        false
% 7.12/1.51  --abstr_ref_until_sat                   false
% 7.12/1.51  --abstr_ref_sig_restrict                funpre
% 7.12/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.12/1.51  --abstr_ref_under                       []
% 7.12/1.51  
% 7.12/1.51  ------ SAT Options
% 7.12/1.51  
% 7.12/1.51  --sat_mode                              false
% 7.12/1.51  --sat_fm_restart_options                ""
% 7.12/1.51  --sat_gr_def                            false
% 7.12/1.51  --sat_epr_types                         true
% 7.12/1.51  --sat_non_cyclic_types                  false
% 7.12/1.51  --sat_finite_models                     false
% 7.12/1.51  --sat_fm_lemmas                         false
% 7.12/1.51  --sat_fm_prep                           false
% 7.12/1.51  --sat_fm_uc_incr                        true
% 7.12/1.51  --sat_out_model                         small
% 7.12/1.51  --sat_out_clauses                       false
% 7.12/1.51  
% 7.12/1.51  ------ QBF Options
% 7.12/1.51  
% 7.12/1.51  --qbf_mode                              false
% 7.12/1.51  --qbf_elim_univ                         false
% 7.12/1.51  --qbf_dom_inst                          none
% 7.12/1.51  --qbf_dom_pre_inst                      false
% 7.12/1.51  --qbf_sk_in                             false
% 7.12/1.51  --qbf_pred_elim                         true
% 7.12/1.51  --qbf_split                             512
% 7.12/1.51  
% 7.12/1.51  ------ BMC1 Options
% 7.12/1.51  
% 7.12/1.51  --bmc1_incremental                      false
% 7.12/1.51  --bmc1_axioms                           reachable_all
% 7.12/1.51  --bmc1_min_bound                        0
% 7.12/1.51  --bmc1_max_bound                        -1
% 7.12/1.51  --bmc1_max_bound_default                -1
% 7.12/1.51  --bmc1_symbol_reachability              true
% 7.12/1.51  --bmc1_property_lemmas                  false
% 7.12/1.51  --bmc1_k_induction                      false
% 7.12/1.51  --bmc1_non_equiv_states                 false
% 7.12/1.51  --bmc1_deadlock                         false
% 7.12/1.51  --bmc1_ucm                              false
% 7.12/1.51  --bmc1_add_unsat_core                   none
% 7.12/1.51  --bmc1_unsat_core_children              false
% 7.12/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.12/1.51  --bmc1_out_stat                         full
% 7.12/1.51  --bmc1_ground_init                      false
% 7.12/1.51  --bmc1_pre_inst_next_state              false
% 7.12/1.51  --bmc1_pre_inst_state                   false
% 7.12/1.51  --bmc1_pre_inst_reach_state             false
% 7.12/1.51  --bmc1_out_unsat_core                   false
% 7.12/1.51  --bmc1_aig_witness_out                  false
% 7.12/1.51  --bmc1_verbose                          false
% 7.12/1.51  --bmc1_dump_clauses_tptp                false
% 7.12/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.12/1.51  --bmc1_dump_file                        -
% 7.12/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.12/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.12/1.51  --bmc1_ucm_extend_mode                  1
% 7.12/1.51  --bmc1_ucm_init_mode                    2
% 7.12/1.51  --bmc1_ucm_cone_mode                    none
% 7.12/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.12/1.51  --bmc1_ucm_relax_model                  4
% 7.12/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.12/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.12/1.51  --bmc1_ucm_layered_model                none
% 7.12/1.51  --bmc1_ucm_max_lemma_size               10
% 7.12/1.51  
% 7.12/1.51  ------ AIG Options
% 7.12/1.51  
% 7.12/1.51  --aig_mode                              false
% 7.12/1.51  
% 7.12/1.51  ------ Instantiation Options
% 7.12/1.51  
% 7.12/1.51  --instantiation_flag                    true
% 7.12/1.51  --inst_sos_flag                         false
% 7.12/1.51  --inst_sos_phase                        true
% 7.12/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.12/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.12/1.51  --inst_lit_sel_side                     none
% 7.12/1.51  --inst_solver_per_active                1400
% 7.12/1.51  --inst_solver_calls_frac                1.
% 7.12/1.51  --inst_passive_queue_type               priority_queues
% 7.12/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.12/1.51  --inst_passive_queues_freq              [25;2]
% 7.12/1.51  --inst_dismatching                      true
% 7.12/1.51  --inst_eager_unprocessed_to_passive     true
% 7.12/1.51  --inst_prop_sim_given                   true
% 7.12/1.51  --inst_prop_sim_new                     false
% 7.12/1.51  --inst_subs_new                         false
% 7.12/1.51  --inst_eq_res_simp                      false
% 7.12/1.51  --inst_subs_given                       false
% 7.12/1.51  --inst_orphan_elimination               true
% 7.12/1.51  --inst_learning_loop_flag               true
% 7.12/1.51  --inst_learning_start                   3000
% 7.12/1.51  --inst_learning_factor                  2
% 7.12/1.51  --inst_start_prop_sim_after_learn       3
% 7.12/1.51  --inst_sel_renew                        solver
% 7.12/1.51  --inst_lit_activity_flag                true
% 7.12/1.51  --inst_restr_to_given                   false
% 7.12/1.51  --inst_activity_threshold               500
% 7.12/1.51  --inst_out_proof                        true
% 7.12/1.51  
% 7.12/1.51  ------ Resolution Options
% 7.12/1.51  
% 7.12/1.51  --resolution_flag                       false
% 7.12/1.51  --res_lit_sel                           adaptive
% 7.12/1.51  --res_lit_sel_side                      none
% 7.12/1.51  --res_ordering                          kbo
% 7.12/1.51  --res_to_prop_solver                    active
% 7.12/1.51  --res_prop_simpl_new                    false
% 7.12/1.51  --res_prop_simpl_given                  true
% 7.12/1.51  --res_passive_queue_type                priority_queues
% 7.12/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.12/1.51  --res_passive_queues_freq               [15;5]
% 7.12/1.51  --res_forward_subs                      full
% 7.12/1.51  --res_backward_subs                     full
% 7.12/1.51  --res_forward_subs_resolution           true
% 7.12/1.51  --res_backward_subs_resolution          true
% 7.12/1.51  --res_orphan_elimination                true
% 7.12/1.51  --res_time_limit                        2.
% 7.12/1.51  --res_out_proof                         true
% 7.12/1.51  
% 7.12/1.51  ------ Superposition Options
% 7.12/1.51  
% 7.12/1.51  --superposition_flag                    true
% 7.12/1.51  --sup_passive_queue_type                priority_queues
% 7.12/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.12/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.12/1.51  --demod_completeness_check              fast
% 7.12/1.51  --demod_use_ground                      true
% 7.12/1.51  --sup_to_prop_solver                    passive
% 7.12/1.51  --sup_prop_simpl_new                    true
% 7.12/1.51  --sup_prop_simpl_given                  true
% 7.12/1.51  --sup_fun_splitting                     false
% 7.12/1.51  --sup_smt_interval                      50000
% 7.12/1.51  
% 7.12/1.51  ------ Superposition Simplification Setup
% 7.12/1.51  
% 7.12/1.51  --sup_indices_passive                   []
% 7.12/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.12/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.12/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.12/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.12/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.12/1.51  --sup_full_bw                           [BwDemod]
% 7.12/1.51  --sup_immed_triv                        [TrivRules]
% 7.12/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.12/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.12/1.51  --sup_immed_bw_main                     []
% 7.12/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.12/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.12/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.12/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.12/1.51  
% 7.12/1.51  ------ Combination Options
% 7.12/1.51  
% 7.12/1.51  --comb_res_mult                         3
% 7.12/1.51  --comb_sup_mult                         2
% 7.12/1.51  --comb_inst_mult                        10
% 7.12/1.51  
% 7.12/1.51  ------ Debug Options
% 7.12/1.51  
% 7.12/1.51  --dbg_backtrace                         false
% 7.12/1.51  --dbg_dump_prop_clauses                 false
% 7.12/1.51  --dbg_dump_prop_clauses_file            -
% 7.12/1.51  --dbg_out_stat                          false
% 7.12/1.51  
% 7.12/1.51  
% 7.12/1.51  
% 7.12/1.51  
% 7.12/1.51  ------ Proving...
% 7.12/1.51  
% 7.12/1.51  
% 7.12/1.51  % SZS status Theorem for theBenchmark.p
% 7.12/1.51  
% 7.12/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.12/1.51  
% 7.12/1.51  fof(f12,conjecture,(
% 7.12/1.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 7.12/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.51  
% 7.12/1.51  fof(f13,negated_conjecture,(
% 7.12/1.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 7.12/1.51    inference(negated_conjecture,[],[f12])).
% 7.12/1.51  
% 7.12/1.51  fof(f25,plain,(
% 7.12/1.51    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.12/1.51    inference(ennf_transformation,[],[f13])).
% 7.12/1.51  
% 7.12/1.51  fof(f26,plain,(
% 7.12/1.51    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.12/1.51    inference(flattening,[],[f25])).
% 7.12/1.51  
% 7.12/1.51  fof(f30,plain,(
% 7.12/1.51    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.12/1.51    inference(nnf_transformation,[],[f26])).
% 7.12/1.51  
% 7.12/1.51  fof(f31,plain,(
% 7.12/1.51    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.12/1.51    inference(flattening,[],[f30])).
% 7.12/1.51  
% 7.12/1.51  fof(f33,plain,(
% 7.12/1.51    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.12/1.51    introduced(choice_axiom,[])).
% 7.12/1.51  
% 7.12/1.51  fof(f32,plain,(
% 7.12/1.51    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 7.12/1.51    introduced(choice_axiom,[])).
% 7.12/1.51  
% 7.12/1.51  fof(f34,plain,(
% 7.12/1.51    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 7.12/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f33,f32])).
% 7.12/1.51  
% 7.12/1.51  fof(f53,plain,(
% 7.12/1.51    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 7.12/1.51    inference(cnf_transformation,[],[f34])).
% 7.12/1.51  
% 7.12/1.51  fof(f8,axiom,(
% 7.12/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 7.12/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.51  
% 7.12/1.51  fof(f19,plain,(
% 7.12/1.51    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.12/1.51    inference(ennf_transformation,[],[f8])).
% 7.12/1.51  
% 7.12/1.51  fof(f20,plain,(
% 7.12/1.51    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.12/1.51    inference(flattening,[],[f19])).
% 7.12/1.51  
% 7.12/1.51  fof(f45,plain,(
% 7.12/1.51    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.12/1.51    inference(cnf_transformation,[],[f20])).
% 7.12/1.51  
% 7.12/1.51  fof(f51,plain,(
% 7.12/1.51    l1_pre_topc(sK0)),
% 7.12/1.51    inference(cnf_transformation,[],[f34])).
% 7.12/1.51  
% 7.12/1.51  fof(f52,plain,(
% 7.12/1.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 7.12/1.51    inference(cnf_transformation,[],[f34])).
% 7.12/1.51  
% 7.12/1.51  fof(f7,axiom,(
% 7.12/1.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.12/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.51  
% 7.12/1.51  fof(f29,plain,(
% 7.12/1.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.12/1.51    inference(nnf_transformation,[],[f7])).
% 7.12/1.51  
% 7.12/1.51  fof(f43,plain,(
% 7.12/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.12/1.51    inference(cnf_transformation,[],[f29])).
% 7.12/1.51  
% 7.12/1.51  fof(f6,axiom,(
% 7.12/1.51    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 7.12/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.51  
% 7.12/1.51  fof(f18,plain,(
% 7.12/1.51    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.12/1.51    inference(ennf_transformation,[],[f6])).
% 7.12/1.51  
% 7.12/1.51  fof(f42,plain,(
% 7.12/1.51    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.12/1.51    inference(cnf_transformation,[],[f18])).
% 7.12/1.51  
% 7.12/1.51  fof(f44,plain,(
% 7.12/1.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.12/1.51    inference(cnf_transformation,[],[f29])).
% 7.12/1.51  
% 7.12/1.51  fof(f2,axiom,(
% 7.12/1.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.12/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.51  
% 7.12/1.51  fof(f27,plain,(
% 7.12/1.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.12/1.51    inference(nnf_transformation,[],[f2])).
% 7.12/1.51  
% 7.12/1.51  fof(f28,plain,(
% 7.12/1.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.12/1.51    inference(flattening,[],[f27])).
% 7.12/1.51  
% 7.12/1.51  fof(f36,plain,(
% 7.12/1.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 7.12/1.51    inference(cnf_transformation,[],[f28])).
% 7.12/1.51  
% 7.12/1.51  fof(f56,plain,(
% 7.12/1.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.12/1.51    inference(equality_resolution,[],[f36])).
% 7.12/1.51  
% 7.12/1.51  fof(f4,axiom,(
% 7.12/1.51    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 7.12/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.51  
% 7.12/1.51  fof(f15,plain,(
% 7.12/1.51    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.12/1.51    inference(ennf_transformation,[],[f4])).
% 7.12/1.51  
% 7.12/1.51  fof(f40,plain,(
% 7.12/1.51    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.12/1.51    inference(cnf_transformation,[],[f15])).
% 7.12/1.51  
% 7.12/1.51  fof(f3,axiom,(
% 7.12/1.51    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 7.12/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.51  
% 7.12/1.51  fof(f14,plain,(
% 7.12/1.51    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 7.12/1.51    inference(ennf_transformation,[],[f3])).
% 7.12/1.51  
% 7.12/1.51  fof(f39,plain,(
% 7.12/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 7.12/1.51    inference(cnf_transformation,[],[f14])).
% 7.12/1.51  
% 7.12/1.51  fof(f1,axiom,(
% 7.12/1.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 7.12/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.51  
% 7.12/1.51  fof(f35,plain,(
% 7.12/1.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 7.12/1.51    inference(cnf_transformation,[],[f1])).
% 7.12/1.51  
% 7.12/1.51  fof(f5,axiom,(
% 7.12/1.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 7.12/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.51  
% 7.12/1.51  fof(f16,plain,(
% 7.12/1.51    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 7.12/1.51    inference(ennf_transformation,[],[f5])).
% 7.12/1.51  
% 7.12/1.51  fof(f17,plain,(
% 7.12/1.51    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.12/1.51    inference(flattening,[],[f16])).
% 7.12/1.51  
% 7.12/1.51  fof(f41,plain,(
% 7.12/1.51    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.12/1.51    inference(cnf_transformation,[],[f17])).
% 7.12/1.51  
% 7.12/1.51  fof(f11,axiom,(
% 7.12/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 7.12/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.51  
% 7.12/1.51  fof(f24,plain,(
% 7.12/1.51    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.12/1.51    inference(ennf_transformation,[],[f11])).
% 7.12/1.51  
% 7.12/1.51  fof(f49,plain,(
% 7.12/1.51    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.12/1.51    inference(cnf_transformation,[],[f24])).
% 7.12/1.51  
% 7.12/1.51  fof(f10,axiom,(
% 7.12/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 7.12/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.12/1.51  
% 7.12/1.51  fof(f23,plain,(
% 7.12/1.51    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.12/1.51    inference(ennf_transformation,[],[f10])).
% 7.12/1.51  
% 7.12/1.51  fof(f48,plain,(
% 7.12/1.51    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.12/1.51    inference(cnf_transformation,[],[f23])).
% 7.12/1.51  
% 7.12/1.51  fof(f54,plain,(
% 7.12/1.51    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 7.12/1.51    inference(cnf_transformation,[],[f34])).
% 7.12/1.51  
% 7.12/1.51  fof(f46,plain,(
% 7.12/1.51    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.12/1.51    inference(cnf_transformation,[],[f20])).
% 7.12/1.51  
% 7.12/1.51  fof(f50,plain,(
% 7.12/1.51    v2_pre_topc(sK0)),
% 7.12/1.51    inference(cnf_transformation,[],[f34])).
% 7.12/1.51  
% 7.12/1.51  cnf(c_16,negated_conjecture,
% 7.12/1.51      ( v4_pre_topc(sK1,sK0)
% 7.12/1.51      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.12/1.51      inference(cnf_transformation,[],[f53]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_154,plain,
% 7.12/1.51      ( v4_pre_topc(sK1,sK0)
% 7.12/1.51      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.12/1.51      inference(prop_impl,[status(thm)],[c_16]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_11,plain,
% 7.12/1.51      ( ~ v4_pre_topc(X0,X1)
% 7.12/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.12/1.51      | ~ l1_pre_topc(X1)
% 7.12/1.51      | k2_pre_topc(X1,X0) = X0 ),
% 7.12/1.51      inference(cnf_transformation,[],[f45]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_18,negated_conjecture,
% 7.12/1.51      ( l1_pre_topc(sK0) ),
% 7.12/1.51      inference(cnf_transformation,[],[f51]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_339,plain,
% 7.12/1.51      ( ~ v4_pre_topc(X0,X1)
% 7.12/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.12/1.51      | k2_pre_topc(X1,X0) = X0
% 7.12/1.51      | sK0 != X1 ),
% 7.12/1.51      inference(resolution_lifted,[status(thm)],[c_11,c_18]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_340,plain,
% 7.12/1.51      ( ~ v4_pre_topc(X0,sK0)
% 7.12/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.12/1.51      | k2_pre_topc(sK0,X0) = X0 ),
% 7.12/1.51      inference(unflattening,[status(thm)],[c_339]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_386,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.12/1.51      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.12/1.51      | k2_pre_topc(sK0,X0) = X0
% 7.12/1.51      | sK1 != X0
% 7.12/1.51      | sK0 != sK0 ),
% 7.12/1.51      inference(resolution_lifted,[status(thm)],[c_154,c_340]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_387,plain,
% 7.12/1.51      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.12/1.51      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.12/1.51      | k2_pre_topc(sK0,sK1) = sK1 ),
% 7.12/1.51      inference(unflattening,[status(thm)],[c_386]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_17,negated_conjecture,
% 7.12/1.51      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 7.12/1.51      inference(cnf_transformation,[],[f52]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_389,plain,
% 7.12/1.51      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.12/1.51      | k2_pre_topc(sK0,sK1) = sK1 ),
% 7.12/1.51      inference(global_propositional_subsumption,
% 7.12/1.51                [status(thm)],
% 7.12/1.51                [c_387,c_17]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_487,plain,
% 7.12/1.51      ( k2_pre_topc(sK0,sK1) = sK1
% 7.12/1.51      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.12/1.51      inference(prop_impl,[status(thm)],[c_389]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_488,plain,
% 7.12/1.51      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 7.12/1.51      | k2_pre_topc(sK0,sK1) = sK1 ),
% 7.12/1.51      inference(renaming,[status(thm)],[c_487]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_917,plain,
% 7.12/1.51      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.12/1.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_9,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.12/1.51      inference(cnf_transformation,[],[f43]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_918,plain,
% 7.12/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.12/1.51      | r1_tarski(X0,X1) = iProver_top ),
% 7.12/1.51      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_1291,plain,
% 7.12/1.51      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_917,c_918]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_7,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.12/1.51      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 7.12/1.51      inference(cnf_transformation,[],[f42]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_8,plain,
% 7.12/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.12/1.51      inference(cnf_transformation,[],[f44]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_150,plain,
% 7.12/1.51      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.12/1.51      inference(prop_impl,[status(thm)],[c_8]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_151,plain,
% 7.12/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.12/1.51      inference(renaming,[status(thm)],[c_150]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_191,plain,
% 7.12/1.51      ( ~ r1_tarski(X0,X1) | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 7.12/1.51      inference(bin_hyper_res,[status(thm)],[c_7,c_151]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_915,plain,
% 7.12/1.51      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 7.12/1.51      | r1_tarski(X1,X0) != iProver_top ),
% 7.12/1.51      inference(predicate_to_equality,[status(thm)],[c_191]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_1930,plain,
% 7.12/1.51      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_1291,c_915]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_1939,plain,
% 7.12/1.51      ( k2_pre_topc(sK0,sK1) = sK1
% 7.12/1.51      | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_488,c_1930]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_3,plain,
% 7.12/1.51      ( r1_tarski(X0,X0) ),
% 7.12/1.51      inference(cnf_transformation,[],[f56]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_921,plain,
% 7.12/1.51      ( r1_tarski(X0,X0) = iProver_top ),
% 7.12/1.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_5,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.12/1.51      | m1_subset_1(k7_subset_1(X1,X0,X2),k1_zfmisc_1(X1)) ),
% 7.12/1.51      inference(cnf_transformation,[],[f40]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_189,plain,
% 7.12/1.51      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
% 7.12/1.51      | ~ r1_tarski(X1,X0) ),
% 7.12/1.51      inference(bin_hyper_res,[status(thm)],[c_5,c_151]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_916,plain,
% 7.12/1.51      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) = iProver_top
% 7.12/1.51      | r1_tarski(X1,X0) != iProver_top ),
% 7.12/1.51      inference(predicate_to_equality,[status(thm)],[c_189]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_2186,plain,
% 7.12/1.51      ( r1_tarski(X0,X1) != iProver_top
% 7.12/1.51      | r1_tarski(k7_subset_1(X1,X0,X2),X1) = iProver_top ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_916,c_918]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_4,plain,
% 7.12/1.51      ( ~ r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1 ),
% 7.12/1.51      inference(cnf_transformation,[],[f39]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_920,plain,
% 7.12/1.51      ( k2_xboole_0(X0,X1) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 7.12/1.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_2675,plain,
% 7.12/1.51      ( k2_xboole_0(k7_subset_1(X0,X1,X2),X0) = X0
% 7.12/1.51      | r1_tarski(X1,X0) != iProver_top ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_2186,c_920]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_3541,plain,
% 7.12/1.51      ( k2_xboole_0(k7_subset_1(X0,X0,X1),X0) = X0 ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_921,c_2675]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_1929,plain,
% 7.12/1.51      ( k7_subset_1(X0,X0,X1) = k4_xboole_0(X0,X1) ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_921,c_915]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_3559,plain,
% 7.12/1.51      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 7.12/1.51      inference(light_normalisation,[status(thm)],[c_3541,c_1929]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_0,plain,
% 7.12/1.51      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 7.12/1.51      inference(cnf_transformation,[],[f35]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_5469,plain,
% 7.12/1.51      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_3559,c_0]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_5591,plain,
% 7.12/1.51      ( k2_pre_topc(sK0,sK1) = sK1
% 7.12/1.51      | k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_1939,c_5469]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_2181,plain,
% 7.12/1.51      ( k2_pre_topc(sK0,sK1) = sK1
% 7.12/1.51      | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 7.12/1.51      | r1_tarski(sK1,u1_struct_0(sK0)) != iProver_top ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_488,c_916]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_22,plain,
% 7.12/1.51      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.12/1.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_1110,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.12/1.51      | r1_tarski(X0,u1_struct_0(sK0)) ),
% 7.12/1.51      inference(instantiation,[status(thm)],[c_9]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_1180,plain,
% 7.12/1.51      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.12/1.51      | r1_tarski(sK1,u1_struct_0(sK0)) ),
% 7.12/1.51      inference(instantiation,[status(thm)],[c_1110]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_1181,plain,
% 7.12/1.51      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 7.12/1.51      | r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 7.12/1.51      inference(predicate_to_equality,[status(thm)],[c_1180]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_2524,plain,
% 7.12/1.51      ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 7.12/1.51      | k2_pre_topc(sK0,sK1) = sK1 ),
% 7.12/1.51      inference(global_propositional_subsumption,
% 7.12/1.51                [status(thm)],
% 7.12/1.51                [c_2181,c_22,c_1181]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_2525,plain,
% 7.12/1.51      ( k2_pre_topc(sK0,sK1) = sK1
% 7.12/1.51      | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 7.12/1.51      inference(renaming,[status(thm)],[c_2524]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_2530,plain,
% 7.12/1.51      ( k2_pre_topc(sK0,sK1) = sK1
% 7.12/1.51      | r1_tarski(k2_tops_1(sK0,sK1),u1_struct_0(sK0)) = iProver_top ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_2525,c_918]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_6,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.12/1.51      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.12/1.51      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 7.12/1.51      inference(cnf_transformation,[],[f41]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_190,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.12/1.51      | ~ r1_tarski(X2,X1)
% 7.12/1.51      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 7.12/1.51      inference(bin_hyper_res,[status(thm)],[c_6,c_151]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_483,plain,
% 7.12/1.51      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.12/1.51      inference(prop_impl,[status(thm)],[c_8]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_484,plain,
% 7.12/1.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.12/1.51      inference(renaming,[status(thm)],[c_483]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_515,plain,
% 7.12/1.51      ( ~ r1_tarski(X0,X1)
% 7.12/1.51      | ~ r1_tarski(X2,X1)
% 7.12/1.51      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 7.12/1.51      inference(bin_hyper_res,[status(thm)],[c_190,c_484]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_911,plain,
% 7.12/1.51      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 7.12/1.51      | r1_tarski(X2,X0) != iProver_top
% 7.12/1.51      | r1_tarski(X1,X0) != iProver_top ),
% 7.12/1.51      inference(predicate_to_equality,[status(thm)],[c_515]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_20085,plain,
% 7.12/1.51      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
% 7.12/1.51      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_1291,c_911]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_20519,plain,
% 7.12/1.51      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
% 7.12/1.51      | k2_pre_topc(sK0,sK1) = sK1 ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_2530,c_20085]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_14,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.12/1.51      | ~ l1_pre_topc(X1)
% 7.12/1.51      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 7.12/1.51      inference(cnf_transformation,[],[f49]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_315,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.12/1.51      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
% 7.12/1.51      | sK0 != X1 ),
% 7.12/1.51      inference(resolution_lifted,[status(thm)],[c_14,c_18]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_316,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.12/1.51      | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 7.12/1.51      inference(unflattening,[status(thm)],[c_315]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_914,plain,
% 7.12/1.51      ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
% 7.12/1.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.12/1.51      inference(predicate_to_equality,[status(thm)],[c_316]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_1036,plain,
% 7.12/1.51      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_917,c_914]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_20547,plain,
% 7.12/1.51      ( k2_pre_topc(sK0,sK1) = sK1
% 7.12/1.51      | k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 7.12/1.51      inference(light_normalisation,[status(thm)],[c_20519,c_1036]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_20754,plain,
% 7.12/1.51      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_5591,c_20547]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_13,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.12/1.51      | ~ l1_pre_topc(X1)
% 7.12/1.51      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 7.12/1.51      inference(cnf_transformation,[],[f48]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_327,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.12/1.51      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 7.12/1.51      | sK0 != X1 ),
% 7.12/1.51      inference(resolution_lifted,[status(thm)],[c_13,c_18]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_328,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.12/1.51      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 7.12/1.51      inference(unflattening,[status(thm)],[c_327]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_913,plain,
% 7.12/1.51      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 7.12/1.51      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 7.12/1.51      inference(predicate_to_equality,[status(thm)],[c_328]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_1052,plain,
% 7.12/1.51      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.12/1.51      inference(superposition,[status(thm)],[c_917,c_913]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_20804,plain,
% 7.12/1.51      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 7.12/1.51      inference(demodulation,[status(thm)],[c_20754,c_1052]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_15,negated_conjecture,
% 7.12/1.51      ( ~ v4_pre_topc(sK1,sK0)
% 7.12/1.51      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 7.12/1.51      inference(cnf_transformation,[],[f54]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_152,plain,
% 7.12/1.51      ( ~ v4_pre_topc(sK1,sK0)
% 7.12/1.51      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 7.12/1.51      inference(prop_impl,[status(thm)],[c_15]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_10,plain,
% 7.12/1.51      ( v4_pre_topc(X0,X1)
% 7.12/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.12/1.51      | ~ l1_pre_topc(X1)
% 7.12/1.51      | ~ v2_pre_topc(X1)
% 7.12/1.51      | k2_pre_topc(X1,X0) != X0 ),
% 7.12/1.51      inference(cnf_transformation,[],[f46]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_19,negated_conjecture,
% 7.12/1.51      ( v2_pre_topc(sK0) ),
% 7.12/1.51      inference(cnf_transformation,[],[f50]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_287,plain,
% 7.12/1.51      ( v4_pre_topc(X0,X1)
% 7.12/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.12/1.51      | ~ l1_pre_topc(X1)
% 7.12/1.51      | k2_pre_topc(X1,X0) != X0
% 7.12/1.51      | sK0 != X1 ),
% 7.12/1.51      inference(resolution_lifted,[status(thm)],[c_10,c_19]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_288,plain,
% 7.12/1.51      ( v4_pre_topc(X0,sK0)
% 7.12/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.12/1.51      | ~ l1_pre_topc(sK0)
% 7.12/1.51      | k2_pre_topc(sK0,X0) != X0 ),
% 7.12/1.51      inference(unflattening,[status(thm)],[c_287]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_292,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.12/1.51      | v4_pre_topc(X0,sK0)
% 7.12/1.51      | k2_pre_topc(sK0,X0) != X0 ),
% 7.12/1.51      inference(global_propositional_subsumption,
% 7.12/1.51                [status(thm)],
% 7.12/1.51                [c_288,c_18]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_293,plain,
% 7.12/1.51      ( v4_pre_topc(X0,sK0)
% 7.12/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.12/1.51      | k2_pre_topc(sK0,X0) != X0 ),
% 7.12/1.51      inference(renaming,[status(thm)],[c_292]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_397,plain,
% 7.12/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.12/1.51      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 7.12/1.51      | k2_pre_topc(sK0,X0) != X0
% 7.12/1.51      | sK1 != X0
% 7.12/1.51      | sK0 != sK0 ),
% 7.12/1.51      inference(resolution_lifted,[status(thm)],[c_152,c_293]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_398,plain,
% 7.12/1.51      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 7.12/1.51      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 7.12/1.51      | k2_pre_topc(sK0,sK1) != sK1 ),
% 7.12/1.51      inference(unflattening,[status(thm)],[c_397]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(c_400,plain,
% 7.12/1.51      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 7.12/1.51      | k2_pre_topc(sK0,sK1) != sK1 ),
% 7.12/1.51      inference(global_propositional_subsumption,
% 7.12/1.51                [status(thm)],
% 7.12/1.51                [c_398,c_17]) ).
% 7.12/1.51  
% 7.12/1.51  cnf(contradiction,plain,
% 7.12/1.51      ( $false ),
% 7.12/1.51      inference(minisat,[status(thm)],[c_20804,c_20754,c_400]) ).
% 7.12/1.51  
% 7.12/1.51  
% 7.12/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.12/1.51  
% 7.12/1.51  ------                               Statistics
% 7.12/1.51  
% 7.12/1.51  ------ General
% 7.12/1.51  
% 7.12/1.51  abstr_ref_over_cycles:                  0
% 7.12/1.51  abstr_ref_under_cycles:                 0
% 7.12/1.51  gc_basic_clause_elim:                   0
% 7.12/1.51  forced_gc_time:                         0
% 7.12/1.51  parsing_time:                           0.013
% 7.12/1.51  unif_index_cands_time:                  0.
% 7.12/1.51  unif_index_add_time:                    0.
% 7.12/1.51  orderings_time:                         0.
% 7.12/1.51  out_proof_time:                         0.01
% 7.12/1.51  total_time:                             0.879
% 7.12/1.51  num_of_symbols:                         47
% 7.12/1.51  num_of_terms:                           22744
% 7.12/1.51  
% 7.12/1.51  ------ Preprocessing
% 7.12/1.51  
% 7.12/1.51  num_of_splits:                          0
% 7.12/1.51  num_of_split_atoms:                     0
% 7.12/1.51  num_of_reused_defs:                     0
% 7.12/1.51  num_eq_ax_congr_red:                    23
% 7.12/1.51  num_of_sem_filtered_clauses:            1
% 7.12/1.51  num_of_subtypes:                        0
% 7.12/1.51  monotx_restored_types:                  0
% 7.12/1.51  sat_num_of_epr_types:                   0
% 7.12/1.51  sat_num_of_non_cyclic_types:            0
% 7.12/1.51  sat_guarded_non_collapsed_types:        0
% 7.12/1.51  num_pure_diseq_elim:                    0
% 7.12/1.51  simp_replaced_by:                       0
% 7.12/1.51  res_preprocessed:                       88
% 7.12/1.51  prep_upred:                             0
% 7.12/1.51  prep_unflattend:                        8
% 7.12/1.51  smt_new_axioms:                         0
% 7.12/1.51  pred_elim_cands:                        2
% 7.12/1.51  pred_elim:                              3
% 7.12/1.51  pred_elim_cl:                           3
% 7.12/1.51  pred_elim_cycles:                       5
% 7.12/1.51  merged_defs:                            16
% 7.12/1.51  merged_defs_ncl:                        0
% 7.12/1.51  bin_hyper_res:                          21
% 7.12/1.51  prep_cycles:                            4
% 7.12/1.51  pred_elim_time:                         0.003
% 7.12/1.51  splitting_time:                         0.
% 7.12/1.51  sem_filter_time:                        0.
% 7.12/1.51  monotx_time:                            0.
% 7.12/1.51  subtype_inf_time:                       0.
% 7.12/1.51  
% 7.12/1.51  ------ Problem properties
% 7.12/1.51  
% 7.12/1.51  clauses:                                16
% 7.12/1.51  conjectures:                            1
% 7.12/1.51  epr:                                    2
% 7.12/1.51  horn:                                   15
% 7.12/1.51  ground:                                 3
% 7.12/1.51  unary:                                  3
% 7.12/1.51  binary:                                 9
% 7.12/1.51  lits:                                   33
% 7.12/1.51  lits_eq:                                14
% 7.12/1.51  fd_pure:                                0
% 7.12/1.51  fd_pseudo:                              0
% 7.12/1.51  fd_cond:                                0
% 7.12/1.51  fd_pseudo_cond:                         1
% 7.12/1.51  ac_symbols:                             0
% 7.12/1.51  
% 7.12/1.51  ------ Propositional Solver
% 7.12/1.51  
% 7.12/1.51  prop_solver_calls:                      32
% 7.12/1.51  prop_fast_solver_calls:                 1030
% 7.12/1.51  smt_solver_calls:                       0
% 7.12/1.51  smt_fast_solver_calls:                  0
% 7.12/1.51  prop_num_of_clauses:                    8720
% 7.12/1.51  prop_preprocess_simplified:             16245
% 7.12/1.51  prop_fo_subsumed:                       24
% 7.12/1.51  prop_solver_time:                       0.
% 7.12/1.51  smt_solver_time:                        0.
% 7.12/1.51  smt_fast_solver_time:                   0.
% 7.12/1.51  prop_fast_solver_time:                  0.
% 7.12/1.51  prop_unsat_core_time:                   0.001
% 7.12/1.51  
% 7.12/1.51  ------ QBF
% 7.12/1.51  
% 7.12/1.51  qbf_q_res:                              0
% 7.12/1.51  qbf_num_tautologies:                    0
% 7.12/1.51  qbf_prep_cycles:                        0
% 7.12/1.51  
% 7.12/1.51  ------ BMC1
% 7.12/1.51  
% 7.12/1.51  bmc1_current_bound:                     -1
% 7.12/1.51  bmc1_last_solved_bound:                 -1
% 7.12/1.51  bmc1_unsat_core_size:                   -1
% 7.12/1.51  bmc1_unsat_core_parents_size:           -1
% 7.12/1.51  bmc1_merge_next_fun:                    0
% 7.12/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.12/1.51  
% 7.12/1.51  ------ Instantiation
% 7.12/1.51  
% 7.12/1.51  inst_num_of_clauses:                    3022
% 7.12/1.51  inst_num_in_passive:                    720
% 7.12/1.51  inst_num_in_active:                     1182
% 7.12/1.51  inst_num_in_unprocessed:                1120
% 7.12/1.51  inst_num_of_loops:                      1200
% 7.12/1.51  inst_num_of_learning_restarts:          0
% 7.12/1.51  inst_num_moves_active_passive:          12
% 7.12/1.51  inst_lit_activity:                      0
% 7.12/1.51  inst_lit_activity_moves:                0
% 7.12/1.51  inst_num_tautologies:                   0
% 7.12/1.51  inst_num_prop_implied:                  0
% 7.12/1.51  inst_num_existing_simplified:           0
% 7.12/1.51  inst_num_eq_res_simplified:             0
% 7.12/1.51  inst_num_child_elim:                    0
% 7.12/1.51  inst_num_of_dismatching_blockings:      1658
% 7.12/1.51  inst_num_of_non_proper_insts:           4260
% 7.12/1.51  inst_num_of_duplicates:                 0
% 7.12/1.51  inst_inst_num_from_inst_to_res:         0
% 7.12/1.51  inst_dismatching_checking_time:         0.
% 7.12/1.51  
% 7.12/1.51  ------ Resolution
% 7.12/1.51  
% 7.12/1.51  res_num_of_clauses:                     0
% 7.12/1.51  res_num_in_passive:                     0
% 7.12/1.51  res_num_in_active:                      0
% 7.12/1.51  res_num_of_loops:                       92
% 7.12/1.51  res_forward_subset_subsumed:            278
% 7.12/1.51  res_backward_subset_subsumed:           2
% 7.12/1.51  res_forward_subsumed:                   0
% 7.12/1.51  res_backward_subsumed:                  0
% 7.12/1.51  res_forward_subsumption_resolution:     0
% 7.12/1.51  res_backward_subsumption_resolution:    0
% 7.12/1.51  res_clause_to_clause_subsumption:       1900
% 7.12/1.51  res_orphan_elimination:                 0
% 7.12/1.51  res_tautology_del:                      463
% 7.12/1.51  res_num_eq_res_simplified:              0
% 7.12/1.51  res_num_sel_changes:                    0
% 7.12/1.51  res_moves_from_active_to_pass:          0
% 7.12/1.51  
% 7.12/1.51  ------ Superposition
% 7.12/1.51  
% 7.12/1.51  sup_time_total:                         0.
% 7.12/1.51  sup_time_generating:                    0.
% 7.12/1.51  sup_time_sim_full:                      0.
% 7.12/1.51  sup_time_sim_immed:                     0.
% 7.12/1.51  
% 7.12/1.51  sup_num_of_clauses:                     269
% 7.12/1.51  sup_num_in_active:                      124
% 7.12/1.51  sup_num_in_passive:                     145
% 7.12/1.51  sup_num_of_loops:                       239
% 7.12/1.51  sup_fw_superposition:                   314
% 7.12/1.51  sup_bw_superposition:                   344
% 7.12/1.51  sup_immediate_simplified:               82
% 7.12/1.51  sup_given_eliminated:                   0
% 7.12/1.51  comparisons_done:                       0
% 7.12/1.51  comparisons_avoided:                    288
% 7.12/1.51  
% 7.12/1.51  ------ Simplifications
% 7.12/1.51  
% 7.12/1.51  
% 7.12/1.51  sim_fw_subset_subsumed:                 3
% 7.12/1.51  sim_bw_subset_subsumed:                 142
% 7.12/1.51  sim_fw_subsumed:                        4
% 7.12/1.51  sim_bw_subsumed:                        0
% 7.12/1.51  sim_fw_subsumption_res:                 2
% 7.12/1.51  sim_bw_subsumption_res:                 0
% 7.12/1.51  sim_tautology_del:                      2
% 7.12/1.51  sim_eq_tautology_del:                   54
% 7.12/1.51  sim_eq_res_simp:                        1
% 7.12/1.51  sim_fw_demodulated:                     40
% 7.12/1.51  sim_bw_demodulated:                     58
% 7.12/1.51  sim_light_normalised:                   36
% 7.12/1.51  sim_joinable_taut:                      0
% 7.12/1.51  sim_joinable_simp:                      0
% 7.12/1.51  sim_ac_normalised:                      0
% 7.12/1.51  sim_smt_subsumption:                    0
% 7.12/1.51  
%------------------------------------------------------------------------------
