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
% DateTime   : Thu Dec  3 12:15:57 EST 2020

% Result     : Theorem 27.39s
% Output     : CNFRefutation 27.39s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 650 expanded)
%              Number of clauses        :   99 ( 201 expanded)
%              Number of leaves         :   19 ( 151 expanded)
%              Depth                    :   23
%              Number of atoms          :  637 (2836 expanded)
%              Number of equality atoms :  136 ( 539 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              | ~ r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
            & ( ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
                & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) )
              | ~ v4_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f52])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
           => k1_tops_1(X0,k2_tops_1(X0,X1)) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_tops_1(X1,X0)
             => k1_tops_1(X0,k2_tops_1(X0,X1)) = k1_xboole_0 ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k1_tops_1(X0,k2_tops_1(X0,sK1)) != k1_xboole_0
        & v4_tops_1(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0
            & v4_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( k1_tops_1(sK0,k2_tops_1(sK0,X1)) != k1_xboole_0
          & v4_tops_1(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0
    & v4_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f49,f56,f55])).

fof(f83,plain,(
    v4_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f81,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f82,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f57])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f80,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f60,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => ( v3_tops_1(X1,X0)
            <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> k2_tops_1(X0,X1) = X1 )
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> k2_tops_1(X0,X1) = X1 )
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tops_1(X1,X0)
              | k2_tops_1(X0,X1) != X1 )
            & ( k2_tops_1(X0,X1) = X1
              | ~ v3_tops_1(X1,X0) ) )
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = X1
      | ~ v3_tops_1(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => v3_tops_1(k2_tops_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(k2_tops_1(X0,X1),X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(k2_tops_1(X0,X1),X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v3_tops_1(k2_tops_1(X0,X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f84,plain,(
    k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_9,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_23,negated_conjecture,
    ( v4_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_578,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_23])).

cnf(c_579,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_578])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_581,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_579,c_25,c_24])).

cnf(c_1323,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_581])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_682,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_25])).

cnf(c_683,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_682])).

cnf(c_1315,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_683])).

cnf(c_1326,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_14,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_18,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_291,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ r1_tarski(X2,X4)
    | r1_tarski(X2,k1_tops_1(X3,X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | X3 != X1
    | k1_tops_1(X1,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_18])).

cnf(c_292,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k1_tops_1(X1,X0),X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_296,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k1_tops_1(X1,X0),X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_292,c_10])).

cnf(c_297,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k1_tops_1(X1,X0),X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_296])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_480,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(k1_tops_1(X1,X0),X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_297,c_26])).

cnf(c_481,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,X0),X1)
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_480])).

cnf(c_485,plain,
    ( r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1))
    | ~ r1_tarski(k1_tops_1(sK0,X0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_481,c_25])).

cnf(c_486,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,X1),X0)
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
    inference(renaming,[status(thm)],[c_485])).

cnf(c_1325,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1),X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_486])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1329,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3720,plain,
    ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1325,c_1329])).

cnf(c_6356,plain,
    ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X1),X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1325,c_3720])).

cnf(c_38990,plain,
    ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1326,c_6356])).

cnf(c_39082,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = k1_tops_1(sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1315,c_38990])).

cnf(c_39155,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1323,c_39082])).

cnf(c_1447,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_683])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_658,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_25])).

cnf(c_659,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_658])).

cnf(c_1450,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_659])).

cnf(c_1462,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1))
    | ~ r1_tarski(k1_tops_1(sK0,X0),sK1) ),
    inference(instantiation,[status(thm)],[c_486])).

cnf(c_1713,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1))
    | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) ),
    inference(instantiation,[status(thm)],[c_1462])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_604,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_605,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) ),
    inference(unflattening,[status(thm)],[c_604])).

cnf(c_1467,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0))
    | ~ r1_tarski(sK1,X0) ),
    inference(instantiation,[status(thm)],[c_605])).

cnf(c_1730,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1467])).

cnf(c_6588,plain,
    ( ~ r1_tarski(X0,k1_tops_1(sK0,sK1))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),X0)
    | X0 = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_21541,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_6588])).

cnf(c_111019,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_39155,c_25,c_24,c_579,c_1447,c_1450,c_1713,c_1730,c_21541])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_622,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_25])).

cnf(c_623,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_622])).

cnf(c_1320,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_623])).

cnf(c_2919,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,X0)),k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1315,c_1320])).

cnf(c_7256,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_1326,c_2919])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_670,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_25])).

cnf(c_671,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_670])).

cnf(c_1316,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_671])).

cnf(c_1693,plain,
    ( k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1326,c_1316])).

cnf(c_7277,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_7256,c_1693])).

cnf(c_111076,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_111019,c_7277])).

cnf(c_2918,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1326,c_1320])).

cnf(c_111087,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_111076,c_2918])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X0))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_504,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X0))) = k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_26])).

cnf(c_505,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_504])).

cnf(c_509,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_505,c_25])).

cnf(c_1324,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_509])).

cnf(c_2587,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0)))) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1315,c_1324])).

cnf(c_4513,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1326,c_2587])).

cnf(c_13,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_423,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_26])).

cnf(c_424,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_423])).

cnf(c_428,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k2_pre_topc(sK0,X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_424,c_25])).

cnf(c_429,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_428])).

cnf(c_20,plain,
    ( ~ v3_tops_1(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_21,plain,
    ( v3_tops_1(k2_tops_1(X0,X1),X0)
    | ~ v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_329,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(X2,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | X3 != X1
    | k2_tops_1(X3,X2) != X0
    | k2_tops_1(X1,X0) = X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_21])).

cnf(c_330,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(k2_tops_1(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_tops_1(X1,k2_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(unflattening,[status(thm)],[c_329])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_334,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(k2_tops_1(X1,X0),X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_tops_1(X1,k2_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_330,c_11])).

cnf(c_335,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(k2_tops_1(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_tops_1(X1,k2_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(renaming,[status(thm)],[c_334])).

cnf(c_12,plain,
    ( v4_pre_topc(k2_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_352,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_tops_1(X1,k2_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_335,c_12])).

cnf(c_459,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_tops_1(X1,k2_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_352,c_26])).

cnf(c_460,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,k2_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_459])).

cnf(c_464,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(X0,sK0)
    | k2_tops_1(sK0,k2_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_460,c_25])).

cnf(c_465,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,k2_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(renaming,[status(thm)],[c_464])).

cnf(c_847,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,k2_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | k2_pre_topc(sK0,X1) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_429,c_465])).

cnf(c_848,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_847])).

cnf(c_540,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,k2_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | k2_pre_topc(sK0,X1) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_429,c_465])).

cnf(c_541,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_540])).

cnf(c_850,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_848,c_541,c_683])).

cnf(c_1314,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_850])).

cnf(c_3123,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_1326,c_1314])).

cnf(c_4530,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4513,c_3123])).

cnf(c_111548,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_111087,c_4530])).

cnf(c_22,negated_conjecture,
    ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f84])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_111548,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:52:53 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 27.39/3.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.39/3.99  
% 27.39/3.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.39/3.99  
% 27.39/3.99  ------  iProver source info
% 27.39/3.99  
% 27.39/3.99  git: date: 2020-06-30 10:37:57 +0100
% 27.39/3.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.39/3.99  git: non_committed_changes: false
% 27.39/3.99  git: last_make_outside_of_git: false
% 27.39/3.99  
% 27.39/3.99  ------ 
% 27.39/3.99  
% 27.39/3.99  ------ Input Options
% 27.39/3.99  
% 27.39/3.99  --out_options                           all
% 27.39/3.99  --tptp_safe_out                         true
% 27.39/3.99  --problem_path                          ""
% 27.39/3.99  --include_path                          ""
% 27.39/3.99  --clausifier                            res/vclausify_rel
% 27.39/3.99  --clausifier_options                    --mode clausify
% 27.39/3.99  --stdin                                 false
% 27.39/3.99  --stats_out                             all
% 27.39/3.99  
% 27.39/3.99  ------ General Options
% 27.39/3.99  
% 27.39/3.99  --fof                                   false
% 27.39/3.99  --time_out_real                         305.
% 27.39/3.99  --time_out_virtual                      -1.
% 27.39/3.99  --symbol_type_check                     false
% 27.39/3.99  --clausify_out                          false
% 27.39/3.99  --sig_cnt_out                           false
% 27.39/3.99  --trig_cnt_out                          false
% 27.39/3.99  --trig_cnt_out_tolerance                1.
% 27.39/3.99  --trig_cnt_out_sk_spl                   false
% 27.39/3.99  --abstr_cl_out                          false
% 27.39/3.99  
% 27.39/3.99  ------ Global Options
% 27.39/3.99  
% 27.39/3.99  --schedule                              default
% 27.39/3.99  --add_important_lit                     false
% 27.39/3.99  --prop_solver_per_cl                    1000
% 27.39/3.99  --min_unsat_core                        false
% 27.39/3.99  --soft_assumptions                      false
% 27.39/3.99  --soft_lemma_size                       3
% 27.39/3.99  --prop_impl_unit_size                   0
% 27.39/3.99  --prop_impl_unit                        []
% 27.39/3.99  --share_sel_clauses                     true
% 27.39/3.99  --reset_solvers                         false
% 27.39/3.99  --bc_imp_inh                            [conj_cone]
% 27.39/3.99  --conj_cone_tolerance                   3.
% 27.39/3.99  --extra_neg_conj                        none
% 27.39/3.99  --large_theory_mode                     true
% 27.39/3.99  --prolific_symb_bound                   200
% 27.39/3.99  --lt_threshold                          2000
% 27.39/3.99  --clause_weak_htbl                      true
% 27.39/3.99  --gc_record_bc_elim                     false
% 27.39/3.99  
% 27.39/3.99  ------ Preprocessing Options
% 27.39/3.99  
% 27.39/3.99  --preprocessing_flag                    true
% 27.39/3.99  --time_out_prep_mult                    0.1
% 27.39/3.99  --splitting_mode                        input
% 27.39/3.99  --splitting_grd                         true
% 27.39/3.99  --splitting_cvd                         false
% 27.39/3.99  --splitting_cvd_svl                     false
% 27.39/3.99  --splitting_nvd                         32
% 27.39/3.99  --sub_typing                            true
% 27.39/3.99  --prep_gs_sim                           true
% 27.39/3.99  --prep_unflatten                        true
% 27.39/3.99  --prep_res_sim                          true
% 27.39/3.99  --prep_upred                            true
% 27.39/3.99  --prep_sem_filter                       exhaustive
% 27.39/3.99  --prep_sem_filter_out                   false
% 27.39/3.99  --pred_elim                             true
% 27.39/3.99  --res_sim_input                         true
% 27.39/3.99  --eq_ax_congr_red                       true
% 27.39/3.99  --pure_diseq_elim                       true
% 27.39/3.99  --brand_transform                       false
% 27.39/3.99  --non_eq_to_eq                          false
% 27.39/3.99  --prep_def_merge                        true
% 27.39/3.99  --prep_def_merge_prop_impl              false
% 27.39/3.99  --prep_def_merge_mbd                    true
% 27.39/3.99  --prep_def_merge_tr_red                 false
% 27.39/3.99  --prep_def_merge_tr_cl                  false
% 27.39/3.99  --smt_preprocessing                     true
% 27.39/3.99  --smt_ac_axioms                         fast
% 27.39/3.99  --preprocessed_out                      false
% 27.39/3.99  --preprocessed_stats                    false
% 27.39/3.99  
% 27.39/3.99  ------ Abstraction refinement Options
% 27.39/3.99  
% 27.39/3.99  --abstr_ref                             []
% 27.39/3.99  --abstr_ref_prep                        false
% 27.39/3.99  --abstr_ref_until_sat                   false
% 27.39/3.99  --abstr_ref_sig_restrict                funpre
% 27.39/3.99  --abstr_ref_af_restrict_to_split_sk     false
% 27.39/3.99  --abstr_ref_under                       []
% 27.39/3.99  
% 27.39/3.99  ------ SAT Options
% 27.39/3.99  
% 27.39/3.99  --sat_mode                              false
% 27.39/3.99  --sat_fm_restart_options                ""
% 27.39/3.99  --sat_gr_def                            false
% 27.39/3.99  --sat_epr_types                         true
% 27.39/3.99  --sat_non_cyclic_types                  false
% 27.39/3.99  --sat_finite_models                     false
% 27.39/3.99  --sat_fm_lemmas                         false
% 27.39/3.99  --sat_fm_prep                           false
% 27.39/3.99  --sat_fm_uc_incr                        true
% 27.39/3.99  --sat_out_model                         small
% 27.39/3.99  --sat_out_clauses                       false
% 27.39/3.99  
% 27.39/3.99  ------ QBF Options
% 27.39/3.99  
% 27.39/3.99  --qbf_mode                              false
% 27.39/3.99  --qbf_elim_univ                         false
% 27.39/3.99  --qbf_dom_inst                          none
% 27.39/3.99  --qbf_dom_pre_inst                      false
% 27.39/3.99  --qbf_sk_in                             false
% 27.39/3.99  --qbf_pred_elim                         true
% 27.39/3.99  --qbf_split                             512
% 27.39/3.99  
% 27.39/3.99  ------ BMC1 Options
% 27.39/3.99  
% 27.39/3.99  --bmc1_incremental                      false
% 27.39/3.99  --bmc1_axioms                           reachable_all
% 27.39/3.99  --bmc1_min_bound                        0
% 27.39/3.99  --bmc1_max_bound                        -1
% 27.39/3.99  --bmc1_max_bound_default                -1
% 27.39/3.99  --bmc1_symbol_reachability              true
% 27.39/3.99  --bmc1_property_lemmas                  false
% 27.39/3.99  --bmc1_k_induction                      false
% 27.39/3.99  --bmc1_non_equiv_states                 false
% 27.39/3.99  --bmc1_deadlock                         false
% 27.39/3.99  --bmc1_ucm                              false
% 27.39/3.99  --bmc1_add_unsat_core                   none
% 27.39/3.99  --bmc1_unsat_core_children              false
% 27.39/3.99  --bmc1_unsat_core_extrapolate_axioms    false
% 27.39/3.99  --bmc1_out_stat                         full
% 27.39/3.99  --bmc1_ground_init                      false
% 27.39/3.99  --bmc1_pre_inst_next_state              false
% 27.39/3.99  --bmc1_pre_inst_state                   false
% 27.39/3.99  --bmc1_pre_inst_reach_state             false
% 27.39/3.99  --bmc1_out_unsat_core                   false
% 27.39/3.99  --bmc1_aig_witness_out                  false
% 27.39/3.99  --bmc1_verbose                          false
% 27.39/3.99  --bmc1_dump_clauses_tptp                false
% 27.39/3.99  --bmc1_dump_unsat_core_tptp             false
% 27.39/3.99  --bmc1_dump_file                        -
% 27.39/3.99  --bmc1_ucm_expand_uc_limit              128
% 27.39/3.99  --bmc1_ucm_n_expand_iterations          6
% 27.39/3.99  --bmc1_ucm_extend_mode                  1
% 27.39/3.99  --bmc1_ucm_init_mode                    2
% 27.39/3.99  --bmc1_ucm_cone_mode                    none
% 27.39/3.99  --bmc1_ucm_reduced_relation_type        0
% 27.39/3.99  --bmc1_ucm_relax_model                  4
% 27.39/3.99  --bmc1_ucm_full_tr_after_sat            true
% 27.39/3.99  --bmc1_ucm_expand_neg_assumptions       false
% 27.39/3.99  --bmc1_ucm_layered_model                none
% 27.39/3.99  --bmc1_ucm_max_lemma_size               10
% 27.39/3.99  
% 27.39/3.99  ------ AIG Options
% 27.39/3.99  
% 27.39/3.99  --aig_mode                              false
% 27.39/3.99  
% 27.39/3.99  ------ Instantiation Options
% 27.39/3.99  
% 27.39/3.99  --instantiation_flag                    true
% 27.39/3.99  --inst_sos_flag                         false
% 27.39/3.99  --inst_sos_phase                        true
% 27.39/3.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.39/3.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.39/3.99  --inst_lit_sel_side                     num_symb
% 27.39/3.99  --inst_solver_per_active                1400
% 27.39/3.99  --inst_solver_calls_frac                1.
% 27.39/3.99  --inst_passive_queue_type               priority_queues
% 27.39/3.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.39/3.99  --inst_passive_queues_freq              [25;2]
% 27.39/3.99  --inst_dismatching                      true
% 27.39/3.99  --inst_eager_unprocessed_to_passive     true
% 27.39/3.99  --inst_prop_sim_given                   true
% 27.39/3.99  --inst_prop_sim_new                     false
% 27.39/3.99  --inst_subs_new                         false
% 27.39/3.99  --inst_eq_res_simp                      false
% 27.39/3.99  --inst_subs_given                       false
% 27.39/3.99  --inst_orphan_elimination               true
% 27.39/3.99  --inst_learning_loop_flag               true
% 27.39/3.99  --inst_learning_start                   3000
% 27.39/3.99  --inst_learning_factor                  2
% 27.39/3.99  --inst_start_prop_sim_after_learn       3
% 27.39/3.99  --inst_sel_renew                        solver
% 27.39/3.99  --inst_lit_activity_flag                true
% 27.39/3.99  --inst_restr_to_given                   false
% 27.39/3.99  --inst_activity_threshold               500
% 27.39/3.99  --inst_out_proof                        true
% 27.39/3.99  
% 27.39/3.99  ------ Resolution Options
% 27.39/3.99  
% 27.39/3.99  --resolution_flag                       true
% 27.39/3.99  --res_lit_sel                           adaptive
% 27.39/3.99  --res_lit_sel_side                      none
% 27.39/3.99  --res_ordering                          kbo
% 27.39/3.99  --res_to_prop_solver                    active
% 27.39/3.99  --res_prop_simpl_new                    false
% 27.39/3.99  --res_prop_simpl_given                  true
% 27.39/3.99  --res_passive_queue_type                priority_queues
% 27.39/3.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.39/3.99  --res_passive_queues_freq               [15;5]
% 27.39/3.99  --res_forward_subs                      full
% 27.39/3.99  --res_backward_subs                     full
% 27.39/3.99  --res_forward_subs_resolution           true
% 27.39/3.99  --res_backward_subs_resolution          true
% 27.39/3.99  --res_orphan_elimination                true
% 27.39/3.99  --res_time_limit                        2.
% 27.39/3.99  --res_out_proof                         true
% 27.39/3.99  
% 27.39/3.99  ------ Superposition Options
% 27.39/3.99  
% 27.39/3.99  --superposition_flag                    true
% 27.39/3.99  --sup_passive_queue_type                priority_queues
% 27.39/3.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.39/3.99  --sup_passive_queues_freq               [8;1;4]
% 27.39/3.99  --demod_completeness_check              fast
% 27.39/3.99  --demod_use_ground                      true
% 27.39/3.99  --sup_to_prop_solver                    passive
% 27.39/3.99  --sup_prop_simpl_new                    true
% 27.39/3.99  --sup_prop_simpl_given                  true
% 27.39/3.99  --sup_fun_splitting                     false
% 27.39/3.99  --sup_smt_interval                      50000
% 27.39/3.99  
% 27.39/3.99  ------ Superposition Simplification Setup
% 27.39/3.99  
% 27.39/3.99  --sup_indices_passive                   []
% 27.39/3.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.39/3.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.39/3.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.39/3.99  --sup_full_triv                         [TrivRules;PropSubs]
% 27.39/3.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.39/3.99  --sup_full_bw                           [BwDemod]
% 27.39/3.99  --sup_immed_triv                        [TrivRules]
% 27.39/3.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.39/3.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.39/3.99  --sup_immed_bw_main                     []
% 27.39/3.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.39/3.99  --sup_input_triv                        [Unflattening;TrivRules]
% 27.39/3.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.39/3.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.39/3.99  
% 27.39/3.99  ------ Combination Options
% 27.39/3.99  
% 27.39/3.99  --comb_res_mult                         3
% 27.39/3.99  --comb_sup_mult                         2
% 27.39/3.99  --comb_inst_mult                        10
% 27.39/3.99  
% 27.39/3.99  ------ Debug Options
% 27.39/3.99  
% 27.39/3.99  --dbg_backtrace                         false
% 27.39/3.99  --dbg_dump_prop_clauses                 false
% 27.39/3.99  --dbg_dump_prop_clauses_file            -
% 27.39/3.99  --dbg_out_stat                          false
% 27.39/3.99  ------ Parsing...
% 27.39/3.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.39/3.99  
% 27.39/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 27.39/3.99  
% 27.39/3.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.39/3.99  
% 27.39/3.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.39/3.99  ------ Proving...
% 27.39/3.99  ------ Problem Properties 
% 27.39/3.99  
% 27.39/3.99  
% 27.39/3.99  clauses                                 18
% 27.39/3.99  conjectures                             2
% 27.39/3.99  EPR                                     2
% 27.39/3.99  Horn                                    18
% 27.39/3.99  unary                                   5
% 27.39/3.99  binary                                  10
% 27.39/3.99  lits                                    36
% 27.39/3.99  lits eq                                 8
% 27.39/3.99  fd_pure                                 0
% 27.39/3.99  fd_pseudo                               0
% 27.39/3.99  fd_cond                                 0
% 27.39/3.99  fd_pseudo_cond                          1
% 27.39/3.99  AC symbols                              0
% 27.39/3.99  
% 27.39/3.99  ------ Schedule dynamic 5 is on 
% 27.39/3.99  
% 27.39/3.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.39/3.99  
% 27.39/3.99  
% 27.39/3.99  ------ 
% 27.39/3.99  Current options:
% 27.39/3.99  ------ 
% 27.39/3.99  
% 27.39/3.99  ------ Input Options
% 27.39/3.99  
% 27.39/3.99  --out_options                           all
% 27.39/3.99  --tptp_safe_out                         true
% 27.39/3.99  --problem_path                          ""
% 27.39/3.99  --include_path                          ""
% 27.39/3.99  --clausifier                            res/vclausify_rel
% 27.39/3.99  --clausifier_options                    --mode clausify
% 27.39/3.99  --stdin                                 false
% 27.39/3.99  --stats_out                             all
% 27.39/3.99  
% 27.39/3.99  ------ General Options
% 27.39/3.99  
% 27.39/3.99  --fof                                   false
% 27.39/3.99  --time_out_real                         305.
% 27.39/3.99  --time_out_virtual                      -1.
% 27.39/3.99  --symbol_type_check                     false
% 27.39/3.99  --clausify_out                          false
% 27.39/3.99  --sig_cnt_out                           false
% 27.39/3.99  --trig_cnt_out                          false
% 27.39/3.99  --trig_cnt_out_tolerance                1.
% 27.39/3.99  --trig_cnt_out_sk_spl                   false
% 27.39/3.99  --abstr_cl_out                          false
% 27.39/3.99  
% 27.39/3.99  ------ Global Options
% 27.39/3.99  
% 27.39/3.99  --schedule                              default
% 27.39/3.99  --add_important_lit                     false
% 27.39/3.99  --prop_solver_per_cl                    1000
% 27.39/3.99  --min_unsat_core                        false
% 27.39/3.99  --soft_assumptions                      false
% 27.39/3.99  --soft_lemma_size                       3
% 27.39/3.99  --prop_impl_unit_size                   0
% 27.39/3.99  --prop_impl_unit                        []
% 27.39/3.99  --share_sel_clauses                     true
% 27.39/3.99  --reset_solvers                         false
% 27.39/3.99  --bc_imp_inh                            [conj_cone]
% 27.39/3.99  --conj_cone_tolerance                   3.
% 27.39/3.99  --extra_neg_conj                        none
% 27.39/3.99  --large_theory_mode                     true
% 27.39/3.99  --prolific_symb_bound                   200
% 27.39/3.99  --lt_threshold                          2000
% 27.39/3.99  --clause_weak_htbl                      true
% 27.39/3.99  --gc_record_bc_elim                     false
% 27.39/3.99  
% 27.39/3.99  ------ Preprocessing Options
% 27.39/3.99  
% 27.39/3.99  --preprocessing_flag                    true
% 27.39/3.99  --time_out_prep_mult                    0.1
% 27.39/3.99  --splitting_mode                        input
% 27.39/3.99  --splitting_grd                         true
% 27.39/3.99  --splitting_cvd                         false
% 27.39/3.99  --splitting_cvd_svl                     false
% 27.39/3.99  --splitting_nvd                         32
% 27.39/3.99  --sub_typing                            true
% 27.39/3.99  --prep_gs_sim                           true
% 27.39/3.99  --prep_unflatten                        true
% 27.39/3.99  --prep_res_sim                          true
% 27.39/3.99  --prep_upred                            true
% 27.39/3.99  --prep_sem_filter                       exhaustive
% 27.39/3.99  --prep_sem_filter_out                   false
% 27.39/3.99  --pred_elim                             true
% 27.39/3.99  --res_sim_input                         true
% 27.39/3.99  --eq_ax_congr_red                       true
% 27.39/3.99  --pure_diseq_elim                       true
% 27.39/3.99  --brand_transform                       false
% 27.39/3.99  --non_eq_to_eq                          false
% 27.39/3.99  --prep_def_merge                        true
% 27.39/3.99  --prep_def_merge_prop_impl              false
% 27.39/3.99  --prep_def_merge_mbd                    true
% 27.39/3.99  --prep_def_merge_tr_red                 false
% 27.39/3.99  --prep_def_merge_tr_cl                  false
% 27.39/3.99  --smt_preprocessing                     true
% 27.39/3.99  --smt_ac_axioms                         fast
% 27.39/3.99  --preprocessed_out                      false
% 27.39/3.99  --preprocessed_stats                    false
% 27.39/3.99  
% 27.39/3.99  ------ Abstraction refinement Options
% 27.39/3.99  
% 27.39/3.99  --abstr_ref                             []
% 27.39/3.99  --abstr_ref_prep                        false
% 27.39/3.99  --abstr_ref_until_sat                   false
% 27.39/3.99  --abstr_ref_sig_restrict                funpre
% 27.39/3.99  --abstr_ref_af_restrict_to_split_sk     false
% 27.39/3.99  --abstr_ref_under                       []
% 27.39/3.99  
% 27.39/3.99  ------ SAT Options
% 27.39/3.99  
% 27.39/3.99  --sat_mode                              false
% 27.39/3.99  --sat_fm_restart_options                ""
% 27.39/3.99  --sat_gr_def                            false
% 27.39/3.99  --sat_epr_types                         true
% 27.39/3.99  --sat_non_cyclic_types                  false
% 27.39/3.99  --sat_finite_models                     false
% 27.39/3.99  --sat_fm_lemmas                         false
% 27.39/3.99  --sat_fm_prep                           false
% 27.39/3.99  --sat_fm_uc_incr                        true
% 27.39/3.99  --sat_out_model                         small
% 27.39/3.99  --sat_out_clauses                       false
% 27.39/3.99  
% 27.39/3.99  ------ QBF Options
% 27.39/3.99  
% 27.39/3.99  --qbf_mode                              false
% 27.39/3.99  --qbf_elim_univ                         false
% 27.39/3.99  --qbf_dom_inst                          none
% 27.39/3.99  --qbf_dom_pre_inst                      false
% 27.39/3.99  --qbf_sk_in                             false
% 27.39/3.99  --qbf_pred_elim                         true
% 27.39/3.99  --qbf_split                             512
% 27.39/3.99  
% 27.39/3.99  ------ BMC1 Options
% 27.39/3.99  
% 27.39/3.99  --bmc1_incremental                      false
% 27.39/3.99  --bmc1_axioms                           reachable_all
% 27.39/3.99  --bmc1_min_bound                        0
% 27.39/3.99  --bmc1_max_bound                        -1
% 27.39/3.99  --bmc1_max_bound_default                -1
% 27.39/3.99  --bmc1_symbol_reachability              true
% 27.39/3.99  --bmc1_property_lemmas                  false
% 27.39/3.99  --bmc1_k_induction                      false
% 27.39/3.99  --bmc1_non_equiv_states                 false
% 27.39/3.99  --bmc1_deadlock                         false
% 27.39/3.99  --bmc1_ucm                              false
% 27.39/3.99  --bmc1_add_unsat_core                   none
% 27.39/3.99  --bmc1_unsat_core_children              false
% 27.39/3.99  --bmc1_unsat_core_extrapolate_axioms    false
% 27.39/3.99  --bmc1_out_stat                         full
% 27.39/3.99  --bmc1_ground_init                      false
% 27.39/3.99  --bmc1_pre_inst_next_state              false
% 27.39/3.99  --bmc1_pre_inst_state                   false
% 27.39/3.99  --bmc1_pre_inst_reach_state             false
% 27.39/3.99  --bmc1_out_unsat_core                   false
% 27.39/3.99  --bmc1_aig_witness_out                  false
% 27.39/3.99  --bmc1_verbose                          false
% 27.39/3.99  --bmc1_dump_clauses_tptp                false
% 27.39/3.99  --bmc1_dump_unsat_core_tptp             false
% 27.39/3.99  --bmc1_dump_file                        -
% 27.39/3.99  --bmc1_ucm_expand_uc_limit              128
% 27.39/3.99  --bmc1_ucm_n_expand_iterations          6
% 27.39/3.99  --bmc1_ucm_extend_mode                  1
% 27.39/3.99  --bmc1_ucm_init_mode                    2
% 27.39/3.99  --bmc1_ucm_cone_mode                    none
% 27.39/3.99  --bmc1_ucm_reduced_relation_type        0
% 27.39/3.99  --bmc1_ucm_relax_model                  4
% 27.39/3.99  --bmc1_ucm_full_tr_after_sat            true
% 27.39/3.99  --bmc1_ucm_expand_neg_assumptions       false
% 27.39/3.99  --bmc1_ucm_layered_model                none
% 27.39/3.99  --bmc1_ucm_max_lemma_size               10
% 27.39/3.99  
% 27.39/3.99  ------ AIG Options
% 27.39/3.99  
% 27.39/3.99  --aig_mode                              false
% 27.39/3.99  
% 27.39/3.99  ------ Instantiation Options
% 27.39/3.99  
% 27.39/3.99  --instantiation_flag                    true
% 27.39/3.99  --inst_sos_flag                         false
% 27.39/3.99  --inst_sos_phase                        true
% 27.39/3.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.39/3.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.39/3.99  --inst_lit_sel_side                     none
% 27.39/3.99  --inst_solver_per_active                1400
% 27.39/3.99  --inst_solver_calls_frac                1.
% 27.39/3.99  --inst_passive_queue_type               priority_queues
% 27.39/3.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.39/3.99  --inst_passive_queues_freq              [25;2]
% 27.39/3.99  --inst_dismatching                      true
% 27.39/3.99  --inst_eager_unprocessed_to_passive     true
% 27.39/3.99  --inst_prop_sim_given                   true
% 27.39/3.99  --inst_prop_sim_new                     false
% 27.39/3.99  --inst_subs_new                         false
% 27.39/3.99  --inst_eq_res_simp                      false
% 27.39/3.99  --inst_subs_given                       false
% 27.39/3.99  --inst_orphan_elimination               true
% 27.39/3.99  --inst_learning_loop_flag               true
% 27.39/3.99  --inst_learning_start                   3000
% 27.39/3.99  --inst_learning_factor                  2
% 27.39/3.99  --inst_start_prop_sim_after_learn       3
% 27.39/3.99  --inst_sel_renew                        solver
% 27.39/3.99  --inst_lit_activity_flag                true
% 27.39/3.99  --inst_restr_to_given                   false
% 27.39/3.99  --inst_activity_threshold               500
% 27.39/3.99  --inst_out_proof                        true
% 27.39/3.99  
% 27.39/3.99  ------ Resolution Options
% 27.39/3.99  
% 27.39/3.99  --resolution_flag                       false
% 27.39/3.99  --res_lit_sel                           adaptive
% 27.39/3.99  --res_lit_sel_side                      none
% 27.39/3.99  --res_ordering                          kbo
% 27.39/3.99  --res_to_prop_solver                    active
% 27.39/3.99  --res_prop_simpl_new                    false
% 27.39/3.99  --res_prop_simpl_given                  true
% 27.39/3.99  --res_passive_queue_type                priority_queues
% 27.39/3.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.39/3.99  --res_passive_queues_freq               [15;5]
% 27.39/3.99  --res_forward_subs                      full
% 27.39/3.99  --res_backward_subs                     full
% 27.39/3.99  --res_forward_subs_resolution           true
% 27.39/3.99  --res_backward_subs_resolution          true
% 27.39/3.99  --res_orphan_elimination                true
% 27.39/3.99  --res_time_limit                        2.
% 27.39/3.99  --res_out_proof                         true
% 27.39/3.99  
% 27.39/3.99  ------ Superposition Options
% 27.39/3.99  
% 27.39/3.99  --superposition_flag                    true
% 27.39/3.99  --sup_passive_queue_type                priority_queues
% 27.39/3.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.39/3.99  --sup_passive_queues_freq               [8;1;4]
% 27.39/3.99  --demod_completeness_check              fast
% 27.39/3.99  --demod_use_ground                      true
% 27.39/3.99  --sup_to_prop_solver                    passive
% 27.39/3.99  --sup_prop_simpl_new                    true
% 27.39/3.99  --sup_prop_simpl_given                  true
% 27.39/3.99  --sup_fun_splitting                     false
% 27.39/3.99  --sup_smt_interval                      50000
% 27.39/3.99  
% 27.39/3.99  ------ Superposition Simplification Setup
% 27.39/3.99  
% 27.39/3.99  --sup_indices_passive                   []
% 27.39/3.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.39/3.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.39/3.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 27.39/3.99  --sup_full_triv                         [TrivRules;PropSubs]
% 27.39/3.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.39/3.99  --sup_full_bw                           [BwDemod]
% 27.39/3.99  --sup_immed_triv                        [TrivRules]
% 27.39/3.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.39/3.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.39/3.99  --sup_immed_bw_main                     []
% 27.39/3.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.39/3.99  --sup_input_triv                        [Unflattening;TrivRules]
% 27.39/3.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 27.39/3.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 27.39/3.99  
% 27.39/3.99  ------ Combination Options
% 27.39/3.99  
% 27.39/3.99  --comb_res_mult                         3
% 27.39/3.99  --comb_sup_mult                         2
% 27.39/3.99  --comb_inst_mult                        10
% 27.39/3.99  
% 27.39/3.99  ------ Debug Options
% 27.39/3.99  
% 27.39/3.99  --dbg_backtrace                         false
% 27.39/3.99  --dbg_dump_prop_clauses                 false
% 27.39/3.99  --dbg_dump_prop_clauses_file            -
% 27.39/3.99  --dbg_out_stat                          false
% 27.39/3.99  
% 27.39/3.99  
% 27.39/3.99  
% 27.39/3.99  
% 27.39/3.99  ------ Proving...
% 27.39/3.99  
% 27.39/3.99  
% 27.39/3.99  % SZS status Theorem for theBenchmark.p
% 27.39/3.99  
% 27.39/3.99  % SZS output start CNFRefutation for theBenchmark.p
% 27.39/3.99  
% 27.39/3.99  fof(f6,axiom,(
% 27.39/3.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 27.39/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.39/3.99  
% 27.39/3.99  fof(f26,plain,(
% 27.39/3.99    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.39/3.99    inference(ennf_transformation,[],[f6])).
% 27.39/3.99  
% 27.39/3.99  fof(f52,plain,(
% 27.39/3.99    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.39/3.99    inference(nnf_transformation,[],[f26])).
% 27.39/3.99  
% 27.39/3.99  fof(f53,plain,(
% 27.39/3.99    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.39/3.99    inference(flattening,[],[f52])).
% 27.39/3.99  
% 27.39/3.99  fof(f65,plain,(
% 27.39/3.99    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.39/3.99    inference(cnf_transformation,[],[f53])).
% 27.39/3.99  
% 27.39/3.99  fof(f18,conjecture,(
% 27.39/3.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) => k1_tops_1(X0,k2_tops_1(X0,X1)) = k1_xboole_0)))),
% 27.39/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.39/3.99  
% 27.39/3.99  fof(f19,negated_conjecture,(
% 27.39/3.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) => k1_tops_1(X0,k2_tops_1(X0,X1)) = k1_xboole_0)))),
% 27.39/3.99    inference(negated_conjecture,[],[f18])).
% 27.39/3.99  
% 27.39/3.99  fof(f48,plain,(
% 27.39/3.99    ? [X0] : (? [X1] : ((k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0 & v4_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 27.39/3.99    inference(ennf_transformation,[],[f19])).
% 27.39/3.99  
% 27.39/3.99  fof(f49,plain,(
% 27.39/3.99    ? [X0] : (? [X1] : (k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0 & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 27.39/3.99    inference(flattening,[],[f48])).
% 27.39/3.99  
% 27.39/3.99  fof(f56,plain,(
% 27.39/3.99    ( ! [X0] : (? [X1] : (k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0 & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (k1_tops_1(X0,k2_tops_1(X0,sK1)) != k1_xboole_0 & v4_tops_1(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 27.39/3.99    introduced(choice_axiom,[])).
% 27.39/3.99  
% 27.39/3.99  fof(f55,plain,(
% 27.39/3.99    ? [X0] : (? [X1] : (k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0 & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (k1_tops_1(sK0,k2_tops_1(sK0,X1)) != k1_xboole_0 & v4_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 27.39/3.99    introduced(choice_axiom,[])).
% 27.39/3.99  
% 27.39/3.99  fof(f57,plain,(
% 27.39/3.99    (k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0 & v4_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 27.39/3.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f49,f56,f55])).
% 27.39/3.99  
% 27.39/3.99  fof(f83,plain,(
% 27.39/3.99    v4_tops_1(sK1,sK0)),
% 27.39/3.99    inference(cnf_transformation,[],[f57])).
% 27.39/3.99  
% 27.39/3.99  fof(f81,plain,(
% 27.39/3.99    l1_pre_topc(sK0)),
% 27.39/3.99    inference(cnf_transformation,[],[f57])).
% 27.39/3.99  
% 27.39/3.99  fof(f82,plain,(
% 27.39/3.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 27.39/3.99    inference(cnf_transformation,[],[f57])).
% 27.39/3.99  
% 27.39/3.99  fof(f3,axiom,(
% 27.39/3.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 27.39/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.39/3.99  
% 27.39/3.99  fof(f21,plain,(
% 27.39/3.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 27.39/3.99    inference(ennf_transformation,[],[f3])).
% 27.39/3.99  
% 27.39/3.99  fof(f22,plain,(
% 27.39/3.99    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 27.39/3.99    inference(flattening,[],[f21])).
% 27.39/3.99  
% 27.39/3.99  fof(f62,plain,(
% 27.39/3.99    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.39/3.99    inference(cnf_transformation,[],[f22])).
% 27.39/3.99  
% 27.39/3.99  fof(f11,axiom,(
% 27.39/3.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 27.39/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.39/3.99  
% 27.39/3.99  fof(f35,plain,(
% 27.39/3.99    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 27.39/3.99    inference(ennf_transformation,[],[f11])).
% 27.39/3.99  
% 27.39/3.99  fof(f36,plain,(
% 27.39/3.99    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.39/3.99    inference(flattening,[],[f35])).
% 27.39/3.99  
% 27.39/3.99  fof(f72,plain,(
% 27.39/3.99    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.39/3.99    inference(cnf_transformation,[],[f36])).
% 27.39/3.99  
% 27.39/3.99  fof(f15,axiom,(
% 27.39/3.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 27.39/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.39/3.99  
% 27.39/3.99  fof(f42,plain,(
% 27.39/3.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.39/3.99    inference(ennf_transformation,[],[f15])).
% 27.39/3.99  
% 27.39/3.99  fof(f43,plain,(
% 27.39/3.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.39/3.99    inference(flattening,[],[f42])).
% 27.39/3.99  
% 27.39/3.99  fof(f76,plain,(
% 27.39/3.99    ( ! [X2,X0,X1] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.39/3.99    inference(cnf_transformation,[],[f43])).
% 27.39/3.99  
% 27.39/3.99  fof(f7,axiom,(
% 27.39/3.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 27.39/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.39/3.99  
% 27.39/3.99  fof(f27,plain,(
% 27.39/3.99    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 27.39/3.99    inference(ennf_transformation,[],[f7])).
% 27.39/3.99  
% 27.39/3.99  fof(f28,plain,(
% 27.39/3.99    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 27.39/3.99    inference(flattening,[],[f27])).
% 27.39/3.99  
% 27.39/3.99  fof(f68,plain,(
% 27.39/3.99    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.39/3.99    inference(cnf_transformation,[],[f28])).
% 27.39/3.99  
% 27.39/3.99  fof(f80,plain,(
% 27.39/3.99    v2_pre_topc(sK0)),
% 27.39/3.99    inference(cnf_transformation,[],[f57])).
% 27.39/3.99  
% 27.39/3.99  fof(f1,axiom,(
% 27.39/3.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 27.39/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.39/3.99  
% 27.39/3.99  fof(f50,plain,(
% 27.39/3.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.39/3.99    inference(nnf_transformation,[],[f1])).
% 27.39/3.99  
% 27.39/3.99  fof(f51,plain,(
% 27.39/3.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.39/3.99    inference(flattening,[],[f50])).
% 27.39/3.99  
% 27.39/3.99  fof(f60,plain,(
% 27.39/3.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 27.39/3.99    inference(cnf_transformation,[],[f51])).
% 27.39/3.99  
% 27.39/3.99  fof(f5,axiom,(
% 27.39/3.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 27.39/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.39/3.99  
% 27.39/3.99  fof(f25,plain,(
% 27.39/3.99    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.39/3.99    inference(ennf_transformation,[],[f5])).
% 27.39/3.99  
% 27.39/3.99  fof(f64,plain,(
% 27.39/3.99    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.39/3.99    inference(cnf_transformation,[],[f25])).
% 27.39/3.99  
% 27.39/3.99  fof(f14,axiom,(
% 27.39/3.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 27.39/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.39/3.99  
% 27.39/3.99  fof(f40,plain,(
% 27.39/3.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.39/3.99    inference(ennf_transformation,[],[f14])).
% 27.39/3.99  
% 27.39/3.99  fof(f41,plain,(
% 27.39/3.99    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.39/3.99    inference(flattening,[],[f40])).
% 27.39/3.99  
% 27.39/3.99  fof(f75,plain,(
% 27.39/3.99    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.39/3.99    inference(cnf_transformation,[],[f41])).
% 27.39/3.99  
% 27.39/3.99  fof(f12,axiom,(
% 27.39/3.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 27.39/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.39/3.99  
% 27.39/3.99  fof(f37,plain,(
% 27.39/3.99    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.39/3.99    inference(ennf_transformation,[],[f12])).
% 27.39/3.99  
% 27.39/3.99  fof(f73,plain,(
% 27.39/3.99    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.39/3.99    inference(cnf_transformation,[],[f37])).
% 27.39/3.99  
% 27.39/3.99  fof(f4,axiom,(
% 27.39/3.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)))),
% 27.39/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.39/3.99  
% 27.39/3.99  fof(f23,plain,(
% 27.39/3.99    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 27.39/3.99    inference(ennf_transformation,[],[f4])).
% 27.39/3.99  
% 27.39/3.99  fof(f24,plain,(
% 27.39/3.99    ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 27.39/3.99    inference(flattening,[],[f23])).
% 27.39/3.99  
% 27.39/3.99  fof(f63,plain,(
% 27.39/3.99    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.39/3.99    inference(cnf_transformation,[],[f24])).
% 27.39/3.99  
% 27.39/3.99  fof(f13,axiom,(
% 27.39/3.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0))),
% 27.39/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.39/3.99  
% 27.39/3.99  fof(f38,plain,(
% 27.39/3.99    ! [X0] : (! [X1] : (k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 27.39/3.99    inference(ennf_transformation,[],[f13])).
% 27.39/3.99  
% 27.39/3.99  fof(f39,plain,(
% 27.39/3.99    ! [X0] : (! [X1] : (k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.39/3.99    inference(flattening,[],[f38])).
% 27.39/3.99  
% 27.39/3.99  fof(f74,plain,(
% 27.39/3.99    ( ! [X0,X1] : (k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.39/3.99    inference(cnf_transformation,[],[f39])).
% 27.39/3.99  
% 27.39/3.99  fof(f10,axiom,(
% 27.39/3.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 27.39/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.39/3.99  
% 27.39/3.99  fof(f33,plain,(
% 27.39/3.99    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 27.39/3.99    inference(ennf_transformation,[],[f10])).
% 27.39/3.99  
% 27.39/3.99  fof(f34,plain,(
% 27.39/3.99    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.39/3.99    inference(flattening,[],[f33])).
% 27.39/3.99  
% 27.39/3.99  fof(f71,plain,(
% 27.39/3.99    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.39/3.99    inference(cnf_transformation,[],[f34])).
% 27.39/3.99  
% 27.39/3.99  fof(f16,axiom,(
% 27.39/3.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 27.39/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.39/3.99  
% 27.39/3.99  fof(f44,plain,(
% 27.39/3.99    ! [X0] : (! [X1] : (((v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.39/3.99    inference(ennf_transformation,[],[f16])).
% 27.39/3.99  
% 27.39/3.99  fof(f45,plain,(
% 27.39/3.99    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.39/3.99    inference(flattening,[],[f44])).
% 27.39/3.99  
% 27.39/3.99  fof(f54,plain,(
% 27.39/3.99    ! [X0] : (! [X1] : (((v3_tops_1(X1,X0) | k2_tops_1(X0,X1) != X1) & (k2_tops_1(X0,X1) = X1 | ~v3_tops_1(X1,X0))) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 27.39/3.99    inference(nnf_transformation,[],[f45])).
% 27.39/3.99  
% 27.39/3.99  fof(f77,plain,(
% 27.39/3.99    ( ! [X0,X1] : (k2_tops_1(X0,X1) = X1 | ~v3_tops_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.39/3.99    inference(cnf_transformation,[],[f54])).
% 27.39/3.99  
% 27.39/3.99  fof(f17,axiom,(
% 27.39/3.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_tops_1(k2_tops_1(X0,X1),X0))))),
% 27.39/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.39/3.99  
% 27.39/3.99  fof(f46,plain,(
% 27.39/3.99    ! [X0] : (! [X1] : ((v3_tops_1(k2_tops_1(X0,X1),X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 27.39/3.99    inference(ennf_transformation,[],[f17])).
% 27.39/3.99  
% 27.39/3.99  fof(f47,plain,(
% 27.39/3.99    ! [X0] : (! [X1] : (v3_tops_1(k2_tops_1(X0,X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.39/3.99    inference(flattening,[],[f46])).
% 27.39/3.99  
% 27.39/3.99  fof(f79,plain,(
% 27.39/3.99    ( ! [X0,X1] : (v3_tops_1(k2_tops_1(X0,X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.39/3.99    inference(cnf_transformation,[],[f47])).
% 27.39/3.99  
% 27.39/3.99  fof(f8,axiom,(
% 27.39/3.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 27.39/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.39/3.99  
% 27.39/3.99  fof(f29,plain,(
% 27.39/3.99    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 27.39/3.99    inference(ennf_transformation,[],[f8])).
% 27.39/3.99  
% 27.39/3.99  fof(f30,plain,(
% 27.39/3.99    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 27.39/3.99    inference(flattening,[],[f29])).
% 27.39/3.99  
% 27.39/3.99  fof(f69,plain,(
% 27.39/3.99    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 27.39/3.99    inference(cnf_transformation,[],[f30])).
% 27.39/3.99  
% 27.39/3.99  fof(f9,axiom,(
% 27.39/3.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_tops_1(X0,X1),X0))),
% 27.39/3.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.39/3.99  
% 27.39/3.99  fof(f31,plain,(
% 27.39/3.99    ! [X0,X1] : (v4_pre_topc(k2_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 27.39/3.99    inference(ennf_transformation,[],[f9])).
% 27.39/3.99  
% 27.39/3.99  fof(f32,plain,(
% 27.39/3.99    ! [X0,X1] : (v4_pre_topc(k2_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 27.39/3.99    inference(flattening,[],[f31])).
% 27.39/3.99  
% 27.39/3.99  fof(f70,plain,(
% 27.39/3.99    ( ! [X0,X1] : (v4_pre_topc(k2_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 27.39/3.99    inference(cnf_transformation,[],[f32])).
% 27.39/3.99  
% 27.39/3.99  fof(f84,plain,(
% 27.39/3.99    k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0),
% 27.39/3.99    inference(cnf_transformation,[],[f57])).
% 27.39/3.99  
% 27.39/3.99  cnf(c_9,plain,
% 27.39/3.99      ( ~ v4_tops_1(X0,X1)
% 27.39/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 27.39/3.99      | ~ l1_pre_topc(X1) ),
% 27.39/3.99      inference(cnf_transformation,[],[f65]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_23,negated_conjecture,
% 27.39/3.99      ( v4_tops_1(sK1,sK0) ),
% 27.39/3.99      inference(cnf_transformation,[],[f83]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_578,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 27.39/3.99      | ~ l1_pre_topc(X1)
% 27.39/3.99      | sK1 != X0
% 27.39/3.99      | sK0 != X1 ),
% 27.39/3.99      inference(resolution_lifted,[status(thm)],[c_9,c_23]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_579,plain,
% 27.39/3.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1)
% 27.39/3.99      | ~ l1_pre_topc(sK0) ),
% 27.39/3.99      inference(unflattening,[status(thm)],[c_578]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_25,negated_conjecture,
% 27.39/3.99      ( l1_pre_topc(sK0) ),
% 27.39/3.99      inference(cnf_transformation,[],[f81]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_24,negated_conjecture,
% 27.39/3.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 27.39/3.99      inference(cnf_transformation,[],[f82]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_581,plain,
% 27.39/3.99      ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) ),
% 27.39/3.99      inference(global_propositional_subsumption,
% 27.39/3.99                [status(thm)],
% 27.39/3.99                [c_579,c_25,c_24]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_1323,plain,
% 27.39/3.99      ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) = iProver_top ),
% 27.39/3.99      inference(predicate_to_equality,[status(thm)],[c_581]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_4,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | ~ l1_pre_topc(X1) ),
% 27.39/3.99      inference(cnf_transformation,[],[f62]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_682,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | sK0 != X1 ),
% 27.39/3.99      inference(resolution_lifted,[status(thm)],[c_4,c_25]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_683,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 27.39/3.99      inference(unflattening,[status(thm)],[c_682]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_1315,plain,
% 27.39/3.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 27.39/3.99      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 27.39/3.99      inference(predicate_to_equality,[status(thm)],[c_683]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_1326,plain,
% 27.39/3.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 27.39/3.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_14,plain,
% 27.39/3.99      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 27.39/3.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 27.39/3.99      | ~ v2_pre_topc(X0)
% 27.39/3.99      | ~ l1_pre_topc(X0) ),
% 27.39/3.99      inference(cnf_transformation,[],[f72]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_18,plain,
% 27.39/3.99      ( ~ v3_pre_topc(X0,X1)
% 27.39/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | ~ r1_tarski(X0,X2)
% 27.39/3.99      | r1_tarski(X0,k1_tops_1(X1,X2))
% 27.39/3.99      | ~ l1_pre_topc(X1) ),
% 27.39/3.99      inference(cnf_transformation,[],[f76]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_291,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 27.39/3.99      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
% 27.39/3.99      | ~ r1_tarski(X2,X4)
% 27.39/3.99      | r1_tarski(X2,k1_tops_1(X3,X4))
% 27.39/3.99      | ~ v2_pre_topc(X1)
% 27.39/3.99      | ~ l1_pre_topc(X1)
% 27.39/3.99      | ~ l1_pre_topc(X3)
% 27.39/3.99      | X3 != X1
% 27.39/3.99      | k1_tops_1(X1,X0) != X2 ),
% 27.39/3.99      inference(resolution_lifted,[status(thm)],[c_14,c_18]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_292,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | ~ m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | ~ r1_tarski(k1_tops_1(X1,X0),X2)
% 27.39/3.99      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 27.39/3.99      | ~ v2_pre_topc(X1)
% 27.39/3.99      | ~ l1_pre_topc(X1) ),
% 27.39/3.99      inference(unflattening,[status(thm)],[c_291]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_10,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | ~ l1_pre_topc(X1) ),
% 27.39/3.99      inference(cnf_transformation,[],[f68]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_296,plain,
% 27.39/3.99      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | ~ r1_tarski(k1_tops_1(X1,X0),X2)
% 27.39/3.99      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 27.39/3.99      | ~ v2_pre_topc(X1)
% 27.39/3.99      | ~ l1_pre_topc(X1) ),
% 27.39/3.99      inference(global_propositional_subsumption,
% 27.39/3.99                [status(thm)],
% 27.39/3.99                [c_292,c_10]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_297,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | ~ r1_tarski(k1_tops_1(X1,X0),X2)
% 27.39/3.99      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 27.39/3.99      | ~ v2_pre_topc(X1)
% 27.39/3.99      | ~ l1_pre_topc(X1) ),
% 27.39/3.99      inference(renaming,[status(thm)],[c_296]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_26,negated_conjecture,
% 27.39/3.99      ( v2_pre_topc(sK0) ),
% 27.39/3.99      inference(cnf_transformation,[],[f80]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_480,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | ~ r1_tarski(k1_tops_1(X1,X0),X2)
% 27.39/3.99      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 27.39/3.99      | ~ l1_pre_topc(X1)
% 27.39/3.99      | sK0 != X1 ),
% 27.39/3.99      inference(resolution_lifted,[status(thm)],[c_297,c_26]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_481,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | ~ r1_tarski(k1_tops_1(sK0,X0),X1)
% 27.39/3.99      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1))
% 27.39/3.99      | ~ l1_pre_topc(sK0) ),
% 27.39/3.99      inference(unflattening,[status(thm)],[c_480]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_485,plain,
% 27.39/3.99      ( r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1))
% 27.39/3.99      | ~ r1_tarski(k1_tops_1(sK0,X0),X1)
% 27.39/3.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 27.39/3.99      inference(global_propositional_subsumption,
% 27.39/3.99                [status(thm)],
% 27.39/3.99                [c_481,c_25]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_486,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | ~ r1_tarski(k1_tops_1(sK0,X1),X0)
% 27.39/3.99      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) ),
% 27.39/3.99      inference(renaming,[status(thm)],[c_485]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_1325,plain,
% 27.39/3.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 27.39/3.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 27.39/3.99      | r1_tarski(k1_tops_1(sK0,X1),X0) != iProver_top
% 27.39/3.99      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) = iProver_top ),
% 27.39/3.99      inference(predicate_to_equality,[status(thm)],[c_486]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_0,plain,
% 27.39/3.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 27.39/3.99      inference(cnf_transformation,[],[f60]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_1329,plain,
% 27.39/3.99      ( X0 = X1
% 27.39/3.99      | r1_tarski(X0,X1) != iProver_top
% 27.39/3.99      | r1_tarski(X1,X0) != iProver_top ),
% 27.39/3.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_3720,plain,
% 27.39/3.99      ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,X1)
% 27.39/3.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 27.39/3.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 27.39/3.99      | r1_tarski(k1_tops_1(sK0,X0),X1) != iProver_top
% 27.39/3.99      | r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) != iProver_top ),
% 27.39/3.99      inference(superposition,[status(thm)],[c_1325,c_1329]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_6356,plain,
% 27.39/3.99      ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,X1)
% 27.39/3.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 27.39/3.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 27.39/3.99      | r1_tarski(k1_tops_1(sK0,X1),X0) != iProver_top
% 27.39/3.99      | r1_tarski(k1_tops_1(sK0,X0),X1) != iProver_top ),
% 27.39/3.99      inference(superposition,[status(thm)],[c_1325,c_3720]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_38990,plain,
% 27.39/3.99      ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,sK1)
% 27.39/3.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 27.39/3.99      | r1_tarski(k1_tops_1(sK0,X0),sK1) != iProver_top
% 27.39/3.99      | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top ),
% 27.39/3.99      inference(superposition,[status(thm)],[c_1326,c_6356]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_39082,plain,
% 27.39/3.99      ( k1_tops_1(sK0,k2_pre_topc(sK0,X0)) = k1_tops_1(sK0,sK1)
% 27.39/3.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 27.39/3.99      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,X0)),sK1) != iProver_top
% 27.39/3.99      | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,X0)) != iProver_top ),
% 27.39/3.99      inference(superposition,[status(thm)],[c_1315,c_38990]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_39155,plain,
% 27.39/3.99      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 27.39/3.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 27.39/3.99      | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) != iProver_top ),
% 27.39/3.99      inference(superposition,[status(thm)],[c_1323,c_39082]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_1447,plain,
% 27.39/3.99      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 27.39/3.99      inference(instantiation,[status(thm)],[c_683]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_6,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 27.39/3.99      | ~ l1_pre_topc(X1) ),
% 27.39/3.99      inference(cnf_transformation,[],[f64]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_658,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 27.39/3.99      | sK0 != X1 ),
% 27.39/3.99      inference(resolution_lifted,[status(thm)],[c_6,c_25]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_659,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
% 27.39/3.99      inference(unflattening,[status(thm)],[c_658]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_1450,plain,
% 27.39/3.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
% 27.39/3.99      inference(instantiation,[status(thm)],[c_659]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_1462,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1))
% 27.39/3.99      | ~ r1_tarski(k1_tops_1(sK0,X0),sK1) ),
% 27.39/3.99      inference(instantiation,[status(thm)],[c_486]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_1713,plain,
% 27.39/3.99      ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1))
% 27.39/3.99      | ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) ),
% 27.39/3.99      inference(instantiation,[status(thm)],[c_1462]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_17,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | ~ r1_tarski(X0,X2)
% 27.39/3.99      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 27.39/3.99      | ~ l1_pre_topc(X1) ),
% 27.39/3.99      inference(cnf_transformation,[],[f75]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_604,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | ~ r1_tarski(X0,X2)
% 27.39/3.99      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 27.39/3.99      | sK0 != X1 ),
% 27.39/3.99      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_605,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | ~ r1_tarski(X0,X1)
% 27.39/3.99      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) ),
% 27.39/3.99      inference(unflattening,[status(thm)],[c_604]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_1467,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0))
% 27.39/3.99      | ~ r1_tarski(sK1,X0) ),
% 27.39/3.99      inference(instantiation,[status(thm)],[c_605]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_1730,plain,
% 27.39/3.99      ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
% 27.39/3.99      | ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
% 27.39/3.99      inference(instantiation,[status(thm)],[c_1467]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_6588,plain,
% 27.39/3.99      ( ~ r1_tarski(X0,k1_tops_1(sK0,sK1))
% 27.39/3.99      | ~ r1_tarski(k1_tops_1(sK0,sK1),X0)
% 27.39/3.99      | X0 = k1_tops_1(sK0,sK1) ),
% 27.39/3.99      inference(instantiation,[status(thm)],[c_0]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_21541,plain,
% 27.39/3.99      ( ~ r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,sK1))
% 27.39/3.99      | ~ r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
% 27.39/3.99      | k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 27.39/3.99      inference(instantiation,[status(thm)],[c_6588]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_111019,plain,
% 27.39/3.99      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 27.39/3.99      inference(global_propositional_subsumption,
% 27.39/3.99                [status(thm)],
% 27.39/3.99                [c_39155,c_25,c_24,c_579,c_1447,c_1450,c_1713,c_1730,
% 27.39/3.99                 c_21541]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_15,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | ~ l1_pre_topc(X1)
% 27.39/3.99      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 27.39/3.99      inference(cnf_transformation,[],[f73]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_622,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 27.39/3.99      | sK0 != X1 ),
% 27.39/3.99      inference(resolution_lifted,[status(thm)],[c_15,c_25]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_623,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 27.39/3.99      inference(unflattening,[status(thm)],[c_622]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_1320,plain,
% 27.39/3.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 27.39/3.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 27.39/3.99      inference(predicate_to_equality,[status(thm)],[c_623]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_2919,plain,
% 27.39/3.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,X0)),k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0))
% 27.39/3.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 27.39/3.99      inference(superposition,[status(thm)],[c_1315,c_1320]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_7256,plain,
% 27.39/3.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
% 27.39/3.99      inference(superposition,[status(thm)],[c_1326,c_2919]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_5,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | ~ l1_pre_topc(X1)
% 27.39/3.99      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0) ),
% 27.39/3.99      inference(cnf_transformation,[],[f63]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_670,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | k2_pre_topc(X1,k2_pre_topc(X1,X0)) = k2_pre_topc(X1,X0)
% 27.39/3.99      | sK0 != X1 ),
% 27.39/3.99      inference(resolution_lifted,[status(thm)],[c_5,c_25]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_671,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 27.39/3.99      inference(unflattening,[status(thm)],[c_670]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_1316,plain,
% 27.39/3.99      ( k2_pre_topc(sK0,k2_pre_topc(sK0,X0)) = k2_pre_topc(sK0,X0)
% 27.39/3.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 27.39/3.99      inference(predicate_to_equality,[status(thm)],[c_671]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_1693,plain,
% 27.39/3.99      ( k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 27.39/3.99      inference(superposition,[status(thm)],[c_1326,c_1316]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_7277,plain,
% 27.39/3.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
% 27.39/3.99      inference(light_normalisation,[status(thm)],[c_7256,c_1693]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_111076,plain,
% 27.39/3.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
% 27.39/3.99      inference(demodulation,[status(thm)],[c_111019,c_7277]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_2918,plain,
% 27.39/3.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 27.39/3.99      inference(superposition,[status(thm)],[c_1326,c_1320]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_111087,plain,
% 27.39/3.99      ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 27.39/3.99      inference(light_normalisation,[status(thm)],[c_111076,c_2918]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_16,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | ~ v2_pre_topc(X1)
% 27.39/3.99      | ~ l1_pre_topc(X1)
% 27.39/3.99      | k1_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X0))) = k1_xboole_0 ),
% 27.39/3.99      inference(cnf_transformation,[],[f74]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_504,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | ~ l1_pre_topc(X1)
% 27.39/3.99      | k1_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X0))) = k1_xboole_0
% 27.39/3.99      | sK0 != X1 ),
% 27.39/3.99      inference(resolution_lifted,[status(thm)],[c_16,c_26]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_505,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | ~ l1_pre_topc(sK0)
% 27.39/3.99      | k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) = k1_xboole_0 ),
% 27.39/3.99      inference(unflattening,[status(thm)],[c_504]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_509,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) = k1_xboole_0 ),
% 27.39/3.99      inference(global_propositional_subsumption,
% 27.39/3.99                [status(thm)],
% 27.39/3.99                [c_505,c_25]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_1324,plain,
% 27.39/3.99      ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) = k1_xboole_0
% 27.39/3.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 27.39/3.99      inference(predicate_to_equality,[status(thm)],[c_509]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_2587,plain,
% 27.39/3.99      ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0)))) = k1_xboole_0
% 27.39/3.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 27.39/3.99      inference(superposition,[status(thm)],[c_1315,c_1324]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_4513,plain,
% 27.39/3.99      ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = k1_xboole_0 ),
% 27.39/3.99      inference(superposition,[status(thm)],[c_1326,c_2587]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_13,plain,
% 27.39/3.99      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 27.39/3.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 27.39/3.99      | ~ v2_pre_topc(X0)
% 27.39/3.99      | ~ l1_pre_topc(X0) ),
% 27.39/3.99      inference(cnf_transformation,[],[f71]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_423,plain,
% 27.39/3.99      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 27.39/3.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 27.39/3.99      | ~ l1_pre_topc(X0)
% 27.39/3.99      | sK0 != X0 ),
% 27.39/3.99      inference(resolution_lifted,[status(thm)],[c_13,c_26]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_424,plain,
% 27.39/3.99      ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
% 27.39/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | ~ l1_pre_topc(sK0) ),
% 27.39/3.99      inference(unflattening,[status(thm)],[c_423]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_428,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | v4_pre_topc(k2_pre_topc(sK0,X0),sK0) ),
% 27.39/3.99      inference(global_propositional_subsumption,
% 27.39/3.99                [status(thm)],
% 27.39/3.99                [c_424,c_25]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_429,plain,
% 27.39/3.99      ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
% 27.39/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 27.39/3.99      inference(renaming,[status(thm)],[c_428]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_20,plain,
% 27.39/3.99      ( ~ v3_tops_1(X0,X1)
% 27.39/3.99      | ~ v4_pre_topc(X0,X1)
% 27.39/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | ~ l1_pre_topc(X1)
% 27.39/3.99      | k2_tops_1(X1,X0) = X0 ),
% 27.39/3.99      inference(cnf_transformation,[],[f77]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_21,plain,
% 27.39/3.99      ( v3_tops_1(k2_tops_1(X0,X1),X0)
% 27.39/3.99      | ~ v4_pre_topc(X1,X0)
% 27.39/3.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 27.39/3.99      | ~ v2_pre_topc(X0)
% 27.39/3.99      | ~ l1_pre_topc(X0) ),
% 27.39/3.99      inference(cnf_transformation,[],[f79]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_329,plain,
% 27.39/3.99      ( ~ v4_pre_topc(X0,X1)
% 27.39/3.99      | ~ v4_pre_topc(X2,X3)
% 27.39/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 27.39/3.99      | ~ v2_pre_topc(X3)
% 27.39/3.99      | ~ l1_pre_topc(X1)
% 27.39/3.99      | ~ l1_pre_topc(X3)
% 27.39/3.99      | X3 != X1
% 27.39/3.99      | k2_tops_1(X3,X2) != X0
% 27.39/3.99      | k2_tops_1(X1,X0) = X0 ),
% 27.39/3.99      inference(resolution_lifted,[status(thm)],[c_20,c_21]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_330,plain,
% 27.39/3.99      ( ~ v4_pre_topc(X0,X1)
% 27.39/3.99      | ~ v4_pre_topc(k2_tops_1(X1,X0),X1)
% 27.39/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | ~ m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | ~ v2_pre_topc(X1)
% 27.39/3.99      | ~ l1_pre_topc(X1)
% 27.39/3.99      | k2_tops_1(X1,k2_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 27.39/3.99      inference(unflattening,[status(thm)],[c_329]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_11,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | ~ l1_pre_topc(X1) ),
% 27.39/3.99      inference(cnf_transformation,[],[f69]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_334,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | ~ v4_pre_topc(k2_tops_1(X1,X0),X1)
% 27.39/3.99      | ~ v4_pre_topc(X0,X1)
% 27.39/3.99      | ~ v2_pre_topc(X1)
% 27.39/3.99      | ~ l1_pre_topc(X1)
% 27.39/3.99      | k2_tops_1(X1,k2_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 27.39/3.99      inference(global_propositional_subsumption,
% 27.39/3.99                [status(thm)],
% 27.39/3.99                [c_330,c_11]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_335,plain,
% 27.39/3.99      ( ~ v4_pre_topc(X0,X1)
% 27.39/3.99      | ~ v4_pre_topc(k2_tops_1(X1,X0),X1)
% 27.39/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | ~ v2_pre_topc(X1)
% 27.39/3.99      | ~ l1_pre_topc(X1)
% 27.39/3.99      | k2_tops_1(X1,k2_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 27.39/3.99      inference(renaming,[status(thm)],[c_334]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_12,plain,
% 27.39/3.99      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
% 27.39/3.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 27.39/3.99      | ~ v2_pre_topc(X0)
% 27.39/3.99      | ~ l1_pre_topc(X0) ),
% 27.39/3.99      inference(cnf_transformation,[],[f70]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_352,plain,
% 27.39/3.99      ( ~ v4_pre_topc(X0,X1)
% 27.39/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | ~ v2_pre_topc(X1)
% 27.39/3.99      | ~ l1_pre_topc(X1)
% 27.39/3.99      | k2_tops_1(X1,k2_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 27.39/3.99      inference(forward_subsumption_resolution,
% 27.39/3.99                [status(thm)],
% 27.39/3.99                [c_335,c_12]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_459,plain,
% 27.39/3.99      ( ~ v4_pre_topc(X0,X1)
% 27.39/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 27.39/3.99      | ~ l1_pre_topc(X1)
% 27.39/3.99      | k2_tops_1(X1,k2_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 27.39/3.99      | sK0 != X1 ),
% 27.39/3.99      inference(resolution_lifted,[status(thm)],[c_352,c_26]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_460,plain,
% 27.39/3.99      ( ~ v4_pre_topc(X0,sK0)
% 27.39/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | ~ l1_pre_topc(sK0)
% 27.39/3.99      | k2_tops_1(sK0,k2_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 27.39/3.99      inference(unflattening,[status(thm)],[c_459]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_464,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | ~ v4_pre_topc(X0,sK0)
% 27.39/3.99      | k2_tops_1(sK0,k2_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 27.39/3.99      inference(global_propositional_subsumption,
% 27.39/3.99                [status(thm)],
% 27.39/3.99                [c_460,c_25]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_465,plain,
% 27.39/3.99      ( ~ v4_pre_topc(X0,sK0)
% 27.39/3.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | k2_tops_1(sK0,k2_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 27.39/3.99      inference(renaming,[status(thm)],[c_464]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_847,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | k2_tops_1(sK0,k2_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 27.39/3.99      | k2_pre_topc(sK0,X1) != X0
% 27.39/3.99      | sK0 != sK0 ),
% 27.39/3.99      inference(resolution_lifted,[status(thm)],[c_429,c_465]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_848,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | ~ m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0)) ),
% 27.39/3.99      inference(unflattening,[status(thm)],[c_847]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_540,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | k2_tops_1(sK0,k2_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 27.39/3.99      | k2_pre_topc(sK0,X1) != X0
% 27.39/3.99      | sK0 != sK0 ),
% 27.39/3.99      inference(resolution_lifted,[status(thm)],[c_429,c_465]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_541,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | ~ m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0)) ),
% 27.39/3.99      inference(unflattening,[status(thm)],[c_540]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_850,plain,
% 27.39/3.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 27.39/3.99      | k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0)) ),
% 27.39/3.99      inference(global_propositional_subsumption,
% 27.39/3.99                [status(thm)],
% 27.39/3.99                [c_848,c_541,c_683]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_1314,plain,
% 27.39/3.99      ( k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0))
% 27.39/3.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 27.39/3.99      inference(predicate_to_equality,[status(thm)],[c_850]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_3123,plain,
% 27.39/3.99      ( k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
% 27.39/3.99      inference(superposition,[status(thm)],[c_1326,c_1314]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_4530,plain,
% 27.39/3.99      ( k1_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_xboole_0 ),
% 27.39/3.99      inference(light_normalisation,[status(thm)],[c_4513,c_3123]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_111548,plain,
% 27.39/3.99      ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) = k1_xboole_0 ),
% 27.39/3.99      inference(demodulation,[status(thm)],[c_111087,c_4530]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(c_22,negated_conjecture,
% 27.39/3.99      ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0 ),
% 27.39/3.99      inference(cnf_transformation,[],[f84]) ).
% 27.39/3.99  
% 27.39/3.99  cnf(contradiction,plain,
% 27.39/3.99      ( $false ),
% 27.39/3.99      inference(minisat,[status(thm)],[c_111548,c_22]) ).
% 27.39/3.99  
% 27.39/3.99  
% 27.39/3.99  % SZS output end CNFRefutation for theBenchmark.p
% 27.39/3.99  
% 27.39/3.99  ------                               Statistics
% 27.39/3.99  
% 27.39/3.99  ------ General
% 27.39/3.99  
% 27.39/3.99  abstr_ref_over_cycles:                  0
% 27.39/3.99  abstr_ref_under_cycles:                 0
% 27.39/3.99  gc_basic_clause_elim:                   0
% 27.39/3.99  forced_gc_time:                         0
% 27.39/3.99  parsing_time:                           0.009
% 27.39/3.99  unif_index_cands_time:                  0.
% 27.39/3.99  unif_index_add_time:                    0.
% 27.39/3.99  orderings_time:                         0.
% 27.39/3.99  out_proof_time:                         0.019
% 27.39/3.99  total_time:                             3.063
% 27.39/3.99  num_of_symbols:                         49
% 27.39/3.99  num_of_terms:                           94126
% 27.39/3.99  
% 27.39/3.99  ------ Preprocessing
% 27.39/3.99  
% 27.39/3.99  num_of_splits:                          0
% 27.39/3.99  num_of_split_atoms:                     0
% 27.39/3.99  num_of_reused_defs:                     0
% 27.39/3.99  num_eq_ax_congr_red:                    12
% 27.39/3.99  num_of_sem_filtered_clauses:            1
% 27.39/3.99  num_of_subtypes:                        0
% 27.39/3.99  monotx_restored_types:                  0
% 27.39/3.99  sat_num_of_epr_types:                   0
% 27.39/3.99  sat_num_of_non_cyclic_types:            0
% 27.39/3.99  sat_guarded_non_collapsed_types:        0
% 27.39/3.99  num_pure_diseq_elim:                    0
% 27.39/3.99  simp_replaced_by:                       0
% 27.39/3.99  res_preprocessed:                       120
% 27.39/3.99  prep_upred:                             0
% 27.39/3.99  prep_unflattend:                        28
% 27.39/3.99  smt_new_axioms:                         0
% 27.39/3.99  pred_elim_cands:                        2
% 27.39/3.99  pred_elim:                              6
% 27.39/3.99  pred_elim_cl:                           8
% 27.39/3.99  pred_elim_cycles:                       11
% 27.39/3.99  merged_defs:                            0
% 27.39/3.99  merged_defs_ncl:                        0
% 27.39/3.99  bin_hyper_res:                          0
% 27.39/3.99  prep_cycles:                            5
% 27.39/3.99  pred_elim_time:                         0.014
% 27.39/3.99  splitting_time:                         0.
% 27.39/3.99  sem_filter_time:                        0.
% 27.39/3.99  monotx_time:                            0.
% 27.39/3.99  subtype_inf_time:                       0.
% 27.39/3.99  
% 27.39/3.99  ------ Problem properties
% 27.39/3.99  
% 27.39/3.99  clauses:                                18
% 27.39/3.99  conjectures:                            2
% 27.39/3.99  epr:                                    2
% 27.39/3.99  horn:                                   18
% 27.39/3.99  ground:                                 4
% 27.39/3.99  unary:                                  5
% 27.39/3.99  binary:                                 10
% 27.39/3.99  lits:                                   36
% 27.39/3.99  lits_eq:                                8
% 27.39/3.99  fd_pure:                                0
% 27.39/3.99  fd_pseudo:                              0
% 27.39/3.99  fd_cond:                                0
% 27.39/3.99  fd_pseudo_cond:                         1
% 27.39/3.99  ac_symbols:                             0
% 27.39/3.99  
% 27.39/3.99  ------ Propositional Solver
% 27.39/3.99  
% 27.39/3.99  prop_solver_calls:                      48
% 27.39/3.99  prop_fast_solver_calls:                 3751
% 27.39/3.99  smt_solver_calls:                       0
% 27.39/3.99  smt_fast_solver_calls:                  0
% 27.39/3.99  prop_num_of_clauses:                    30753
% 27.39/3.99  prop_preprocess_simplified:             40099
% 27.39/3.99  prop_fo_subsumed:                       249
% 27.39/3.99  prop_solver_time:                       0.
% 27.39/3.99  smt_solver_time:                        0.
% 27.39/3.99  smt_fast_solver_time:                   0.
% 27.39/3.99  prop_fast_solver_time:                  0.
% 27.39/3.99  prop_unsat_core_time:                   0.003
% 27.39/3.99  
% 27.39/3.99  ------ QBF
% 27.39/3.99  
% 27.39/3.99  qbf_q_res:                              0
% 27.39/3.99  qbf_num_tautologies:                    0
% 27.39/3.99  qbf_prep_cycles:                        0
% 27.39/3.99  
% 27.39/3.99  ------ BMC1
% 27.39/3.99  
% 27.39/3.99  bmc1_current_bound:                     -1
% 27.39/3.99  bmc1_last_solved_bound:                 -1
% 27.39/3.99  bmc1_unsat_core_size:                   -1
% 27.39/3.99  bmc1_unsat_core_parents_size:           -1
% 27.39/3.99  bmc1_merge_next_fun:                    0
% 27.39/3.99  bmc1_unsat_core_clauses_time:           0.
% 27.39/3.99  
% 27.39/3.99  ------ Instantiation
% 27.39/3.99  
% 27.39/3.99  inst_num_of_clauses:                    1321
% 27.39/3.99  inst_num_in_passive:                    115
% 27.39/3.99  inst_num_in_active:                     3895
% 27.39/3.99  inst_num_in_unprocessed:                207
% 27.39/3.99  inst_num_of_loops:                      4179
% 27.39/3.99  inst_num_of_learning_restarts:          1
% 27.39/3.99  inst_num_moves_active_passive:          276
% 27.39/3.99  inst_lit_activity:                      0
% 27.39/3.99  inst_lit_activity_moves:                4
% 27.39/3.99  inst_num_tautologies:                   0
% 27.39/3.99  inst_num_prop_implied:                  0
% 27.39/3.99  inst_num_existing_simplified:           0
% 27.39/3.99  inst_num_eq_res_simplified:             0
% 27.39/3.99  inst_num_child_elim:                    0
% 27.39/3.99  inst_num_of_dismatching_blockings:      16432
% 27.39/3.99  inst_num_of_non_proper_insts:           10843
% 27.39/3.99  inst_num_of_duplicates:                 0
% 27.39/3.99  inst_inst_num_from_inst_to_res:         0
% 27.39/3.99  inst_dismatching_checking_time:         0.
% 27.39/3.99  
% 27.39/3.99  ------ Resolution
% 27.39/3.99  
% 27.39/3.99  res_num_of_clauses:                     28
% 27.39/3.99  res_num_in_passive:                     28
% 27.39/3.99  res_num_in_active:                      0
% 27.39/3.99  res_num_of_loops:                       125
% 27.39/3.99  res_forward_subset_subsumed:            774
% 27.39/3.99  res_backward_subset_subsumed:           0
% 27.39/3.99  res_forward_subsumed:                   0
% 27.39/3.99  res_backward_subsumed:                  0
% 27.39/3.99  res_forward_subsumption_resolution:     1
% 27.39/3.99  res_backward_subsumption_resolution:    0
% 27.39/3.99  res_clause_to_clause_subsumption:       21938
% 27.39/3.99  res_orphan_elimination:                 0
% 27.39/3.99  res_tautology_del:                      478
% 27.39/3.99  res_num_eq_res_simplified:              0
% 27.39/3.99  res_num_sel_changes:                    0
% 27.39/3.99  res_moves_from_active_to_pass:          0
% 27.39/3.99  
% 27.39/3.99  ------ Superposition
% 27.39/3.99  
% 27.39/3.99  sup_time_total:                         0.
% 27.39/3.99  sup_time_generating:                    0.
% 27.39/3.99  sup_time_sim_full:                      0.
% 27.39/3.99  sup_time_sim_immed:                     0.
% 27.39/3.99  
% 27.39/3.99  sup_num_of_clauses:                     3211
% 27.39/3.99  sup_num_in_active:                      735
% 27.39/3.99  sup_num_in_passive:                     2476
% 27.39/3.99  sup_num_of_loops:                       835
% 27.39/3.99  sup_fw_superposition:                   4175
% 27.39/3.99  sup_bw_superposition:                   4393
% 27.39/3.99  sup_immediate_simplified:               5843
% 27.39/3.99  sup_given_eliminated:                   0
% 27.39/3.99  comparisons_done:                       0
% 27.39/3.99  comparisons_avoided:                    0
% 27.39/3.99  
% 27.39/3.99  ------ Simplifications
% 27.39/3.99  
% 27.39/3.99  
% 27.39/3.99  sim_fw_subset_subsumed:                 1708
% 27.39/3.99  sim_bw_subset_subsumed:                 4
% 27.39/3.99  sim_fw_subsumed:                        2699
% 27.39/3.99  sim_bw_subsumed:                        0
% 27.39/3.99  sim_fw_subsumption_res:                 0
% 27.39/3.99  sim_bw_subsumption_res:                 0
% 27.39/3.99  sim_tautology_del:                      23
% 27.39/3.99  sim_eq_tautology_del:                   241
% 27.39/3.99  sim_eq_res_simp:                        0
% 27.39/3.99  sim_fw_demodulated:                     9
% 27.39/3.99  sim_bw_demodulated:                     97
% 27.39/3.99  sim_light_normalised:                   3946
% 27.39/3.99  sim_joinable_taut:                      0
% 27.39/3.99  sim_joinable_simp:                      0
% 27.39/3.99  sim_ac_normalised:                      0
% 27.39/3.99  sim_smt_subsumption:                    0
% 27.39/3.99  
%------------------------------------------------------------------------------
