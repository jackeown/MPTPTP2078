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
% DateTime   : Thu Dec  3 12:15:57 EST 2020

% Result     : Theorem 11.42s
% Output     : CNFRefutation 11.42s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 831 expanded)
%              Number of clauses        :  111 ( 260 expanded)
%              Number of leaves         :   18 ( 194 expanded)
%              Depth                    :   23
%              Number of atoms          :  625 (3471 expanded)
%              Number of equality atoms :  195 ( 776 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
           => k1_tops_1(X0,k2_tops_1(X0,X1)) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_tops_1(X1,X0)
             => k1_tops_1(X0,k2_tops_1(X0,X1)) = k1_xboole_0 ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k1_tops_1(X0,k2_tops_1(X0,sK1)) != k1_xboole_0
        & v4_tops_1(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
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

fof(f53,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0
    & v4_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f44,f52,f51])).

fof(f77,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f53])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f76,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f78,plain,(
    v4_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f75,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => ( v3_tops_1(X1,X0)
            <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> k2_tops_1(X0,X1) = X1 )
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> k2_tops_1(X0,X1) = X1 )
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tops_1(X1,X0)
              | k2_tops_1(X0,X1) != X1 )
            & ( k2_tops_1(X0,X1) = X1
              | ~ v3_tops_1(X1,X0) ) )
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = X1
      | ~ v3_tops_1(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => v3_tops_1(k2_tops_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(k2_tops_1(X0,X1),X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(k2_tops_1(X0,X1),X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v3_tops_1(k2_tops_1(X0,X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f79,plain,(
    k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1271,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_513,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_24])).

cnf(c_514,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_1260,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_514])).

cnf(c_2056,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1271,c_1260])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_561,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_24])).

cnf(c_562,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_561])).

cnf(c_1256,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_562])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_501,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_24])).

cnf(c_502,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_501])).

cnf(c_1261,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_502])).

cnf(c_1886,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k1_tops_1(sK0,k2_pre_topc(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1256,c_1261])).

cnf(c_9398,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_1271,c_1886])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_483,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_484,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) ),
    inference(unflattening,[status(thm)],[c_483])).

cnf(c_1262,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_484])).

cnf(c_9429,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_9398,c_1262])).

cnf(c_28,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1338,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_562])).

cnf(c_1339,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1338])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_537,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_24])).

cnf(c_538,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_537])).

cnf(c_1574,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_538])).

cnf(c_1587,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1574])).

cnf(c_9962,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9429,c_28,c_1339,c_1587])).

cnf(c_1883,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1271,c_1261])).

cnf(c_2233,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1883,c_1262])).

cnf(c_1335,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_538])).

cnf(c_1336,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1335])).

cnf(c_2417,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2233,c_28,c_1336])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1273,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2424,plain,
    ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2417,c_1273])).

cnf(c_9976,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) != iProver_top
    | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9962,c_2424])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_549,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_24])).

cnf(c_550,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_549])).

cnf(c_1361,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_550])).

cnf(c_1362,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1361])).

cnf(c_7,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_22,negated_conjecture,
    ( v4_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_319,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
    | ~ l1_pre_topc(X1)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_22])).

cnf(c_320,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_319])).

cnf(c_322,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_320,c_24,c_23])).

cnf(c_1270,plain,
    ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_322])).

cnf(c_2235,plain,
    ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1262,c_1273])).

cnf(c_9974,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9962,c_2235])).

cnf(c_12709,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,X0)
    | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9974,c_28,c_1339])).

cnf(c_12710,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
    | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_12709])).

cnf(c_12716,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1270,c_12710])).

cnf(c_18813,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9976,c_28,c_1362,c_12716])).

cnf(c_17,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_402,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_403,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_407,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(X0,sK0)
    | k7_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_403,c_24])).

cnf(c_408,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(renaming,[status(thm)],[c_407])).

cnf(c_1265,plain,
    ( k7_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | v4_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_408])).

cnf(c_3862,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0))
    | v4_pre_topc(k2_pre_topc(sK0,X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1256,c_1265])).

cnf(c_11,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_345,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_25])).

cnf(c_346,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_350,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k2_pre_topc(sK0,X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_346,c_24])).

cnf(c_351,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_350])).

cnf(c_611,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | k2_pre_topc(sK0,X1) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_351,c_408])).

cnf(c_612,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_611])).

cnf(c_616,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_612,c_562])).

cnf(c_618,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_616])).

cnf(c_21467,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3862,c_618])).

cnf(c_21471,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_1271,c_21467])).

cnf(c_21486,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_18813,c_21471])).

cnf(c_22037,plain,
    ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_2056,c_21486])).

cnf(c_19,plain,
    ( ~ v3_tops_1(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_20,plain,
    ( v3_tops_1(k2_tops_1(X0,X1),X0)
    | ~ v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_279,plain,
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
    inference(resolution_lifted,[status(thm)],[c_19,c_20])).

cnf(c_280,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(k2_tops_1(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_tops_1(X1,k2_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(unflattening,[status(thm)],[c_279])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_284,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_pre_topc(k2_tops_1(X1,X0),X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_tops_1(X1,k2_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_280,c_9])).

cnf(c_285,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ v4_pre_topc(k2_tops_1(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_tops_1(X1,k2_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(renaming,[status(thm)],[c_284])).

cnf(c_10,plain,
    ( v4_pre_topc(k2_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_302,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_tops_1(X1,k2_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_285,c_10])).

cnf(c_381,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_tops_1(X1,k2_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_302,c_25])).

cnf(c_382,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,k2_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_381])).

cnf(c_386,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(X0,sK0)
    | k2_tops_1(sK0,k2_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_382,c_24])).

cnf(c_387,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,k2_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(renaming,[status(thm)],[c_386])).

cnf(c_1266,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | v4_pre_topc(X0,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_387])).

cnf(c_4712,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0))
    | v4_pre_topc(k2_pre_topc(sK0,X0),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1256,c_1266])).

cnf(c_629,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,k2_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | k2_pre_topc(sK0,X1) != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_351,c_387])).

cnf(c_630,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_629])).

cnf(c_634,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_630,c_562])).

cnf(c_636,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_634])).

cnf(c_30768,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4712,c_636])).

cnf(c_30772,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_1271,c_30768])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X0))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_444,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X0))) = k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_25])).

cnf(c_445,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_449,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_445,c_24])).

cnf(c_1263,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_449])).

cnf(c_2772,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0)))) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1256,c_1263])).

cnf(c_13822,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1271,c_2772])).

cnf(c_30806,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_30772,c_13822])).

cnf(c_31079,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_22037,c_30806])).

cnf(c_21,negated_conjecture,
    ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_31079,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:43:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.42/2.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.42/2.04  
% 11.42/2.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.42/2.04  
% 11.42/2.04  ------  iProver source info
% 11.42/2.04  
% 11.42/2.04  git: date: 2020-06-30 10:37:57 +0100
% 11.42/2.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.42/2.04  git: non_committed_changes: false
% 11.42/2.04  git: last_make_outside_of_git: false
% 11.42/2.04  
% 11.42/2.04  ------ 
% 11.42/2.04  ------ Parsing...
% 11.42/2.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.42/2.04  
% 11.42/2.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 11.42/2.04  
% 11.42/2.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.42/2.04  
% 11.42/2.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.42/2.04  ------ Proving...
% 11.42/2.04  ------ Problem Properties 
% 11.42/2.04  
% 11.42/2.04  
% 11.42/2.04  clauses                                 19
% 11.42/2.04  conjectures                             2
% 11.42/2.04  EPR                                     2
% 11.42/2.04  Horn                                    19
% 11.42/2.04  unary                                   5
% 11.42/2.04  binary                                  9
% 11.42/2.04  lits                                    39
% 11.42/2.04  lits eq                                 8
% 11.42/2.04  fd_pure                                 0
% 11.42/2.04  fd_pseudo                               0
% 11.42/2.04  fd_cond                                 0
% 11.42/2.04  fd_pseudo_cond                          1
% 11.42/2.04  AC symbols                              0
% 11.42/2.04  
% 11.42/2.04  ------ Input Options Time Limit: Unbounded
% 11.42/2.04  
% 11.42/2.04  
% 11.42/2.04  ------ 
% 11.42/2.04  Current options:
% 11.42/2.04  ------ 
% 11.42/2.04  
% 11.42/2.04  
% 11.42/2.04  
% 11.42/2.04  
% 11.42/2.04  ------ Proving...
% 11.42/2.04  
% 11.42/2.04  
% 11.42/2.04  % SZS status Theorem for theBenchmark.p
% 11.42/2.04  
% 11.42/2.04  % SZS output start CNFRefutation for theBenchmark.p
% 11.42/2.04  
% 11.42/2.04  fof(f16,conjecture,(
% 11.42/2.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) => k1_tops_1(X0,k2_tops_1(X0,X1)) = k1_xboole_0)))),
% 11.42/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/2.04  
% 11.42/2.04  fof(f17,negated_conjecture,(
% 11.42/2.04    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) => k1_tops_1(X0,k2_tops_1(X0,X1)) = k1_xboole_0)))),
% 11.42/2.04    inference(negated_conjecture,[],[f16])).
% 11.42/2.04  
% 11.42/2.04  fof(f43,plain,(
% 11.42/2.04    ? [X0] : (? [X1] : ((k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0 & v4_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 11.42/2.04    inference(ennf_transformation,[],[f17])).
% 11.42/2.04  
% 11.42/2.04  fof(f44,plain,(
% 11.42/2.04    ? [X0] : (? [X1] : (k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0 & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.42/2.04    inference(flattening,[],[f43])).
% 11.42/2.04  
% 11.42/2.04  fof(f52,plain,(
% 11.42/2.04    ( ! [X0] : (? [X1] : (k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0 & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (k1_tops_1(X0,k2_tops_1(X0,sK1)) != k1_xboole_0 & v4_tops_1(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.42/2.04    introduced(choice_axiom,[])).
% 11.42/2.04  
% 11.42/2.04  fof(f51,plain,(
% 11.42/2.04    ? [X0] : (? [X1] : (k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0 & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (k1_tops_1(sK0,k2_tops_1(sK0,X1)) != k1_xboole_0 & v4_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 11.42/2.04    introduced(choice_axiom,[])).
% 11.42/2.04  
% 11.42/2.04  fof(f53,plain,(
% 11.42/2.04    (k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0 & v4_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 11.42/2.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f44,f52,f51])).
% 11.42/2.04  
% 11.42/2.04  fof(f77,plain,(
% 11.42/2.04    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.42/2.04    inference(cnf_transformation,[],[f53])).
% 11.42/2.04  
% 11.42/2.04  fof(f9,axiom,(
% 11.42/2.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 11.42/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/2.04  
% 11.42/2.04  fof(f30,plain,(
% 11.42/2.04    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.42/2.04    inference(ennf_transformation,[],[f9])).
% 11.42/2.04  
% 11.42/2.04  fof(f66,plain,(
% 11.42/2.04    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.42/2.04    inference(cnf_transformation,[],[f30])).
% 11.42/2.04  
% 11.42/2.04  fof(f76,plain,(
% 11.42/2.04    l1_pre_topc(sK0)),
% 11.42/2.04    inference(cnf_transformation,[],[f53])).
% 11.42/2.04  
% 11.42/2.04  fof(f2,axiom,(
% 11.42/2.04    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.42/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/2.04  
% 11.42/2.04  fof(f18,plain,(
% 11.42/2.04    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.42/2.04    inference(ennf_transformation,[],[f2])).
% 11.42/2.04  
% 11.42/2.04  fof(f19,plain,(
% 11.42/2.04    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.42/2.04    inference(flattening,[],[f18])).
% 11.42/2.04  
% 11.42/2.04  fof(f57,plain,(
% 11.42/2.04    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.42/2.04    inference(cnf_transformation,[],[f19])).
% 11.42/2.04  
% 11.42/2.04  fof(f11,axiom,(
% 11.42/2.04    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 11.42/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/2.04  
% 11.42/2.04  fof(f33,plain,(
% 11.42/2.04    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.42/2.04    inference(ennf_transformation,[],[f11])).
% 11.42/2.04  
% 11.42/2.04  fof(f34,plain,(
% 11.42/2.04    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.42/2.04    inference(flattening,[],[f33])).
% 11.42/2.04  
% 11.42/2.04  fof(f68,plain,(
% 11.42/2.04    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.42/2.04    inference(cnf_transformation,[],[f34])).
% 11.42/2.04  
% 11.42/2.04  fof(f12,axiom,(
% 11.42/2.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 11.42/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/2.04  
% 11.42/2.04  fof(f35,plain,(
% 11.42/2.04    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.42/2.04    inference(ennf_transformation,[],[f12])).
% 11.42/2.04  
% 11.42/2.04  fof(f36,plain,(
% 11.42/2.04    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.42/2.04    inference(flattening,[],[f35])).
% 11.42/2.04  
% 11.42/2.04  fof(f69,plain,(
% 11.42/2.04    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.42/2.04    inference(cnf_transformation,[],[f36])).
% 11.42/2.04  
% 11.42/2.04  fof(f5,axiom,(
% 11.42/2.04    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.42/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/2.04  
% 11.42/2.04  fof(f22,plain,(
% 11.42/2.04    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.42/2.04    inference(ennf_transformation,[],[f5])).
% 11.42/2.04  
% 11.42/2.04  fof(f23,plain,(
% 11.42/2.04    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.42/2.04    inference(flattening,[],[f22])).
% 11.42/2.04  
% 11.42/2.04  fof(f62,plain,(
% 11.42/2.04    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.42/2.04    inference(cnf_transformation,[],[f23])).
% 11.42/2.04  
% 11.42/2.04  fof(f1,axiom,(
% 11.42/2.04    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.42/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/2.04  
% 11.42/2.04  fof(f45,plain,(
% 11.42/2.04    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.42/2.04    inference(nnf_transformation,[],[f1])).
% 11.42/2.04  
% 11.42/2.04  fof(f46,plain,(
% 11.42/2.04    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.42/2.04    inference(flattening,[],[f45])).
% 11.42/2.04  
% 11.42/2.04  fof(f56,plain,(
% 11.42/2.04    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.42/2.04    inference(cnf_transformation,[],[f46])).
% 11.42/2.04  
% 11.42/2.04  fof(f3,axiom,(
% 11.42/2.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 11.42/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/2.04  
% 11.42/2.04  fof(f20,plain,(
% 11.42/2.04    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.42/2.04    inference(ennf_transformation,[],[f3])).
% 11.42/2.04  
% 11.42/2.04  fof(f58,plain,(
% 11.42/2.04    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.42/2.04    inference(cnf_transformation,[],[f20])).
% 11.42/2.04  
% 11.42/2.04  fof(f4,axiom,(
% 11.42/2.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 11.42/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/2.04  
% 11.42/2.04  fof(f21,plain,(
% 11.42/2.04    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.42/2.04    inference(ennf_transformation,[],[f4])).
% 11.42/2.04  
% 11.42/2.04  fof(f47,plain,(
% 11.42/2.04    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.42/2.04    inference(nnf_transformation,[],[f21])).
% 11.42/2.04  
% 11.42/2.04  fof(f48,plain,(
% 11.42/2.04    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.42/2.04    inference(flattening,[],[f47])).
% 11.42/2.04  
% 11.42/2.04  fof(f59,plain,(
% 11.42/2.04    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.42/2.04    inference(cnf_transformation,[],[f48])).
% 11.42/2.04  
% 11.42/2.04  fof(f78,plain,(
% 11.42/2.04    v4_tops_1(sK1,sK0)),
% 11.42/2.04    inference(cnf_transformation,[],[f53])).
% 11.42/2.04  
% 11.42/2.04  fof(f13,axiom,(
% 11.42/2.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 11.42/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/2.04  
% 11.42/2.04  fof(f37,plain,(
% 11.42/2.04    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.42/2.04    inference(ennf_transformation,[],[f13])).
% 11.42/2.04  
% 11.42/2.04  fof(f38,plain,(
% 11.42/2.04    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.42/2.04    inference(flattening,[],[f37])).
% 11.42/2.04  
% 11.42/2.04  fof(f49,plain,(
% 11.42/2.04    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.42/2.04    inference(nnf_transformation,[],[f38])).
% 11.42/2.04  
% 11.42/2.04  fof(f70,plain,(
% 11.42/2.04    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.42/2.04    inference(cnf_transformation,[],[f49])).
% 11.42/2.04  
% 11.42/2.04  fof(f75,plain,(
% 11.42/2.04    v2_pre_topc(sK0)),
% 11.42/2.04    inference(cnf_transformation,[],[f53])).
% 11.42/2.04  
% 11.42/2.04  fof(f8,axiom,(
% 11.42/2.04    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 11.42/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/2.04  
% 11.42/2.04  fof(f28,plain,(
% 11.42/2.04    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.42/2.04    inference(ennf_transformation,[],[f8])).
% 11.42/2.04  
% 11.42/2.04  fof(f29,plain,(
% 11.42/2.04    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.42/2.04    inference(flattening,[],[f28])).
% 11.42/2.04  
% 11.42/2.04  fof(f65,plain,(
% 11.42/2.04    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.42/2.04    inference(cnf_transformation,[],[f29])).
% 11.42/2.04  
% 11.42/2.04  fof(f14,axiom,(
% 11.42/2.04    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 11.42/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/2.04  
% 11.42/2.04  fof(f39,plain,(
% 11.42/2.04    ! [X0] : (! [X1] : (((v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.42/2.04    inference(ennf_transformation,[],[f14])).
% 11.42/2.04  
% 11.42/2.04  fof(f40,plain,(
% 11.42/2.04    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.42/2.04    inference(flattening,[],[f39])).
% 11.42/2.04  
% 11.42/2.04  fof(f50,plain,(
% 11.42/2.04    ! [X0] : (! [X1] : (((v3_tops_1(X1,X0) | k2_tops_1(X0,X1) != X1) & (k2_tops_1(X0,X1) = X1 | ~v3_tops_1(X1,X0))) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.42/2.04    inference(nnf_transformation,[],[f40])).
% 11.42/2.04  
% 11.42/2.04  fof(f72,plain,(
% 11.42/2.04    ( ! [X0,X1] : (k2_tops_1(X0,X1) = X1 | ~v3_tops_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.42/2.04    inference(cnf_transformation,[],[f50])).
% 11.42/2.04  
% 11.42/2.04  fof(f15,axiom,(
% 11.42/2.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_tops_1(k2_tops_1(X0,X1),X0))))),
% 11.42/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/2.04  
% 11.42/2.04  fof(f41,plain,(
% 11.42/2.04    ! [X0] : (! [X1] : ((v3_tops_1(k2_tops_1(X0,X1),X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.42/2.04    inference(ennf_transformation,[],[f15])).
% 11.42/2.04  
% 11.42/2.04  fof(f42,plain,(
% 11.42/2.04    ! [X0] : (! [X1] : (v3_tops_1(k2_tops_1(X0,X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.42/2.04    inference(flattening,[],[f41])).
% 11.42/2.04  
% 11.42/2.04  fof(f74,plain,(
% 11.42/2.04    ( ! [X0,X1] : (v3_tops_1(k2_tops_1(X0,X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.42/2.04    inference(cnf_transformation,[],[f42])).
% 11.42/2.04  
% 11.42/2.04  fof(f6,axiom,(
% 11.42/2.04    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.42/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/2.04  
% 11.42/2.04  fof(f24,plain,(
% 11.42/2.04    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.42/2.04    inference(ennf_transformation,[],[f6])).
% 11.42/2.04  
% 11.42/2.04  fof(f25,plain,(
% 11.42/2.04    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.42/2.04    inference(flattening,[],[f24])).
% 11.42/2.04  
% 11.42/2.04  fof(f63,plain,(
% 11.42/2.04    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.42/2.04    inference(cnf_transformation,[],[f25])).
% 11.42/2.04  
% 11.42/2.04  fof(f7,axiom,(
% 11.42/2.04    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_tops_1(X0,X1),X0))),
% 11.42/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/2.04  
% 11.42/2.04  fof(f26,plain,(
% 11.42/2.04    ! [X0,X1] : (v4_pre_topc(k2_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.42/2.04    inference(ennf_transformation,[],[f7])).
% 11.42/2.04  
% 11.42/2.04  fof(f27,plain,(
% 11.42/2.04    ! [X0,X1] : (v4_pre_topc(k2_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.42/2.04    inference(flattening,[],[f26])).
% 11.42/2.04  
% 11.42/2.04  fof(f64,plain,(
% 11.42/2.04    ( ! [X0,X1] : (v4_pre_topc(k2_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.42/2.04    inference(cnf_transformation,[],[f27])).
% 11.42/2.04  
% 11.42/2.04  fof(f10,axiom,(
% 11.42/2.04    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0))),
% 11.42/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.42/2.04  
% 11.42/2.04  fof(f31,plain,(
% 11.42/2.04    ! [X0] : (! [X1] : (k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.42/2.04    inference(ennf_transformation,[],[f10])).
% 11.42/2.04  
% 11.42/2.04  fof(f32,plain,(
% 11.42/2.04    ! [X0] : (! [X1] : (k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.42/2.04    inference(flattening,[],[f31])).
% 11.42/2.04  
% 11.42/2.04  fof(f67,plain,(
% 11.42/2.04    ( ! [X0,X1] : (k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.42/2.04    inference(cnf_transformation,[],[f32])).
% 11.42/2.04  
% 11.42/2.04  fof(f79,plain,(
% 11.42/2.04    k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0),
% 11.42/2.04    inference(cnf_transformation,[],[f53])).
% 11.42/2.04  
% 11.42/2.04  cnf(c_23,negated_conjecture,
% 11.42/2.04      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.42/2.04      inference(cnf_transformation,[],[f77]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_1271,plain,
% 11.42/2.04      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.42/2.04      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_12,plain,
% 11.42/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.42/2.04      | ~ l1_pre_topc(X1)
% 11.42/2.04      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 11.42/2.04      inference(cnf_transformation,[],[f66]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_24,negated_conjecture,
% 11.42/2.04      ( l1_pre_topc(sK0) ),
% 11.42/2.04      inference(cnf_transformation,[],[f76]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_513,plain,
% 11.42/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.42/2.04      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 11.42/2.04      | sK0 != X1 ),
% 11.42/2.04      inference(resolution_lifted,[status(thm)],[c_12,c_24]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_514,plain,
% 11.42/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.42/2.04      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 11.42/2.04      inference(unflattening,[status(thm)],[c_513]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_1260,plain,
% 11.42/2.04      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 11.42/2.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.42/2.04      inference(predicate_to_equality,[status(thm)],[c_514]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_2056,plain,
% 11.42/2.04      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.42/2.04      inference(superposition,[status(thm)],[c_1271,c_1260]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_3,plain,
% 11.42/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.42/2.04      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.42/2.04      | ~ l1_pre_topc(X1) ),
% 11.42/2.04      inference(cnf_transformation,[],[f57]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_561,plain,
% 11.42/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.42/2.04      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.42/2.04      | sK0 != X1 ),
% 11.42/2.04      inference(resolution_lifted,[status(thm)],[c_3,c_24]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_562,plain,
% 11.42/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.42/2.04      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.42/2.04      inference(unflattening,[status(thm)],[c_561]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_1256,plain,
% 11.42/2.04      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.42/2.04      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.42/2.04      inference(predicate_to_equality,[status(thm)],[c_562]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_14,plain,
% 11.42/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.42/2.04      | ~ l1_pre_topc(X1)
% 11.42/2.04      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 11.42/2.04      inference(cnf_transformation,[],[f68]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_501,plain,
% 11.42/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.42/2.04      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
% 11.42/2.04      | sK0 != X1 ),
% 11.42/2.04      inference(resolution_lifted,[status(thm)],[c_14,c_24]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_502,plain,
% 11.42/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.42/2.04      | k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
% 11.42/2.04      inference(unflattening,[status(thm)],[c_501]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_1261,plain,
% 11.42/2.04      ( k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 11.42/2.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.42/2.04      inference(predicate_to_equality,[status(thm)],[c_502]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_1886,plain,
% 11.42/2.04      ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k1_tops_1(sK0,k2_pre_topc(sK0,X0))
% 11.42/2.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.42/2.04      inference(superposition,[status(thm)],[c_1256,c_1261]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_9398,plain,
% 11.42/2.04      ( k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
% 11.42/2.04      inference(superposition,[status(thm)],[c_1271,c_1886]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_15,plain,
% 11.42/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.42/2.04      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.42/2.04      | ~ r1_tarski(X0,X2)
% 11.42/2.04      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 11.42/2.04      | ~ l1_pre_topc(X1) ),
% 11.42/2.04      inference(cnf_transformation,[],[f69]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_483,plain,
% 11.42/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.42/2.04      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.42/2.04      | ~ r1_tarski(X0,X2)
% 11.42/2.04      | r1_tarski(k1_tops_1(X1,X0),k1_tops_1(X1,X2))
% 11.42/2.04      | sK0 != X1 ),
% 11.42/2.04      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_484,plain,
% 11.42/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.42/2.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.42/2.04      | ~ r1_tarski(X0,X1)
% 11.42/2.04      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) ),
% 11.42/2.04      inference(unflattening,[status(thm)],[c_483]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_1262,plain,
% 11.42/2.04      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.42/2.04      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.42/2.04      | r1_tarski(X0,X1) != iProver_top
% 11.42/2.04      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) = iProver_top ),
% 11.42/2.04      inference(predicate_to_equality,[status(thm)],[c_484]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_9429,plain,
% 11.42/2.04      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.42/2.04      | m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.42/2.04      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top
% 11.42/2.04      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,X0)) = iProver_top ),
% 11.42/2.04      inference(superposition,[status(thm)],[c_9398,c_1262]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_28,plain,
% 11.42/2.04      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.42/2.04      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_1338,plain,
% 11.42/2.04      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.42/2.04      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.42/2.04      inference(instantiation,[status(thm)],[c_562]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_1339,plain,
% 11.42/2.04      ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 11.42/2.04      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.42/2.04      inference(predicate_to_equality,[status(thm)],[c_1338]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_8,plain,
% 11.42/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.42/2.04      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.42/2.04      | ~ l1_pre_topc(X1) ),
% 11.42/2.04      inference(cnf_transformation,[],[f62]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_537,plain,
% 11.42/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.42/2.04      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.42/2.04      | sK0 != X1 ),
% 11.42/2.04      inference(resolution_lifted,[status(thm)],[c_8,c_24]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_538,plain,
% 11.42/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.42/2.04      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.42/2.04      inference(unflattening,[status(thm)],[c_537]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_1574,plain,
% 11.42/2.04      ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.42/2.04      | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.42/2.04      inference(instantiation,[status(thm)],[c_538]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_1587,plain,
% 11.42/2.04      ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 11.42/2.04      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.42/2.04      inference(predicate_to_equality,[status(thm)],[c_1574]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_9962,plain,
% 11.42/2.04      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.42/2.04      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top
% 11.42/2.04      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_tops_1(sK0,X0)) = iProver_top ),
% 11.42/2.04      inference(global_propositional_subsumption,
% 11.42/2.04                [status(thm)],
% 11.42/2.04                [c_9429,c_28,c_1339,c_1587]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_1883,plain,
% 11.42/2.04      ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 11.42/2.04      inference(superposition,[status(thm)],[c_1271,c_1261]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_2233,plain,
% 11.42/2.04      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.42/2.04      | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.42/2.04      | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top
% 11.42/2.04      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0)) = iProver_top ),
% 11.42/2.04      inference(superposition,[status(thm)],[c_1883,c_1262]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_1335,plain,
% 11.42/2.04      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.42/2.04      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.42/2.04      inference(instantiation,[status(thm)],[c_538]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_1336,plain,
% 11.42/2.04      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 11.42/2.04      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.42/2.04      inference(predicate_to_equality,[status(thm)],[c_1335]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_2417,plain,
% 11.42/2.04      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.42/2.04      | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top
% 11.42/2.04      | r1_tarski(k1_tops_1(sK0,sK1),k1_tops_1(sK0,X0)) = iProver_top ),
% 11.42/2.04      inference(global_propositional_subsumption,
% 11.42/2.04                [status(thm)],
% 11.42/2.04                [c_2233,c_28,c_1336]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_0,plain,
% 11.42/2.04      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.42/2.04      inference(cnf_transformation,[],[f56]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_1273,plain,
% 11.42/2.04      ( X0 = X1
% 11.42/2.04      | r1_tarski(X0,X1) != iProver_top
% 11.42/2.04      | r1_tarski(X1,X0) != iProver_top ),
% 11.42/2.04      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_2424,plain,
% 11.42/2.04      ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,sK1)
% 11.42/2.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.42/2.04      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) != iProver_top
% 11.42/2.04      | r1_tarski(k1_tops_1(sK0,sK1),X0) != iProver_top ),
% 11.42/2.04      inference(superposition,[status(thm)],[c_2417,c_1273]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_9976,plain,
% 11.42/2.04      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 11.42/2.04      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.42/2.04      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.42/2.04      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) != iProver_top
% 11.42/2.04      | r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) != iProver_top ),
% 11.42/2.04      inference(superposition,[status(thm)],[c_9962,c_2424]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_4,plain,
% 11.42/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.42/2.04      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 11.42/2.04      | ~ l1_pre_topc(X1) ),
% 11.42/2.04      inference(cnf_transformation,[],[f58]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_549,plain,
% 11.42/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.42/2.04      | r1_tarski(X0,k2_pre_topc(X1,X0))
% 11.42/2.04      | sK0 != X1 ),
% 11.42/2.04      inference(resolution_lifted,[status(thm)],[c_4,c_24]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_550,plain,
% 11.42/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.42/2.04      | r1_tarski(X0,k2_pre_topc(sK0,X0)) ),
% 11.42/2.04      inference(unflattening,[status(thm)],[c_549]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_1361,plain,
% 11.42/2.04      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.42/2.04      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
% 11.42/2.04      inference(instantiation,[status(thm)],[c_550]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_1362,plain,
% 11.42/2.04      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.42/2.04      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) = iProver_top ),
% 11.42/2.04      inference(predicate_to_equality,[status(thm)],[c_1361]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_7,plain,
% 11.42/2.04      ( ~ v4_tops_1(X0,X1)
% 11.42/2.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.42/2.04      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 11.42/2.04      | ~ l1_pre_topc(X1) ),
% 11.42/2.04      inference(cnf_transformation,[],[f59]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_22,negated_conjecture,
% 11.42/2.04      ( v4_tops_1(sK1,sK0) ),
% 11.42/2.04      inference(cnf_transformation,[],[f78]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_319,plain,
% 11.42/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.42/2.04      | r1_tarski(k1_tops_1(X1,k2_pre_topc(X1,X0)),X0)
% 11.42/2.04      | ~ l1_pre_topc(X1)
% 11.42/2.04      | sK1 != X0
% 11.42/2.04      | sK0 != X1 ),
% 11.42/2.04      inference(resolution_lifted,[status(thm)],[c_7,c_22]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_320,plain,
% 11.42/2.04      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.42/2.04      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1)
% 11.42/2.04      | ~ l1_pre_topc(sK0) ),
% 11.42/2.04      inference(unflattening,[status(thm)],[c_319]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_322,plain,
% 11.42/2.04      ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) ),
% 11.42/2.04      inference(global_propositional_subsumption,
% 11.42/2.04                [status(thm)],
% 11.42/2.04                [c_320,c_24,c_23]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_1270,plain,
% 11.42/2.04      ( r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),sK1) = iProver_top ),
% 11.42/2.04      inference(predicate_to_equality,[status(thm)],[c_322]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_2235,plain,
% 11.42/2.04      ( k1_tops_1(sK0,X0) = k1_tops_1(sK0,X1)
% 11.42/2.04      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.42/2.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.42/2.04      | r1_tarski(X1,X0) != iProver_top
% 11.42/2.04      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,X1)) != iProver_top ),
% 11.42/2.04      inference(superposition,[status(thm)],[c_1262,c_1273]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_9974,plain,
% 11.42/2.04      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,X0)
% 11.42/2.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.42/2.04      | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.42/2.04      | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
% 11.42/2.04      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top ),
% 11.42/2.04      inference(superposition,[status(thm)],[c_9962,c_2235]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_12709,plain,
% 11.42/2.04      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.42/2.04      | k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,X0)
% 11.42/2.04      | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
% 11.42/2.04      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top ),
% 11.42/2.04      inference(global_propositional_subsumption,
% 11.42/2.04                [status(thm)],
% 11.42/2.04                [c_9974,c_28,c_1339]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_12710,plain,
% 11.42/2.04      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,X0)
% 11.42/2.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.42/2.04      | r1_tarski(X0,k2_pre_topc(sK0,sK1)) != iProver_top
% 11.42/2.04      | r1_tarski(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),X0) != iProver_top ),
% 11.42/2.04      inference(renaming,[status(thm)],[c_12709]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_12716,plain,
% 11.42/2.04      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 11.42/2.04      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.42/2.04      | r1_tarski(sK1,k2_pre_topc(sK0,sK1)) != iProver_top ),
% 11.42/2.04      inference(superposition,[status(thm)],[c_1270,c_12710]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_18813,plain,
% 11.42/2.04      ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 11.42/2.04      inference(global_propositional_subsumption,
% 11.42/2.04                [status(thm)],
% 11.42/2.04                [c_9976,c_28,c_1362,c_12716]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_17,plain,
% 11.42/2.04      ( ~ v4_pre_topc(X0,X1)
% 11.42/2.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.42/2.04      | ~ v2_pre_topc(X1)
% 11.42/2.04      | ~ l1_pre_topc(X1)
% 11.42/2.04      | k7_subset_1(u1_struct_0(X1),X0,k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 11.42/2.04      inference(cnf_transformation,[],[f70]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_25,negated_conjecture,
% 11.42/2.04      ( v2_pre_topc(sK0) ),
% 11.42/2.04      inference(cnf_transformation,[],[f75]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_402,plain,
% 11.42/2.04      ( ~ v4_pre_topc(X0,X1)
% 11.42/2.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.42/2.04      | ~ l1_pre_topc(X1)
% 11.42/2.04      | k7_subset_1(u1_struct_0(X1),X0,k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 11.42/2.04      | sK0 != X1 ),
% 11.42/2.04      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_403,plain,
% 11.42/2.04      ( ~ v4_pre_topc(X0,sK0)
% 11.42/2.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.42/2.04      | ~ l1_pre_topc(sK0)
% 11.42/2.04      | k7_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 11.42/2.04      inference(unflattening,[status(thm)],[c_402]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_407,plain,
% 11.42/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.42/2.04      | ~ v4_pre_topc(X0,sK0)
% 11.42/2.04      | k7_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 11.42/2.04      inference(global_propositional_subsumption,
% 11.42/2.04                [status(thm)],
% 11.42/2.04                [c_403,c_24]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_408,plain,
% 11.42/2.04      ( ~ v4_pre_topc(X0,sK0)
% 11.42/2.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.42/2.04      | k7_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 11.42/2.04      inference(renaming,[status(thm)],[c_407]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_1265,plain,
% 11.42/2.04      ( k7_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 11.42/2.04      | v4_pre_topc(X0,sK0) != iProver_top
% 11.42/2.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.42/2.04      inference(predicate_to_equality,[status(thm)],[c_408]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_3862,plain,
% 11.42/2.04      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0))
% 11.42/2.04      | v4_pre_topc(k2_pre_topc(sK0,X0),sK0) != iProver_top
% 11.42/2.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.42/2.04      inference(superposition,[status(thm)],[c_1256,c_1265]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_11,plain,
% 11.42/2.04      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 11.42/2.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.42/2.04      | ~ v2_pre_topc(X0)
% 11.42/2.04      | ~ l1_pre_topc(X0) ),
% 11.42/2.04      inference(cnf_transformation,[],[f65]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_345,plain,
% 11.42/2.04      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 11.42/2.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.42/2.04      | ~ l1_pre_topc(X0)
% 11.42/2.04      | sK0 != X0 ),
% 11.42/2.04      inference(resolution_lifted,[status(thm)],[c_11,c_25]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_346,plain,
% 11.42/2.04      ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
% 11.42/2.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.42/2.04      | ~ l1_pre_topc(sK0) ),
% 11.42/2.04      inference(unflattening,[status(thm)],[c_345]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_350,plain,
% 11.42/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.42/2.04      | v4_pre_topc(k2_pre_topc(sK0,X0),sK0) ),
% 11.42/2.04      inference(global_propositional_subsumption,
% 11.42/2.04                [status(thm)],
% 11.42/2.04                [c_346,c_24]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_351,plain,
% 11.42/2.04      ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
% 11.42/2.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.42/2.04      inference(renaming,[status(thm)],[c_350]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_611,plain,
% 11.42/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.42/2.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.42/2.04      | k7_subset_1(u1_struct_0(sK0),X0,k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 11.42/2.04      | k2_pre_topc(sK0,X1) != X0
% 11.42/2.04      | sK0 != sK0 ),
% 11.42/2.04      inference(resolution_lifted,[status(thm)],[c_351,c_408]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_612,plain,
% 11.42/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.42/2.04      | ~ m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.42/2.04      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0)) ),
% 11.42/2.04      inference(unflattening,[status(thm)],[c_611]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_616,plain,
% 11.42/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.42/2.04      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0)) ),
% 11.42/2.04      inference(global_propositional_subsumption,
% 11.42/2.04                [status(thm)],
% 11.42/2.04                [c_612,c_562]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_618,plain,
% 11.42/2.04      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0))
% 11.42/2.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.42/2.04      inference(predicate_to_equality,[status(thm)],[c_616]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_21467,plain,
% 11.42/2.04      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0))
% 11.42/2.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.42/2.04      inference(global_propositional_subsumption,
% 11.42/2.04                [status(thm)],
% 11.42/2.04                [c_3862,c_618]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_21471,plain,
% 11.42/2.04      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
% 11.42/2.04      inference(superposition,[status(thm)],[c_1271,c_21467]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_21486,plain,
% 11.42/2.04      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
% 11.42/2.04      inference(superposition,[status(thm)],[c_18813,c_21471]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_22037,plain,
% 11.42/2.04      ( k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.42/2.04      inference(superposition,[status(thm)],[c_2056,c_21486]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_19,plain,
% 11.42/2.04      ( ~ v3_tops_1(X0,X1)
% 11.42/2.04      | ~ v4_pre_topc(X0,X1)
% 11.42/2.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.42/2.04      | ~ l1_pre_topc(X1)
% 11.42/2.04      | k2_tops_1(X1,X0) = X0 ),
% 11.42/2.04      inference(cnf_transformation,[],[f72]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_20,plain,
% 11.42/2.04      ( v3_tops_1(k2_tops_1(X0,X1),X0)
% 11.42/2.04      | ~ v4_pre_topc(X1,X0)
% 11.42/2.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.42/2.04      | ~ v2_pre_topc(X0)
% 11.42/2.04      | ~ l1_pre_topc(X0) ),
% 11.42/2.04      inference(cnf_transformation,[],[f74]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_279,plain,
% 11.42/2.04      ( ~ v4_pre_topc(X0,X1)
% 11.42/2.04      | ~ v4_pre_topc(X2,X3)
% 11.42/2.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.42/2.04      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 11.42/2.04      | ~ v2_pre_topc(X3)
% 11.42/2.04      | ~ l1_pre_topc(X1)
% 11.42/2.04      | ~ l1_pre_topc(X3)
% 11.42/2.04      | X3 != X1
% 11.42/2.04      | k2_tops_1(X3,X2) != X0
% 11.42/2.04      | k2_tops_1(X1,X0) = X0 ),
% 11.42/2.04      inference(resolution_lifted,[status(thm)],[c_19,c_20]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_280,plain,
% 11.42/2.04      ( ~ v4_pre_topc(X0,X1)
% 11.42/2.04      | ~ v4_pre_topc(k2_tops_1(X1,X0),X1)
% 11.42/2.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.42/2.04      | ~ m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.42/2.04      | ~ v2_pre_topc(X1)
% 11.42/2.04      | ~ l1_pre_topc(X1)
% 11.42/2.04      | k2_tops_1(X1,k2_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 11.42/2.04      inference(unflattening,[status(thm)],[c_279]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_9,plain,
% 11.42/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.42/2.04      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.42/2.04      | ~ l1_pre_topc(X1) ),
% 11.42/2.04      inference(cnf_transformation,[],[f63]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_284,plain,
% 11.42/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.42/2.04      | ~ v4_pre_topc(k2_tops_1(X1,X0),X1)
% 11.42/2.04      | ~ v4_pre_topc(X0,X1)
% 11.42/2.04      | ~ v2_pre_topc(X1)
% 11.42/2.04      | ~ l1_pre_topc(X1)
% 11.42/2.04      | k2_tops_1(X1,k2_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 11.42/2.04      inference(global_propositional_subsumption,
% 11.42/2.04                [status(thm)],
% 11.42/2.04                [c_280,c_9]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_285,plain,
% 11.42/2.04      ( ~ v4_pre_topc(X0,X1)
% 11.42/2.04      | ~ v4_pre_topc(k2_tops_1(X1,X0),X1)
% 11.42/2.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.42/2.04      | ~ v2_pre_topc(X1)
% 11.42/2.04      | ~ l1_pre_topc(X1)
% 11.42/2.04      | k2_tops_1(X1,k2_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 11.42/2.04      inference(renaming,[status(thm)],[c_284]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_10,plain,
% 11.42/2.04      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
% 11.42/2.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.42/2.04      | ~ v2_pre_topc(X0)
% 11.42/2.04      | ~ l1_pre_topc(X0) ),
% 11.42/2.04      inference(cnf_transformation,[],[f64]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_302,plain,
% 11.42/2.04      ( ~ v4_pre_topc(X0,X1)
% 11.42/2.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.42/2.04      | ~ v2_pre_topc(X1)
% 11.42/2.04      | ~ l1_pre_topc(X1)
% 11.42/2.04      | k2_tops_1(X1,k2_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 11.42/2.04      inference(forward_subsumption_resolution,
% 11.42/2.04                [status(thm)],
% 11.42/2.04                [c_285,c_10]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_381,plain,
% 11.42/2.04      ( ~ v4_pre_topc(X0,X1)
% 11.42/2.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.42/2.04      | ~ l1_pre_topc(X1)
% 11.42/2.04      | k2_tops_1(X1,k2_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 11.42/2.04      | sK0 != X1 ),
% 11.42/2.04      inference(resolution_lifted,[status(thm)],[c_302,c_25]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_382,plain,
% 11.42/2.04      ( ~ v4_pre_topc(X0,sK0)
% 11.42/2.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.42/2.04      | ~ l1_pre_topc(sK0)
% 11.42/2.04      | k2_tops_1(sK0,k2_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 11.42/2.04      inference(unflattening,[status(thm)],[c_381]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_386,plain,
% 11.42/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.42/2.04      | ~ v4_pre_topc(X0,sK0)
% 11.42/2.04      | k2_tops_1(sK0,k2_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 11.42/2.04      inference(global_propositional_subsumption,
% 11.42/2.04                [status(thm)],
% 11.42/2.04                [c_382,c_24]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_387,plain,
% 11.42/2.04      ( ~ v4_pre_topc(X0,sK0)
% 11.42/2.04      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.42/2.04      | k2_tops_1(sK0,k2_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 11.42/2.04      inference(renaming,[status(thm)],[c_386]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_1266,plain,
% 11.42/2.04      ( k2_tops_1(sK0,k2_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 11.42/2.04      | v4_pre_topc(X0,sK0) != iProver_top
% 11.42/2.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.42/2.04      inference(predicate_to_equality,[status(thm)],[c_387]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_4712,plain,
% 11.42/2.04      ( k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0))
% 11.42/2.04      | v4_pre_topc(k2_pre_topc(sK0,X0),sK0) != iProver_top
% 11.42/2.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.42/2.04      inference(superposition,[status(thm)],[c_1256,c_1266]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_629,plain,
% 11.42/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.42/2.04      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.42/2.04      | k2_tops_1(sK0,k2_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 11.42/2.04      | k2_pre_topc(sK0,X1) != X0
% 11.42/2.04      | sK0 != sK0 ),
% 11.42/2.04      inference(resolution_lifted,[status(thm)],[c_351,c_387]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_630,plain,
% 11.42/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.42/2.04      | ~ m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.42/2.04      | k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0)) ),
% 11.42/2.04      inference(unflattening,[status(thm)],[c_629]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_634,plain,
% 11.42/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.42/2.04      | k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0)) ),
% 11.42/2.04      inference(global_propositional_subsumption,
% 11.42/2.04                [status(thm)],
% 11.42/2.04                [c_630,c_562]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_636,plain,
% 11.42/2.04      ( k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0))
% 11.42/2.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.42/2.04      inference(predicate_to_equality,[status(thm)],[c_634]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_30768,plain,
% 11.42/2.04      ( k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0))) = k2_tops_1(sK0,k2_pre_topc(sK0,X0))
% 11.42/2.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.42/2.04      inference(global_propositional_subsumption,
% 11.42/2.04                [status(thm)],
% 11.42/2.04                [c_4712,c_636]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_30772,plain,
% 11.42/2.04      ( k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
% 11.42/2.04      inference(superposition,[status(thm)],[c_1271,c_30768]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_13,plain,
% 11.42/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.42/2.04      | ~ v2_pre_topc(X1)
% 11.42/2.04      | ~ l1_pre_topc(X1)
% 11.42/2.04      | k1_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X0))) = k1_xboole_0 ),
% 11.42/2.04      inference(cnf_transformation,[],[f67]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_444,plain,
% 11.42/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.42/2.04      | ~ l1_pre_topc(X1)
% 11.42/2.04      | k1_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X0))) = k1_xboole_0
% 11.42/2.04      | sK0 != X1 ),
% 11.42/2.04      inference(resolution_lifted,[status(thm)],[c_13,c_25]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_445,plain,
% 11.42/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.42/2.04      | ~ l1_pre_topc(sK0)
% 11.42/2.04      | k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) = k1_xboole_0 ),
% 11.42/2.04      inference(unflattening,[status(thm)],[c_444]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_449,plain,
% 11.42/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.42/2.04      | k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) = k1_xboole_0 ),
% 11.42/2.04      inference(global_propositional_subsumption,
% 11.42/2.04                [status(thm)],
% 11.42/2.04                [c_445,c_24]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_1263,plain,
% 11.42/2.04      ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) = k1_xboole_0
% 11.42/2.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.42/2.04      inference(predicate_to_equality,[status(thm)],[c_449]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_2772,plain,
% 11.42/2.04      ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,X0)))) = k1_xboole_0
% 11.42/2.04      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.42/2.04      inference(superposition,[status(thm)],[c_1256,c_1263]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_13822,plain,
% 11.42/2.04      ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1)))) = k1_xboole_0 ),
% 11.42/2.04      inference(superposition,[status(thm)],[c_1271,c_2772]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_30806,plain,
% 11.42/2.04      ( k1_tops_1(sK0,k2_tops_1(sK0,k2_pre_topc(sK0,sK1))) = k1_xboole_0 ),
% 11.42/2.04      inference(superposition,[status(thm)],[c_30772,c_13822]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_31079,plain,
% 11.42/2.04      ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) = k1_xboole_0 ),
% 11.42/2.04      inference(superposition,[status(thm)],[c_22037,c_30806]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(c_21,negated_conjecture,
% 11.42/2.04      ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0 ),
% 11.42/2.04      inference(cnf_transformation,[],[f79]) ).
% 11.42/2.04  
% 11.42/2.04  cnf(contradiction,plain,
% 11.42/2.04      ( $false ),
% 11.42/2.04      inference(minisat,[status(thm)],[c_31079,c_21]) ).
% 11.42/2.04  
% 11.42/2.04  
% 11.42/2.04  % SZS output end CNFRefutation for theBenchmark.p
% 11.42/2.04  
% 11.42/2.04  ------                               Statistics
% 11.42/2.04  
% 11.42/2.04  ------ Selected
% 11.42/2.04  
% 11.42/2.04  total_time:                             1.227
% 11.42/2.04  
%------------------------------------------------------------------------------
