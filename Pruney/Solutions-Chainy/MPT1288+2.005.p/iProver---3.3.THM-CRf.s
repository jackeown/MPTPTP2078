%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:15:57 EST 2020

% Result     : Theorem 11.41s
% Output     : CNFRefutation 11.41s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 624 expanded)
%              Number of clauses        :  108 ( 192 expanded)
%              Number of leaves         :   19 ( 147 expanded)
%              Depth                    :   24
%              Number of atoms          :  633 (2631 expanded)
%              Number of equality atoms :  150 ( 545 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
           => k1_tops_1(X0,k2_tops_1(X0,X1)) = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_tops_1(X1,X0)
             => k1_tops_1(X0,k2_tops_1(X0,X1)) = k1_xboole_0 ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0
          & v4_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k1_tops_1(X0,k2_tops_1(X0,sK1)) != k1_xboole_0
        & v4_tops_1(sK1,X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
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

fof(f55,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0
    & v4_tops_1(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f47,f54,f53])).

fof(f79,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f55])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f78,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_tops_1(X1,X0)
          <=> ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
              & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1)))
      | ~ v4_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
    v4_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f77,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X2,X1)
                  & v4_pre_topc(X1,X0) )
               => r1_tarski(k2_pre_topc(X0,X2),X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X2),X1)
              | ~ r1_tarski(X2,X1)
              | ~ v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => ( v3_tops_1(X1,X0)
            <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> k2_tops_1(X0,X1) = X1 )
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tops_1(X1,X0)
          <=> k2_tops_1(X0,X1) = X1 )
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tops_1(X1,X0)
              | k2_tops_1(X0,X1) != X1 )
            & ( k2_tops_1(X0,X1) = X1
              | ~ v3_tops_1(X1,X0) ) )
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = X1
      | ~ v3_tops_1(X1,X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
           => v3_tops_1(k2_tops_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(k2_tops_1(X0,X1),X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(k2_tops_1(X0,X1),X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v3_tops_1(k2_tops_1(X0,X1),X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f81,plain,(
    k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1378,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_644,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_24])).

cnf(c_645,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_644])).

cnf(c_1366,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_645])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_656,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_24])).

cnf(c_657,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,X1)
    | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1)) ),
    inference(unflattening,[status(thm)],[c_656])).

cnf(c_1365,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_657])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1380,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3062,plain,
    ( k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1365,c_1380])).

cnf(c_3216,plain,
    ( k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1365,c_3062])).

cnf(c_5767,plain,
    ( k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(X0,sK1) != iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1378,c_3216])).

cnf(c_5891,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = k2_pre_topc(sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | r1_tarski(k1_tops_1(sK0,X0),sK1) != iProver_top
    | r1_tarski(sK1,k1_tops_1(sK0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1366,c_5767])).

cnf(c_44686,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top
    | r1_tarski(sK1,k1_tops_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1378,c_5891])).

cnf(c_6,plain,
    ( ~ v4_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_22,negated_conjecture,
    ( v4_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_434,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
    | ~ l1_pre_topc(X1)
    | sK1 != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_22])).

cnf(c_435,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_1508,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_645])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_575,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_24])).

cnf(c_576,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,X0),X0) ),
    inference(unflattening,[status(thm)],[c_575])).

cnf(c_1517,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(instantiation,[status(thm)],[c_576])).

cnf(c_11,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_325,plain,
    ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_25])).

cnf(c_326,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_325])).

cnf(c_330,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k2_pre_topc(sK0,X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_326,c_24])).

cnf(c_331,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_330])).

cnf(c_1630,plain,
    ( v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_331])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_674,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_24])).

cnf(c_675,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_674])).

cnf(c_1625,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_675])).

cnf(c_1621,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),X0)
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,X0)) ),
    inference(instantiation,[status(thm)],[c_657])).

cnf(c_6072,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1621])).

cnf(c_16,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k2_pre_topc(X1,X2),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_587,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | r1_tarski(k2_pre_topc(X1,X2),X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_24])).

cnf(c_588,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X1,X0)
    | r1_tarski(k2_pre_topc(sK0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_587])).

cnf(c_2161,plain,
    ( ~ v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_588])).

cnf(c_6575,plain,
    ( ~ v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | ~ r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_2161])).

cnf(c_5666,plain,
    ( ~ r1_tarski(X0,k2_pre_topc(sK0,sK1))
    | ~ r1_tarski(k2_pre_topc(sK0,sK1),X0)
    | X0 = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_19205,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1))
    | ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
    | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_5666])).

cnf(c_44736,plain,
    ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_44686,c_24,c_23,c_435,c_1508,c_1517,c_1630,c_1625,c_6072,c_6575,c_19205])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_620,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_24])).

cnf(c_621,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_620])).

cnf(c_1368,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_621])).

cnf(c_3400,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,X0)),k1_tops_1(sK0,k1_tops_1(sK0,X0))) = k2_tops_1(sK0,k1_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1366,c_1368])).

cnf(c_7918,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_1378,c_3400])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_608,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_609,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_608])).

cnf(c_1369,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_609])).

cnf(c_2549,plain,
    ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1378,c_1369])).

cnf(c_7939,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    inference(light_normalisation,[status(thm)],[c_7918,c_2549])).

cnf(c_44759,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    inference(demodulation,[status(thm)],[c_44736,c_7939])).

cnf(c_3397,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1378,c_1368])).

cnf(c_44771,plain,
    ( k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_44759,c_3397])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_632,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_24])).

cnf(c_633,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_632])).

cnf(c_1367,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_633])).

cnf(c_19,plain,
    ( ~ v3_tops_1(X0,X1)
    | ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_12,plain,
    ( v3_pre_topc(k1_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_20,plain,
    ( v3_tops_1(k2_tops_1(X0,X1),X0)
    | ~ v3_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_279,plain,
    ( v3_tops_1(k2_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X0)
    | X0 != X3
    | k1_tops_1(X3,X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_280,plain,
    ( v3_tops_1(k2_tops_1(X0,k1_tops_1(X0,X1)),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(unflattening,[status(thm)],[c_279])).

cnf(c_294,plain,
    ( v3_tops_1(k2_tops_1(X0,k1_tops_1(X0,X1)),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_280,c_8])).

cnf(c_307,plain,
    ( v3_tops_1(k2_tops_1(X0,k1_tops_1(X0,X1)),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_294,c_25])).

cnf(c_308,plain,
    ( v3_tops_1(k2_tops_1(sK0,k1_tops_1(sK0,X0)),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_307])).

cnf(c_312,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tops_1(k2_tops_1(sK0,k1_tops_1(sK0,X0)),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_308,c_24])).

cnf(c_313,plain,
    ( v3_tops_1(k2_tops_1(sK0,k1_tops_1(sK0,X0)),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_312])).

cnf(c_392,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(X1)
    | k2_tops_1(X1,X0) = X0
    | k2_tops_1(sK0,k1_tops_1(sK0,X2)) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_313])).

cnf(c_393,plain,
    ( ~ v4_pre_topc(k2_tops_1(sK0,k1_tops_1(sK0,X0)),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,X0))) = k2_tops_1(sK0,k1_tops_1(sK0,X0)) ),
    inference(unflattening,[status(thm)],[c_392])).

cnf(c_397,plain,
    ( ~ m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_pre_topc(k2_tops_1(sK0,k1_tops_1(sK0,X0)),sK0)
    | k2_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,X0))) = k2_tops_1(sK0,k1_tops_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_393,c_24])).

cnf(c_398,plain,
    ( ~ v4_pre_topc(k2_tops_1(sK0,k1_tops_1(sK0,X0)),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,X0))) = k2_tops_1(sK0,k1_tops_1(sK0,X0)) ),
    inference(renaming,[status(thm)],[c_397])).

cnf(c_1374,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,X0))) = k2_tops_1(sK0,k1_tops_1(sK0,X0))
    | v4_pre_topc(k2_tops_1(sK0,k1_tops_1(sK0,X0)),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_398])).

cnf(c_27,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_394,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,X0))) = k2_tops_1(sK0,k1_tops_1(sK0,X0))
    | v4_pre_topc(k2_tops_1(sK0,k1_tops_1(sK0,X0)),sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_393])).

cnf(c_10,plain,
    ( v4_pre_topc(k2_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_343,plain,
    ( v4_pre_topc(k2_tops_1(X0,X1),X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_25])).

cnf(c_344,plain,
    ( v4_pre_topc(k2_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_343])).

cnf(c_348,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k2_tops_1(sK0,X0),sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_344,c_24])).

cnf(c_349,plain,
    ( v4_pre_topc(k2_tops_1(sK0,X0),sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(renaming,[status(thm)],[c_348])).

cnf(c_1376,plain,
    ( v4_pre_topc(k2_tops_1(sK0,X0),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_349])).

cnf(c_2332,plain,
    ( v4_pre_topc(k2_tops_1(sK0,k1_tops_1(sK0,X0)),sK0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1366,c_1376])).

cnf(c_4162,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,X0))) = k2_tops_1(sK0,k1_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1374,c_27,c_394,c_2332])).

cnf(c_4171,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,X0))) = k2_tops_1(sK0,k1_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1367,c_4162])).

cnf(c_646,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_645])).

cnf(c_18944,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k2_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,X0))) = k2_tops_1(sK0,k1_tops_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4171,c_646])).

cnf(c_18945,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,X0))) = k2_tops_1(sK0,k1_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_18944])).

cnf(c_18952,plain,
    ( k2_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_1378,c_18945])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X0))) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_361,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X0))) = k1_xboole_0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_25])).

cnf(c_362,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_361])).

cnf(c_366,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_362,c_24])).

cnf(c_1375,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_366])).

cnf(c_2877,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,X0)))) = k1_xboole_0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1366,c_1375])).

cnf(c_5448,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1378,c_2877])).

cnf(c_19009,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_18952,c_5448])).

cnf(c_45038,plain,
    ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_44771,c_19009])).

cnf(c_21,negated_conjecture,
    ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f81])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_45038,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.32  % Computer   : n006.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 14:55:37 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 11.41/1.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.41/1.98  
% 11.41/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.41/1.98  
% 11.41/1.98  ------  iProver source info
% 11.41/1.98  
% 11.41/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.41/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.41/1.98  git: non_committed_changes: false
% 11.41/1.98  git: last_make_outside_of_git: false
% 11.41/1.98  
% 11.41/1.98  ------ 
% 11.41/1.98  
% 11.41/1.98  ------ Input Options
% 11.41/1.98  
% 11.41/1.98  --out_options                           all
% 11.41/1.98  --tptp_safe_out                         true
% 11.41/1.98  --problem_path                          ""
% 11.41/1.98  --include_path                          ""
% 11.41/1.98  --clausifier                            res/vclausify_rel
% 11.41/1.98  --clausifier_options                    --mode clausify
% 11.41/1.98  --stdin                                 false
% 11.41/1.98  --stats_out                             all
% 11.41/1.98  
% 11.41/1.98  ------ General Options
% 11.41/1.98  
% 11.41/1.98  --fof                                   false
% 11.41/1.98  --time_out_real                         305.
% 11.41/1.98  --time_out_virtual                      -1.
% 11.41/1.98  --symbol_type_check                     false
% 11.41/1.98  --clausify_out                          false
% 11.41/1.98  --sig_cnt_out                           false
% 11.41/1.98  --trig_cnt_out                          false
% 11.41/1.98  --trig_cnt_out_tolerance                1.
% 11.41/1.98  --trig_cnt_out_sk_spl                   false
% 11.41/1.98  --abstr_cl_out                          false
% 11.41/1.98  
% 11.41/1.98  ------ Global Options
% 11.41/1.98  
% 11.41/1.98  --schedule                              default
% 11.41/1.98  --add_important_lit                     false
% 11.41/1.98  --prop_solver_per_cl                    1000
% 11.41/1.98  --min_unsat_core                        false
% 11.41/1.98  --soft_assumptions                      false
% 11.41/1.98  --soft_lemma_size                       3
% 11.41/1.98  --prop_impl_unit_size                   0
% 11.41/1.98  --prop_impl_unit                        []
% 11.41/1.98  --share_sel_clauses                     true
% 11.41/1.98  --reset_solvers                         false
% 11.41/1.98  --bc_imp_inh                            [conj_cone]
% 11.41/1.98  --conj_cone_tolerance                   3.
% 11.41/1.98  --extra_neg_conj                        none
% 11.41/1.98  --large_theory_mode                     true
% 11.41/1.98  --prolific_symb_bound                   200
% 11.41/1.98  --lt_threshold                          2000
% 11.41/1.98  --clause_weak_htbl                      true
% 11.41/1.98  --gc_record_bc_elim                     false
% 11.41/1.98  
% 11.41/1.98  ------ Preprocessing Options
% 11.41/1.98  
% 11.41/1.98  --preprocessing_flag                    true
% 11.41/1.98  --time_out_prep_mult                    0.1
% 11.41/1.98  --splitting_mode                        input
% 11.41/1.98  --splitting_grd                         true
% 11.41/1.98  --splitting_cvd                         false
% 11.41/1.98  --splitting_cvd_svl                     false
% 11.41/1.98  --splitting_nvd                         32
% 11.41/1.98  --sub_typing                            true
% 11.41/1.98  --prep_gs_sim                           true
% 11.41/1.98  --prep_unflatten                        true
% 11.41/1.98  --prep_res_sim                          true
% 11.41/1.98  --prep_upred                            true
% 11.41/1.98  --prep_sem_filter                       exhaustive
% 11.41/1.98  --prep_sem_filter_out                   false
% 11.41/1.98  --pred_elim                             true
% 11.41/1.98  --res_sim_input                         true
% 11.41/1.98  --eq_ax_congr_red                       true
% 11.41/1.98  --pure_diseq_elim                       true
% 11.41/1.98  --brand_transform                       false
% 11.41/1.98  --non_eq_to_eq                          false
% 11.41/1.98  --prep_def_merge                        true
% 11.41/1.98  --prep_def_merge_prop_impl              false
% 11.41/1.98  --prep_def_merge_mbd                    true
% 11.41/1.98  --prep_def_merge_tr_red                 false
% 11.41/1.98  --prep_def_merge_tr_cl                  false
% 11.41/1.98  --smt_preprocessing                     true
% 11.41/1.98  --smt_ac_axioms                         fast
% 11.41/1.98  --preprocessed_out                      false
% 11.41/1.98  --preprocessed_stats                    false
% 11.41/1.98  
% 11.41/1.98  ------ Abstraction refinement Options
% 11.41/1.98  
% 11.41/1.98  --abstr_ref                             []
% 11.41/1.98  --abstr_ref_prep                        false
% 11.41/1.98  --abstr_ref_until_sat                   false
% 11.41/1.98  --abstr_ref_sig_restrict                funpre
% 11.41/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.41/1.98  --abstr_ref_under                       []
% 11.41/1.98  
% 11.41/1.98  ------ SAT Options
% 11.41/1.98  
% 11.41/1.98  --sat_mode                              false
% 11.41/1.98  --sat_fm_restart_options                ""
% 11.41/1.98  --sat_gr_def                            false
% 11.41/1.98  --sat_epr_types                         true
% 11.41/1.98  --sat_non_cyclic_types                  false
% 11.41/1.98  --sat_finite_models                     false
% 11.41/1.98  --sat_fm_lemmas                         false
% 11.41/1.98  --sat_fm_prep                           false
% 11.41/1.98  --sat_fm_uc_incr                        true
% 11.41/1.98  --sat_out_model                         small
% 11.41/1.98  --sat_out_clauses                       false
% 11.41/1.98  
% 11.41/1.98  ------ QBF Options
% 11.41/1.98  
% 11.41/1.98  --qbf_mode                              false
% 11.41/1.98  --qbf_elim_univ                         false
% 11.41/1.98  --qbf_dom_inst                          none
% 11.41/1.98  --qbf_dom_pre_inst                      false
% 11.41/1.98  --qbf_sk_in                             false
% 11.41/1.98  --qbf_pred_elim                         true
% 11.41/1.98  --qbf_split                             512
% 11.41/1.98  
% 11.41/1.98  ------ BMC1 Options
% 11.41/1.98  
% 11.41/1.98  --bmc1_incremental                      false
% 11.41/1.98  --bmc1_axioms                           reachable_all
% 11.41/1.98  --bmc1_min_bound                        0
% 11.41/1.98  --bmc1_max_bound                        -1
% 11.41/1.98  --bmc1_max_bound_default                -1
% 11.41/1.98  --bmc1_symbol_reachability              true
% 11.41/1.98  --bmc1_property_lemmas                  false
% 11.41/1.98  --bmc1_k_induction                      false
% 11.41/1.98  --bmc1_non_equiv_states                 false
% 11.41/1.98  --bmc1_deadlock                         false
% 11.41/1.98  --bmc1_ucm                              false
% 11.41/1.98  --bmc1_add_unsat_core                   none
% 11.41/1.98  --bmc1_unsat_core_children              false
% 11.41/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.41/1.98  --bmc1_out_stat                         full
% 11.41/1.98  --bmc1_ground_init                      false
% 11.41/1.98  --bmc1_pre_inst_next_state              false
% 11.41/1.98  --bmc1_pre_inst_state                   false
% 11.41/1.98  --bmc1_pre_inst_reach_state             false
% 11.41/1.98  --bmc1_out_unsat_core                   false
% 11.41/1.98  --bmc1_aig_witness_out                  false
% 11.41/1.98  --bmc1_verbose                          false
% 11.41/1.98  --bmc1_dump_clauses_tptp                false
% 11.41/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.41/1.98  --bmc1_dump_file                        -
% 11.41/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.41/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.41/1.98  --bmc1_ucm_extend_mode                  1
% 11.41/1.98  --bmc1_ucm_init_mode                    2
% 11.41/1.98  --bmc1_ucm_cone_mode                    none
% 11.41/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.41/1.98  --bmc1_ucm_relax_model                  4
% 11.41/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.41/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.41/1.98  --bmc1_ucm_layered_model                none
% 11.41/1.98  --bmc1_ucm_max_lemma_size               10
% 11.41/1.98  
% 11.41/1.98  ------ AIG Options
% 11.41/1.98  
% 11.41/1.98  --aig_mode                              false
% 11.41/1.98  
% 11.41/1.98  ------ Instantiation Options
% 11.41/1.98  
% 11.41/1.98  --instantiation_flag                    true
% 11.41/1.98  --inst_sos_flag                         false
% 11.41/1.98  --inst_sos_phase                        true
% 11.41/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.41/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.41/1.98  --inst_lit_sel_side                     num_symb
% 11.41/1.98  --inst_solver_per_active                1400
% 11.41/1.98  --inst_solver_calls_frac                1.
% 11.41/1.98  --inst_passive_queue_type               priority_queues
% 11.41/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.41/1.98  --inst_passive_queues_freq              [25;2]
% 11.41/1.98  --inst_dismatching                      true
% 11.41/1.98  --inst_eager_unprocessed_to_passive     true
% 11.41/1.98  --inst_prop_sim_given                   true
% 11.41/1.98  --inst_prop_sim_new                     false
% 11.41/1.98  --inst_subs_new                         false
% 11.41/1.98  --inst_eq_res_simp                      false
% 11.41/1.98  --inst_subs_given                       false
% 11.41/1.98  --inst_orphan_elimination               true
% 11.41/1.98  --inst_learning_loop_flag               true
% 11.41/1.98  --inst_learning_start                   3000
% 11.41/1.98  --inst_learning_factor                  2
% 11.41/1.98  --inst_start_prop_sim_after_learn       3
% 11.41/1.98  --inst_sel_renew                        solver
% 11.41/1.98  --inst_lit_activity_flag                true
% 11.41/1.98  --inst_restr_to_given                   false
% 11.41/1.98  --inst_activity_threshold               500
% 11.41/1.98  --inst_out_proof                        true
% 11.41/1.98  
% 11.41/1.98  ------ Resolution Options
% 11.41/1.98  
% 11.41/1.98  --resolution_flag                       true
% 11.41/1.98  --res_lit_sel                           adaptive
% 11.41/1.98  --res_lit_sel_side                      none
% 11.41/1.98  --res_ordering                          kbo
% 11.41/1.98  --res_to_prop_solver                    active
% 11.41/1.98  --res_prop_simpl_new                    false
% 11.41/1.98  --res_prop_simpl_given                  true
% 11.41/1.98  --res_passive_queue_type                priority_queues
% 11.41/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.41/1.98  --res_passive_queues_freq               [15;5]
% 11.41/1.98  --res_forward_subs                      full
% 11.41/1.98  --res_backward_subs                     full
% 11.41/1.98  --res_forward_subs_resolution           true
% 11.41/1.98  --res_backward_subs_resolution          true
% 11.41/1.98  --res_orphan_elimination                true
% 11.41/1.98  --res_time_limit                        2.
% 11.41/1.98  --res_out_proof                         true
% 11.41/1.98  
% 11.41/1.98  ------ Superposition Options
% 11.41/1.98  
% 11.41/1.98  --superposition_flag                    true
% 11.41/1.98  --sup_passive_queue_type                priority_queues
% 11.41/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.41/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.41/1.98  --demod_completeness_check              fast
% 11.41/1.98  --demod_use_ground                      true
% 11.41/1.98  --sup_to_prop_solver                    passive
% 11.41/1.98  --sup_prop_simpl_new                    true
% 11.41/1.98  --sup_prop_simpl_given                  true
% 11.41/1.98  --sup_fun_splitting                     false
% 11.41/1.98  --sup_smt_interval                      50000
% 11.41/1.98  
% 11.41/1.98  ------ Superposition Simplification Setup
% 11.41/1.98  
% 11.41/1.98  --sup_indices_passive                   []
% 11.41/1.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.41/1.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.41/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.41/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.41/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.41/1.98  --sup_full_bw                           [BwDemod]
% 11.41/1.98  --sup_immed_triv                        [TrivRules]
% 11.41/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.41/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.41/1.98  --sup_immed_bw_main                     []
% 11.41/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.41/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.41/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.41/1.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.41/1.98  
% 11.41/1.98  ------ Combination Options
% 11.41/1.98  
% 11.41/1.98  --comb_res_mult                         3
% 11.41/1.98  --comb_sup_mult                         2
% 11.41/1.98  --comb_inst_mult                        10
% 11.41/1.98  
% 11.41/1.98  ------ Debug Options
% 11.41/1.98  
% 11.41/1.98  --dbg_backtrace                         false
% 11.41/1.98  --dbg_dump_prop_clauses                 false
% 11.41/1.98  --dbg_dump_prop_clauses_file            -
% 11.41/1.98  --dbg_out_stat                          false
% 11.41/1.98  ------ Parsing...
% 11.41/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.41/1.98  
% 11.41/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 11.41/1.98  
% 11.41/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.41/1.98  
% 11.41/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.41/1.98  ------ Proving...
% 11.41/1.98  ------ Problem Properties 
% 11.41/1.98  
% 11.41/1.98  
% 11.41/1.98  clauses                                 18
% 11.41/1.98  conjectures                             2
% 11.41/1.98  EPR                                     2
% 11.41/1.98  Horn                                    18
% 11.41/1.98  unary                                   5
% 11.41/1.98  binary                                  9
% 11.41/1.98  lits                                    39
% 11.41/1.98  lits eq                                 6
% 11.41/1.98  fd_pure                                 0
% 11.41/1.98  fd_pseudo                               0
% 11.41/1.98  fd_cond                                 0
% 11.41/1.98  fd_pseudo_cond                          1
% 11.41/1.98  AC symbols                              0
% 11.41/1.98  
% 11.41/1.98  ------ Schedule dynamic 5 is on 
% 11.41/1.98  
% 11.41/1.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.41/1.98  
% 11.41/1.98  
% 11.41/1.98  ------ 
% 11.41/1.98  Current options:
% 11.41/1.98  ------ 
% 11.41/1.98  
% 11.41/1.98  ------ Input Options
% 11.41/1.98  
% 11.41/1.98  --out_options                           all
% 11.41/1.98  --tptp_safe_out                         true
% 11.41/1.98  --problem_path                          ""
% 11.41/1.98  --include_path                          ""
% 11.41/1.98  --clausifier                            res/vclausify_rel
% 11.41/1.98  --clausifier_options                    --mode clausify
% 11.41/1.98  --stdin                                 false
% 11.41/1.98  --stats_out                             all
% 11.41/1.98  
% 11.41/1.98  ------ General Options
% 11.41/1.98  
% 11.41/1.98  --fof                                   false
% 11.41/1.98  --time_out_real                         305.
% 11.41/1.98  --time_out_virtual                      -1.
% 11.41/1.98  --symbol_type_check                     false
% 11.41/1.98  --clausify_out                          false
% 11.41/1.98  --sig_cnt_out                           false
% 11.41/1.98  --trig_cnt_out                          false
% 11.41/1.98  --trig_cnt_out_tolerance                1.
% 11.41/1.98  --trig_cnt_out_sk_spl                   false
% 11.41/1.98  --abstr_cl_out                          false
% 11.41/1.98  
% 11.41/1.98  ------ Global Options
% 11.41/1.98  
% 11.41/1.98  --schedule                              default
% 11.41/1.98  --add_important_lit                     false
% 11.41/1.98  --prop_solver_per_cl                    1000
% 11.41/1.98  --min_unsat_core                        false
% 11.41/1.98  --soft_assumptions                      false
% 11.41/1.98  --soft_lemma_size                       3
% 11.41/1.98  --prop_impl_unit_size                   0
% 11.41/1.98  --prop_impl_unit                        []
% 11.41/1.98  --share_sel_clauses                     true
% 11.41/1.98  --reset_solvers                         false
% 11.41/1.98  --bc_imp_inh                            [conj_cone]
% 11.41/1.98  --conj_cone_tolerance                   3.
% 11.41/1.98  --extra_neg_conj                        none
% 11.41/1.98  --large_theory_mode                     true
% 11.41/1.98  --prolific_symb_bound                   200
% 11.41/1.98  --lt_threshold                          2000
% 11.41/1.98  --clause_weak_htbl                      true
% 11.41/1.98  --gc_record_bc_elim                     false
% 11.41/1.98  
% 11.41/1.98  ------ Preprocessing Options
% 11.41/1.98  
% 11.41/1.98  --preprocessing_flag                    true
% 11.41/1.98  --time_out_prep_mult                    0.1
% 11.41/1.98  --splitting_mode                        input
% 11.41/1.98  --splitting_grd                         true
% 11.41/1.98  --splitting_cvd                         false
% 11.41/1.98  --splitting_cvd_svl                     false
% 11.41/1.98  --splitting_nvd                         32
% 11.41/1.98  --sub_typing                            true
% 11.41/1.98  --prep_gs_sim                           true
% 11.41/1.98  --prep_unflatten                        true
% 11.41/1.98  --prep_res_sim                          true
% 11.41/1.98  --prep_upred                            true
% 11.41/1.98  --prep_sem_filter                       exhaustive
% 11.41/1.98  --prep_sem_filter_out                   false
% 11.41/1.98  --pred_elim                             true
% 11.41/1.98  --res_sim_input                         true
% 11.41/1.98  --eq_ax_congr_red                       true
% 11.41/1.98  --pure_diseq_elim                       true
% 11.41/1.98  --brand_transform                       false
% 11.41/1.98  --non_eq_to_eq                          false
% 11.41/1.98  --prep_def_merge                        true
% 11.41/1.98  --prep_def_merge_prop_impl              false
% 11.41/1.98  --prep_def_merge_mbd                    true
% 11.41/1.98  --prep_def_merge_tr_red                 false
% 11.41/1.98  --prep_def_merge_tr_cl                  false
% 11.41/1.98  --smt_preprocessing                     true
% 11.41/1.98  --smt_ac_axioms                         fast
% 11.41/1.98  --preprocessed_out                      false
% 11.41/1.98  --preprocessed_stats                    false
% 11.41/1.98  
% 11.41/1.98  ------ Abstraction refinement Options
% 11.41/1.98  
% 11.41/1.98  --abstr_ref                             []
% 11.41/1.98  --abstr_ref_prep                        false
% 11.41/1.98  --abstr_ref_until_sat                   false
% 11.41/1.98  --abstr_ref_sig_restrict                funpre
% 11.41/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.41/1.98  --abstr_ref_under                       []
% 11.41/1.98  
% 11.41/1.98  ------ SAT Options
% 11.41/1.98  
% 11.41/1.98  --sat_mode                              false
% 11.41/1.98  --sat_fm_restart_options                ""
% 11.41/1.98  --sat_gr_def                            false
% 11.41/1.98  --sat_epr_types                         true
% 11.41/1.98  --sat_non_cyclic_types                  false
% 11.41/1.98  --sat_finite_models                     false
% 11.41/1.98  --sat_fm_lemmas                         false
% 11.41/1.98  --sat_fm_prep                           false
% 11.41/1.98  --sat_fm_uc_incr                        true
% 11.41/1.98  --sat_out_model                         small
% 11.41/1.98  --sat_out_clauses                       false
% 11.41/1.98  
% 11.41/1.98  ------ QBF Options
% 11.41/1.98  
% 11.41/1.98  --qbf_mode                              false
% 11.41/1.98  --qbf_elim_univ                         false
% 11.41/1.98  --qbf_dom_inst                          none
% 11.41/1.98  --qbf_dom_pre_inst                      false
% 11.41/1.98  --qbf_sk_in                             false
% 11.41/1.98  --qbf_pred_elim                         true
% 11.41/1.98  --qbf_split                             512
% 11.41/1.98  
% 11.41/1.98  ------ BMC1 Options
% 11.41/1.98  
% 11.41/1.98  --bmc1_incremental                      false
% 11.41/1.98  --bmc1_axioms                           reachable_all
% 11.41/1.98  --bmc1_min_bound                        0
% 11.41/1.98  --bmc1_max_bound                        -1
% 11.41/1.98  --bmc1_max_bound_default                -1
% 11.41/1.98  --bmc1_symbol_reachability              true
% 11.41/1.98  --bmc1_property_lemmas                  false
% 11.41/1.98  --bmc1_k_induction                      false
% 11.41/1.98  --bmc1_non_equiv_states                 false
% 11.41/1.98  --bmc1_deadlock                         false
% 11.41/1.98  --bmc1_ucm                              false
% 11.41/1.98  --bmc1_add_unsat_core                   none
% 11.41/1.98  --bmc1_unsat_core_children              false
% 11.41/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.41/1.98  --bmc1_out_stat                         full
% 11.41/1.98  --bmc1_ground_init                      false
% 11.41/1.98  --bmc1_pre_inst_next_state              false
% 11.41/1.98  --bmc1_pre_inst_state                   false
% 11.41/1.98  --bmc1_pre_inst_reach_state             false
% 11.41/1.98  --bmc1_out_unsat_core                   false
% 11.41/1.98  --bmc1_aig_witness_out                  false
% 11.41/1.98  --bmc1_verbose                          false
% 11.41/1.98  --bmc1_dump_clauses_tptp                false
% 11.41/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.41/1.98  --bmc1_dump_file                        -
% 11.41/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.41/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.41/1.98  --bmc1_ucm_extend_mode                  1
% 11.41/1.98  --bmc1_ucm_init_mode                    2
% 11.41/1.98  --bmc1_ucm_cone_mode                    none
% 11.41/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.41/1.98  --bmc1_ucm_relax_model                  4
% 11.41/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.41/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.41/1.98  --bmc1_ucm_layered_model                none
% 11.41/1.98  --bmc1_ucm_max_lemma_size               10
% 11.41/1.98  
% 11.41/1.98  ------ AIG Options
% 11.41/1.98  
% 11.41/1.98  --aig_mode                              false
% 11.41/1.98  
% 11.41/1.98  ------ Instantiation Options
% 11.41/1.98  
% 11.41/1.98  --instantiation_flag                    true
% 11.41/1.98  --inst_sos_flag                         false
% 11.41/1.98  --inst_sos_phase                        true
% 11.41/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.41/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.41/1.98  --inst_lit_sel_side                     none
% 11.41/1.98  --inst_solver_per_active                1400
% 11.41/1.98  --inst_solver_calls_frac                1.
% 11.41/1.98  --inst_passive_queue_type               priority_queues
% 11.41/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.41/1.98  --inst_passive_queues_freq              [25;2]
% 11.41/1.98  --inst_dismatching                      true
% 11.41/1.98  --inst_eager_unprocessed_to_passive     true
% 11.41/1.98  --inst_prop_sim_given                   true
% 11.41/1.98  --inst_prop_sim_new                     false
% 11.41/1.98  --inst_subs_new                         false
% 11.41/1.98  --inst_eq_res_simp                      false
% 11.41/1.98  --inst_subs_given                       false
% 11.41/1.98  --inst_orphan_elimination               true
% 11.41/1.98  --inst_learning_loop_flag               true
% 11.41/1.98  --inst_learning_start                   3000
% 11.41/1.98  --inst_learning_factor                  2
% 11.41/1.98  --inst_start_prop_sim_after_learn       3
% 11.41/1.98  --inst_sel_renew                        solver
% 11.41/1.98  --inst_lit_activity_flag                true
% 11.41/1.98  --inst_restr_to_given                   false
% 11.41/1.98  --inst_activity_threshold               500
% 11.41/1.98  --inst_out_proof                        true
% 11.41/1.98  
% 11.41/1.98  ------ Resolution Options
% 11.41/1.98  
% 11.41/1.98  --resolution_flag                       false
% 11.41/1.98  --res_lit_sel                           adaptive
% 11.41/1.98  --res_lit_sel_side                      none
% 11.41/1.98  --res_ordering                          kbo
% 11.41/1.98  --res_to_prop_solver                    active
% 11.41/1.98  --res_prop_simpl_new                    false
% 11.41/1.98  --res_prop_simpl_given                  true
% 11.41/1.98  --res_passive_queue_type                priority_queues
% 11.41/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.41/1.98  --res_passive_queues_freq               [15;5]
% 11.41/1.98  --res_forward_subs                      full
% 11.41/1.98  --res_backward_subs                     full
% 11.41/1.98  --res_forward_subs_resolution           true
% 11.41/1.98  --res_backward_subs_resolution          true
% 11.41/1.98  --res_orphan_elimination                true
% 11.41/1.98  --res_time_limit                        2.
% 11.41/1.98  --res_out_proof                         true
% 11.41/1.98  
% 11.41/1.98  ------ Superposition Options
% 11.41/1.98  
% 11.41/1.98  --superposition_flag                    true
% 11.41/1.98  --sup_passive_queue_type                priority_queues
% 11.41/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.41/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.41/1.98  --demod_completeness_check              fast
% 11.41/1.98  --demod_use_ground                      true
% 11.41/1.98  --sup_to_prop_solver                    passive
% 11.41/1.98  --sup_prop_simpl_new                    true
% 11.41/1.98  --sup_prop_simpl_given                  true
% 11.41/1.98  --sup_fun_splitting                     false
% 11.41/1.98  --sup_smt_interval                      50000
% 11.41/1.98  
% 11.41/1.98  ------ Superposition Simplification Setup
% 11.41/1.98  
% 11.41/1.98  --sup_indices_passive                   []
% 11.41/1.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.41/1.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.41/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.41/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.41/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.41/1.98  --sup_full_bw                           [BwDemod]
% 11.41/1.98  --sup_immed_triv                        [TrivRules]
% 11.41/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.41/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.41/1.98  --sup_immed_bw_main                     []
% 11.41/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.41/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.41/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.41/1.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.41/1.98  
% 11.41/1.98  ------ Combination Options
% 11.41/1.98  
% 11.41/1.98  --comb_res_mult                         3
% 11.41/1.98  --comb_sup_mult                         2
% 11.41/1.98  --comb_inst_mult                        10
% 11.41/1.98  
% 11.41/1.98  ------ Debug Options
% 11.41/1.98  
% 11.41/1.98  --dbg_backtrace                         false
% 11.41/1.98  --dbg_dump_prop_clauses                 false
% 11.41/1.98  --dbg_dump_prop_clauses_file            -
% 11.41/1.98  --dbg_out_stat                          false
% 11.41/1.98  
% 11.41/1.98  
% 11.41/1.98  
% 11.41/1.98  
% 11.41/1.98  ------ Proving...
% 11.41/1.98  
% 11.41/1.98  
% 11.41/1.98  % SZS status Theorem for theBenchmark.p
% 11.41/1.98  
% 11.41/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.41/1.98  
% 11.41/1.98  fof(f17,conjecture,(
% 11.41/1.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) => k1_tops_1(X0,k2_tops_1(X0,X1)) = k1_xboole_0)))),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f18,negated_conjecture,(
% 11.41/1.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) => k1_tops_1(X0,k2_tops_1(X0,X1)) = k1_xboole_0)))),
% 11.41/1.98    inference(negated_conjecture,[],[f17])).
% 11.41/1.98  
% 11.41/1.98  fof(f46,plain,(
% 11.41/1.98    ? [X0] : (? [X1] : ((k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0 & v4_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 11.41/1.98    inference(ennf_transformation,[],[f18])).
% 11.41/1.98  
% 11.41/1.98  fof(f47,plain,(
% 11.41/1.98    ? [X0] : (? [X1] : (k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0 & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.41/1.98    inference(flattening,[],[f46])).
% 11.41/1.98  
% 11.41/1.98  fof(f54,plain,(
% 11.41/1.98    ( ! [X0] : (? [X1] : (k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0 & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (k1_tops_1(X0,k2_tops_1(X0,sK1)) != k1_xboole_0 & v4_tops_1(sK1,X0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.41/1.98    introduced(choice_axiom,[])).
% 11.41/1.98  
% 11.41/1.98  fof(f53,plain,(
% 11.41/1.98    ? [X0] : (? [X1] : (k1_tops_1(X0,k2_tops_1(X0,X1)) != k1_xboole_0 & v4_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (k1_tops_1(sK0,k2_tops_1(sK0,X1)) != k1_xboole_0 & v4_tops_1(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 11.41/1.98    introduced(choice_axiom,[])).
% 11.41/1.98  
% 11.41/1.98  fof(f55,plain,(
% 11.41/1.98    (k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0 & v4_tops_1(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 11.41/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f47,f54,f53])).
% 11.41/1.98  
% 11.41/1.98  fof(f79,plain,(
% 11.41/1.98    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.41/1.98    inference(cnf_transformation,[],[f55])).
% 11.41/1.98  
% 11.41/1.98  fof(f5,axiom,(
% 11.41/1.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f24,plain,(
% 11.41/1.98    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.41/1.98    inference(ennf_transformation,[],[f5])).
% 11.41/1.98  
% 11.41/1.98  fof(f25,plain,(
% 11.41/1.98    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.41/1.98    inference(flattening,[],[f24])).
% 11.41/1.98  
% 11.41/1.98  fof(f64,plain,(
% 11.41/1.98    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.41/1.98    inference(cnf_transformation,[],[f25])).
% 11.41/1.98  
% 11.41/1.98  fof(f78,plain,(
% 11.41/1.98    l1_pre_topc(sK0)),
% 11.41/1.98    inference(cnf_transformation,[],[f55])).
% 11.41/1.98  
% 11.41/1.98  fof(f3,axiom,(
% 11.41/1.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f21,plain,(
% 11.41/1.98    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.41/1.98    inference(ennf_transformation,[],[f3])).
% 11.41/1.98  
% 11.41/1.98  fof(f22,plain,(
% 11.41/1.98    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.41/1.98    inference(flattening,[],[f21])).
% 11.41/1.98  
% 11.41/1.98  fof(f60,plain,(
% 11.41/1.98    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.41/1.98    inference(cnf_transformation,[],[f22])).
% 11.41/1.98  
% 11.41/1.98  fof(f1,axiom,(
% 11.41/1.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f48,plain,(
% 11.41/1.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.41/1.98    inference(nnf_transformation,[],[f1])).
% 11.41/1.98  
% 11.41/1.98  fof(f49,plain,(
% 11.41/1.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.41/1.98    inference(flattening,[],[f48])).
% 11.41/1.98  
% 11.41/1.98  fof(f58,plain,(
% 11.41/1.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.41/1.98    inference(cnf_transformation,[],[f49])).
% 11.41/1.98  
% 11.41/1.98  fof(f4,axiom,(
% 11.41/1.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)))))),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f23,plain,(
% 11.41/1.98    ! [X0] : (! [X1] : ((v4_tops_1(X1,X0) <=> (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.41/1.98    inference(ennf_transformation,[],[f4])).
% 11.41/1.98  
% 11.41/1.98  fof(f50,plain,(
% 11.41/1.98    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | (~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1))) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.41/1.98    inference(nnf_transformation,[],[f23])).
% 11.41/1.98  
% 11.41/1.98  fof(f51,plain,(
% 11.41/1.98    ! [X0] : (! [X1] : (((v4_tops_1(X1,X0) | ~r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) & ((r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) & r1_tarski(k1_tops_1(X0,k2_pre_topc(X0,X1)),X1)) | ~v4_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.41/1.98    inference(flattening,[],[f50])).
% 11.41/1.98  
% 11.41/1.98  fof(f62,plain,(
% 11.41/1.98    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,k1_tops_1(X0,X1))) | ~v4_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.41/1.98    inference(cnf_transformation,[],[f51])).
% 11.41/1.98  
% 11.41/1.98  fof(f80,plain,(
% 11.41/1.98    v4_tops_1(sK1,sK0)),
% 11.41/1.98    inference(cnf_transformation,[],[f55])).
% 11.41/1.98  
% 11.41/1.98  fof(f14,axiom,(
% 11.41/1.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f41,plain,(
% 11.41/1.98    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.41/1.98    inference(ennf_transformation,[],[f14])).
% 11.41/1.98  
% 11.41/1.98  fof(f73,plain,(
% 11.41/1.98    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.41/1.98    inference(cnf_transformation,[],[f41])).
% 11.41/1.98  
% 11.41/1.98  fof(f8,axiom,(
% 11.41/1.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f30,plain,(
% 11.41/1.98    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.41/1.98    inference(ennf_transformation,[],[f8])).
% 11.41/1.98  
% 11.41/1.98  fof(f31,plain,(
% 11.41/1.98    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.41/1.98    inference(flattening,[],[f30])).
% 11.41/1.98  
% 11.41/1.98  fof(f67,plain,(
% 11.41/1.98    ( ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.41/1.98    inference(cnf_transformation,[],[f31])).
% 11.41/1.98  
% 11.41/1.98  fof(f77,plain,(
% 11.41/1.98    v2_pre_topc(sK0)),
% 11.41/1.98    inference(cnf_transformation,[],[f55])).
% 11.41/1.98  
% 11.41/1.98  fof(f2,axiom,(
% 11.41/1.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f19,plain,(
% 11.41/1.98    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.41/1.98    inference(ennf_transformation,[],[f2])).
% 11.41/1.98  
% 11.41/1.98  fof(f20,plain,(
% 11.41/1.98    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.41/1.98    inference(flattening,[],[f19])).
% 11.41/1.98  
% 11.41/1.98  fof(f59,plain,(
% 11.41/1.98    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.41/1.98    inference(cnf_transformation,[],[f20])).
% 11.41/1.98  
% 11.41/1.98  fof(f13,axiom,(
% 11.41/1.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X2,X1) & v4_pre_topc(X1,X0)) => r1_tarski(k2_pre_topc(X0,X2),X1)))))),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f39,plain,(
% 11.41/1.98    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X2),X1) | (~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.41/1.98    inference(ennf_transformation,[],[f13])).
% 11.41/1.98  
% 11.41/1.98  fof(f40,plain,(
% 11.41/1.98    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X2),X1) | ~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.41/1.98    inference(flattening,[],[f39])).
% 11.41/1.98  
% 11.41/1.98  fof(f72,plain,(
% 11.41/1.98    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X2),X1) | ~r1_tarski(X2,X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.41/1.98    inference(cnf_transformation,[],[f40])).
% 11.41/1.98  
% 11.41/1.98  fof(f10,axiom,(
% 11.41/1.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f34,plain,(
% 11.41/1.98    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.41/1.98    inference(ennf_transformation,[],[f10])).
% 11.41/1.98  
% 11.41/1.98  fof(f69,plain,(
% 11.41/1.98    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.41/1.98    inference(cnf_transformation,[],[f34])).
% 11.41/1.98  
% 11.41/1.98  fof(f12,axiom,(
% 11.41/1.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f37,plain,(
% 11.41/1.98    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.41/1.98    inference(ennf_transformation,[],[f12])).
% 11.41/1.98  
% 11.41/1.98  fof(f38,plain,(
% 11.41/1.98    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.41/1.98    inference(flattening,[],[f37])).
% 11.41/1.98  
% 11.41/1.98  fof(f71,plain,(
% 11.41/1.98    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.41/1.98    inference(cnf_transformation,[],[f38])).
% 11.41/1.98  
% 11.41/1.98  fof(f6,axiom,(
% 11.41/1.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f26,plain,(
% 11.41/1.98    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.41/1.98    inference(ennf_transformation,[],[f6])).
% 11.41/1.98  
% 11.41/1.98  fof(f27,plain,(
% 11.41/1.98    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.41/1.98    inference(flattening,[],[f26])).
% 11.41/1.98  
% 11.41/1.98  fof(f65,plain,(
% 11.41/1.98    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.41/1.98    inference(cnf_transformation,[],[f27])).
% 11.41/1.98  
% 11.41/1.98  fof(f15,axiom,(
% 11.41/1.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f42,plain,(
% 11.41/1.98    ! [X0] : (! [X1] : (((v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.41/1.98    inference(ennf_transformation,[],[f15])).
% 11.41/1.98  
% 11.41/1.98  fof(f43,plain,(
% 11.41/1.98    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.41/1.98    inference(flattening,[],[f42])).
% 11.41/1.98  
% 11.41/1.98  fof(f52,plain,(
% 11.41/1.98    ! [X0] : (! [X1] : (((v3_tops_1(X1,X0) | k2_tops_1(X0,X1) != X1) & (k2_tops_1(X0,X1) = X1 | ~v3_tops_1(X1,X0))) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.41/1.98    inference(nnf_transformation,[],[f43])).
% 11.41/1.98  
% 11.41/1.98  fof(f74,plain,(
% 11.41/1.98    ( ! [X0,X1] : (k2_tops_1(X0,X1) = X1 | ~v3_tops_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.41/1.98    inference(cnf_transformation,[],[f52])).
% 11.41/1.98  
% 11.41/1.98  fof(f9,axiom,(
% 11.41/1.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f32,plain,(
% 11.41/1.98    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.41/1.98    inference(ennf_transformation,[],[f9])).
% 11.41/1.98  
% 11.41/1.98  fof(f33,plain,(
% 11.41/1.98    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.41/1.98    inference(flattening,[],[f32])).
% 11.41/1.98  
% 11.41/1.98  fof(f68,plain,(
% 11.41/1.98    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.41/1.98    inference(cnf_transformation,[],[f33])).
% 11.41/1.98  
% 11.41/1.98  fof(f16,axiom,(
% 11.41/1.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => v3_tops_1(k2_tops_1(X0,X1),X0))))),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f44,plain,(
% 11.41/1.98    ! [X0] : (! [X1] : ((v3_tops_1(k2_tops_1(X0,X1),X0) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.41/1.98    inference(ennf_transformation,[],[f16])).
% 11.41/1.98  
% 11.41/1.98  fof(f45,plain,(
% 11.41/1.98    ! [X0] : (! [X1] : (v3_tops_1(k2_tops_1(X0,X1),X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.41/1.98    inference(flattening,[],[f44])).
% 11.41/1.98  
% 11.41/1.98  fof(f76,plain,(
% 11.41/1.98    ( ! [X0,X1] : (v3_tops_1(k2_tops_1(X0,X1),X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.41/1.98    inference(cnf_transformation,[],[f45])).
% 11.41/1.98  
% 11.41/1.98  fof(f7,axiom,(
% 11.41/1.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_tops_1(X0,X1),X0))),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f28,plain,(
% 11.41/1.98    ! [X0,X1] : (v4_pre_topc(k2_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.41/1.98    inference(ennf_transformation,[],[f7])).
% 11.41/1.98  
% 11.41/1.98  fof(f29,plain,(
% 11.41/1.98    ! [X0,X1] : (v4_pre_topc(k2_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.41/1.98    inference(flattening,[],[f28])).
% 11.41/1.98  
% 11.41/1.98  fof(f66,plain,(
% 11.41/1.98    ( ! [X0,X1] : (v4_pre_topc(k2_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.41/1.98    inference(cnf_transformation,[],[f29])).
% 11.41/1.98  
% 11.41/1.98  fof(f11,axiom,(
% 11.41/1.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0))),
% 11.41/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.41/1.98  
% 11.41/1.98  fof(f35,plain,(
% 11.41/1.98    ! [X0] : (! [X1] : (k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.41/1.98    inference(ennf_transformation,[],[f11])).
% 11.41/1.98  
% 11.41/1.98  fof(f36,plain,(
% 11.41/1.98    ! [X0] : (! [X1] : (k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.41/1.98    inference(flattening,[],[f35])).
% 11.41/1.98  
% 11.41/1.98  fof(f70,plain,(
% 11.41/1.98    ( ! [X0,X1] : (k1_tops_1(X0,k2_tops_1(X0,k2_tops_1(X0,X1))) = k1_xboole_0 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.41/1.98    inference(cnf_transformation,[],[f36])).
% 11.41/1.98  
% 11.41/1.98  fof(f81,plain,(
% 11.41/1.98    k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0),
% 11.41/1.98    inference(cnf_transformation,[],[f55])).
% 11.41/1.98  
% 11.41/1.98  cnf(c_23,negated_conjecture,
% 11.41/1.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.41/1.98      inference(cnf_transformation,[],[f79]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_1378,plain,
% 11.41/1.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.41/1.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_8,plain,
% 11.41/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.41/1.98      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.41/1.98      | ~ l1_pre_topc(X1) ),
% 11.41/1.98      inference(cnf_transformation,[],[f64]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_24,negated_conjecture,
% 11.41/1.98      ( l1_pre_topc(sK0) ),
% 11.41/1.98      inference(cnf_transformation,[],[f78]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_644,plain,
% 11.41/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.41/1.98      | m1_subset_1(k1_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.41/1.98      | sK0 != X1 ),
% 11.41/1.98      inference(resolution_lifted,[status(thm)],[c_8,c_24]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_645,plain,
% 11.41/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.98      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.41/1.98      inference(unflattening,[status(thm)],[c_644]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_1366,plain,
% 11.41/1.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.41/1.98      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.41/1.98      inference(predicate_to_equality,[status(thm)],[c_645]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_4,plain,
% 11.41/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.41/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.41/1.98      | ~ r1_tarski(X0,X2)
% 11.41/1.98      | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
% 11.41/1.98      | ~ l1_pre_topc(X1) ),
% 11.41/1.98      inference(cnf_transformation,[],[f60]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_656,plain,
% 11.41/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.41/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.41/1.98      | ~ r1_tarski(X0,X2)
% 11.41/1.98      | r1_tarski(k2_pre_topc(X1,X0),k2_pre_topc(X1,X2))
% 11.41/1.98      | sK0 != X1 ),
% 11.41/1.98      inference(resolution_lifted,[status(thm)],[c_4,c_24]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_657,plain,
% 11.41/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.98      | ~ r1_tarski(X0,X1)
% 11.41/1.98      | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1)) ),
% 11.41/1.98      inference(unflattening,[status(thm)],[c_656]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_1365,plain,
% 11.41/1.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.41/1.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.41/1.98      | r1_tarski(X0,X1) != iProver_top
% 11.41/1.98      | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1)) = iProver_top ),
% 11.41/1.98      inference(predicate_to_equality,[status(thm)],[c_657]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_0,plain,
% 11.41/1.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.41/1.98      inference(cnf_transformation,[],[f58]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_1380,plain,
% 11.41/1.98      ( X0 = X1
% 11.41/1.98      | r1_tarski(X0,X1) != iProver_top
% 11.41/1.98      | r1_tarski(X1,X0) != iProver_top ),
% 11.41/1.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_3062,plain,
% 11.41/1.98      ( k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,X1)
% 11.41/1.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.41/1.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.41/1.98      | r1_tarski(X0,X1) != iProver_top
% 11.41/1.98      | r1_tarski(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X0)) != iProver_top ),
% 11.41/1.98      inference(superposition,[status(thm)],[c_1365,c_1380]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_3216,plain,
% 11.41/1.98      ( k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,X1)
% 11.41/1.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.41/1.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.41/1.98      | r1_tarski(X0,X1) != iProver_top
% 11.41/1.98      | r1_tarski(X1,X0) != iProver_top ),
% 11.41/1.98      inference(superposition,[status(thm)],[c_1365,c_3062]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_5767,plain,
% 11.41/1.98      ( k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,sK1)
% 11.41/1.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.41/1.98      | r1_tarski(X0,sK1) != iProver_top
% 11.41/1.98      | r1_tarski(sK1,X0) != iProver_top ),
% 11.41/1.98      inference(superposition,[status(thm)],[c_1378,c_3216]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_5891,plain,
% 11.41/1.98      ( k2_pre_topc(sK0,k1_tops_1(sK0,X0)) = k2_pre_topc(sK0,sK1)
% 11.41/1.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.41/1.98      | r1_tarski(k1_tops_1(sK0,X0),sK1) != iProver_top
% 11.41/1.98      | r1_tarski(sK1,k1_tops_1(sK0,X0)) != iProver_top ),
% 11.41/1.98      inference(superposition,[status(thm)],[c_1366,c_5767]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_44686,plain,
% 11.41/1.98      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 11.41/1.98      | r1_tarski(k1_tops_1(sK0,sK1),sK1) != iProver_top
% 11.41/1.98      | r1_tarski(sK1,k1_tops_1(sK0,sK1)) != iProver_top ),
% 11.41/1.98      inference(superposition,[status(thm)],[c_1378,c_5891]) ).
% 11.41/1.98  
% 11.41/1.98  cnf(c_6,plain,
% 11.41/1.98      ( ~ v4_tops_1(X0,X1)
% 11.41/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.41/1.98      | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 11.41/1.98      | ~ l1_pre_topc(X1) ),
% 11.41/1.98      inference(cnf_transformation,[],[f62]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_22,negated_conjecture,
% 11.41/1.99      ( v4_tops_1(sK1,sK0) ),
% 11.41/1.99      inference(cnf_transformation,[],[f80]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_434,plain,
% 11.41/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.41/1.99      | r1_tarski(X0,k2_pre_topc(X1,k1_tops_1(X1,X0)))
% 11.41/1.99      | ~ l1_pre_topc(X1)
% 11.41/1.99      | sK1 != X0
% 11.41/1.99      | sK0 != X1 ),
% 11.41/1.99      inference(resolution_lifted,[status(thm)],[c_6,c_22]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_435,plain,
% 11.41/1.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.99      | r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
% 11.41/1.99      | ~ l1_pre_topc(sK0) ),
% 11.41/1.99      inference(unflattening,[status(thm)],[c_434]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1508,plain,
% 11.41/1.99      ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_645]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_17,plain,
% 11.41/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.41/1.99      | r1_tarski(k1_tops_1(X1,X0),X0)
% 11.41/1.99      | ~ l1_pre_topc(X1) ),
% 11.41/1.99      inference(cnf_transformation,[],[f73]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_575,plain,
% 11.41/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.41/1.99      | r1_tarski(k1_tops_1(X1,X0),X0)
% 11.41/1.99      | sK0 != X1 ),
% 11.41/1.99      inference(resolution_lifted,[status(thm)],[c_17,c_24]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_576,plain,
% 11.41/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.99      | r1_tarski(k1_tops_1(sK0,X0),X0) ),
% 11.41/1.99      inference(unflattening,[status(thm)],[c_575]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1517,plain,
% 11.41/1.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.99      | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_576]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_11,plain,
% 11.41/1.99      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 11.41/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.41/1.99      | ~ v2_pre_topc(X0)
% 11.41/1.99      | ~ l1_pre_topc(X0) ),
% 11.41/1.99      inference(cnf_transformation,[],[f67]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_25,negated_conjecture,
% 11.41/1.99      ( v2_pre_topc(sK0) ),
% 11.41/1.99      inference(cnf_transformation,[],[f77]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_325,plain,
% 11.41/1.99      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
% 11.41/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.41/1.99      | ~ l1_pre_topc(X0)
% 11.41/1.99      | sK0 != X0 ),
% 11.41/1.99      inference(resolution_lifted,[status(thm)],[c_11,c_25]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_326,plain,
% 11.41/1.99      ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
% 11.41/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.99      | ~ l1_pre_topc(sK0) ),
% 11.41/1.99      inference(unflattening,[status(thm)],[c_325]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_330,plain,
% 11.41/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.99      | v4_pre_topc(k2_pre_topc(sK0,X0),sK0) ),
% 11.41/1.99      inference(global_propositional_subsumption,
% 11.41/1.99                [status(thm)],
% 11.41/1.99                [c_326,c_24]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_331,plain,
% 11.41/1.99      ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
% 11.41/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.41/1.99      inference(renaming,[status(thm)],[c_330]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1630,plain,
% 11.41/1.99      ( v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),sK0)
% 11.41/1.99      | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_331]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_3,plain,
% 11.41/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.41/1.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.41/1.99      | ~ l1_pre_topc(X1) ),
% 11.41/1.99      inference(cnf_transformation,[],[f59]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_674,plain,
% 11.41/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.41/1.99      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.41/1.99      | sK0 != X1 ),
% 11.41/1.99      inference(resolution_lifted,[status(thm)],[c_3,c_24]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_675,plain,
% 11.41/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.99      | m1_subset_1(k2_pre_topc(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.41/1.99      inference(unflattening,[status(thm)],[c_674]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1625,plain,
% 11.41/1.99      ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.99      | m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_675]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1621,plain,
% 11.41/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.99      | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.99      | ~ r1_tarski(k1_tops_1(sK0,sK1),X0)
% 11.41/1.99      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,X0)) ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_657]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_6072,plain,
% 11.41/1.99      ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.99      | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
% 11.41/1.99      | r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1)) ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_1621]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_16,plain,
% 11.41/1.99      ( ~ v4_pre_topc(X0,X1)
% 11.41/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.41/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.41/1.99      | ~ r1_tarski(X2,X0)
% 11.41/1.99      | r1_tarski(k2_pre_topc(X1,X2),X0)
% 11.41/1.99      | ~ l1_pre_topc(X1) ),
% 11.41/1.99      inference(cnf_transformation,[],[f72]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_587,plain,
% 11.41/1.99      ( ~ v4_pre_topc(X0,X1)
% 11.41/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.41/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 11.41/1.99      | ~ r1_tarski(X2,X0)
% 11.41/1.99      | r1_tarski(k2_pre_topc(X1,X2),X0)
% 11.41/1.99      | sK0 != X1 ),
% 11.41/1.99      inference(resolution_lifted,[status(thm)],[c_16,c_24]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_588,plain,
% 11.41/1.99      ( ~ v4_pre_topc(X0,sK0)
% 11.41/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.99      | ~ r1_tarski(X1,X0)
% 11.41/1.99      | r1_tarski(k2_pre_topc(sK0,X1),X0) ),
% 11.41/1.99      inference(unflattening,[status(thm)],[c_587]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_2161,plain,
% 11.41/1.99      ( ~ v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),sK0)
% 11.41/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.99      | ~ m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.99      | ~ r1_tarski(X0,k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
% 11.41/1.99      | r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_588]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_6575,plain,
% 11.41/1.99      ( ~ v4_pre_topc(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),sK0)
% 11.41/1.99      | ~ m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.99      | r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
% 11.41/1.99      | ~ r1_tarski(sK1,k2_pre_topc(sK0,k1_tops_1(sK0,sK1))) ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_2161]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_5666,plain,
% 11.41/1.99      ( ~ r1_tarski(X0,k2_pre_topc(sK0,sK1))
% 11.41/1.99      | ~ r1_tarski(k2_pre_topc(sK0,sK1),X0)
% 11.41/1.99      | X0 = k2_pre_topc(sK0,sK1) ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_0]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_19205,plain,
% 11.41/1.99      ( ~ r1_tarski(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k2_pre_topc(sK0,sK1))
% 11.41/1.99      | ~ r1_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)))
% 11.41/1.99      | k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 11.41/1.99      inference(instantiation,[status(thm)],[c_5666]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_44736,plain,
% 11.41/1.99      ( k2_pre_topc(sK0,k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 11.41/1.99      inference(global_propositional_subsumption,
% 11.41/1.99                [status(thm)],
% 11.41/1.99                [c_44686,c_24,c_23,c_435,c_1508,c_1517,c_1630,c_1625,
% 11.41/1.99                 c_6072,c_6575,c_19205]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_13,plain,
% 11.41/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.41/1.99      | ~ l1_pre_topc(X1)
% 11.41/1.99      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 11.41/1.99      inference(cnf_transformation,[],[f69]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_620,plain,
% 11.41/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.41/1.99      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 11.41/1.99      | sK0 != X1 ),
% 11.41/1.99      inference(resolution_lifted,[status(thm)],[c_13,c_24]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_621,plain,
% 11.41/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.99      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 11.41/1.99      inference(unflattening,[status(thm)],[c_620]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1368,plain,
% 11.41/1.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 11.41/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_621]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_3400,plain,
% 11.41/1.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,X0)),k1_tops_1(sK0,k1_tops_1(sK0,X0))) = k2_tops_1(sK0,k1_tops_1(sK0,X0))
% 11.41/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_1366,c_1368]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_7918,plain,
% 11.41/1.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_1378,c_3400]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_15,plain,
% 11.41/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.41/1.99      | ~ l1_pre_topc(X1)
% 11.41/1.99      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 11.41/1.99      inference(cnf_transformation,[],[f71]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_608,plain,
% 11.41/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.41/1.99      | k1_tops_1(X1,k1_tops_1(X1,X0)) = k1_tops_1(X1,X0)
% 11.41/1.99      | sK0 != X1 ),
% 11.41/1.99      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_609,plain,
% 11.41/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.99      | k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0) ),
% 11.41/1.99      inference(unflattening,[status(thm)],[c_608]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1369,plain,
% 11.41/1.99      ( k1_tops_1(sK0,k1_tops_1(sK0,X0)) = k1_tops_1(sK0,X0)
% 11.41/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_609]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_2549,plain,
% 11.41/1.99      ( k1_tops_1(sK0,k1_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_1378,c_1369]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_7939,plain,
% 11.41/1.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
% 11.41/1.99      inference(light_normalisation,[status(thm)],[c_7918,c_2549]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_44759,plain,
% 11.41/1.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
% 11.41/1.99      inference(demodulation,[status(thm)],[c_44736,c_7939]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_3397,plain,
% 11.41/1.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_1378,c_1368]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_44771,plain,
% 11.41/1.99      ( k2_tops_1(sK0,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.41/1.99      inference(light_normalisation,[status(thm)],[c_44759,c_3397]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_9,plain,
% 11.41/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.41/1.99      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.41/1.99      | ~ l1_pre_topc(X1) ),
% 11.41/1.99      inference(cnf_transformation,[],[f65]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_632,plain,
% 11.41/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.41/1.99      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.41/1.99      | sK0 != X1 ),
% 11.41/1.99      inference(resolution_lifted,[status(thm)],[c_9,c_24]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_633,plain,
% 11.41/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.99      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.41/1.99      inference(unflattening,[status(thm)],[c_632]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1367,plain,
% 11.41/1.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.41/1.99      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_633]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_19,plain,
% 11.41/1.99      ( ~ v3_tops_1(X0,X1)
% 11.41/1.99      | ~ v4_pre_topc(X0,X1)
% 11.41/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.41/1.99      | ~ l1_pre_topc(X1)
% 11.41/1.99      | k2_tops_1(X1,X0) = X0 ),
% 11.41/1.99      inference(cnf_transformation,[],[f74]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_12,plain,
% 11.41/1.99      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
% 11.41/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.41/1.99      | ~ v2_pre_topc(X0)
% 11.41/1.99      | ~ l1_pre_topc(X0) ),
% 11.41/1.99      inference(cnf_transformation,[],[f68]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_20,plain,
% 11.41/1.99      ( v3_tops_1(k2_tops_1(X0,X1),X0)
% 11.41/1.99      | ~ v3_pre_topc(X1,X0)
% 11.41/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.41/1.99      | ~ v2_pre_topc(X0)
% 11.41/1.99      | ~ l1_pre_topc(X0) ),
% 11.41/1.99      inference(cnf_transformation,[],[f76]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_279,plain,
% 11.41/1.99      ( v3_tops_1(k2_tops_1(X0,X1),X0)
% 11.41/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 11.41/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.41/1.99      | ~ v2_pre_topc(X3)
% 11.41/1.99      | ~ v2_pre_topc(X0)
% 11.41/1.99      | ~ l1_pre_topc(X3)
% 11.41/1.99      | ~ l1_pre_topc(X0)
% 11.41/1.99      | X0 != X3
% 11.41/1.99      | k1_tops_1(X3,X2) != X1 ),
% 11.41/1.99      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_280,plain,
% 11.41/1.99      ( v3_tops_1(k2_tops_1(X0,k1_tops_1(X0,X1)),X0)
% 11.41/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.41/1.99      | ~ m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 11.41/1.99      | ~ v2_pre_topc(X0)
% 11.41/1.99      | ~ l1_pre_topc(X0) ),
% 11.41/1.99      inference(unflattening,[status(thm)],[c_279]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_294,plain,
% 11.41/1.99      ( v3_tops_1(k2_tops_1(X0,k1_tops_1(X0,X1)),X0)
% 11.41/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.41/1.99      | ~ v2_pre_topc(X0)
% 11.41/1.99      | ~ l1_pre_topc(X0) ),
% 11.41/1.99      inference(forward_subsumption_resolution,[status(thm)],[c_280,c_8]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_307,plain,
% 11.41/1.99      ( v3_tops_1(k2_tops_1(X0,k1_tops_1(X0,X1)),X0)
% 11.41/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.41/1.99      | ~ l1_pre_topc(X0)
% 11.41/1.99      | sK0 != X0 ),
% 11.41/1.99      inference(resolution_lifted,[status(thm)],[c_294,c_25]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_308,plain,
% 11.41/1.99      ( v3_tops_1(k2_tops_1(sK0,k1_tops_1(sK0,X0)),sK0)
% 11.41/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.99      | ~ l1_pre_topc(sK0) ),
% 11.41/1.99      inference(unflattening,[status(thm)],[c_307]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_312,plain,
% 11.41/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.99      | v3_tops_1(k2_tops_1(sK0,k1_tops_1(sK0,X0)),sK0) ),
% 11.41/1.99      inference(global_propositional_subsumption,
% 11.41/1.99                [status(thm)],
% 11.41/1.99                [c_308,c_24]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_313,plain,
% 11.41/1.99      ( v3_tops_1(k2_tops_1(sK0,k1_tops_1(sK0,X0)),sK0)
% 11.41/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.41/1.99      inference(renaming,[status(thm)],[c_312]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_392,plain,
% 11.41/1.99      ( ~ v4_pre_topc(X0,X1)
% 11.41/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.41/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.99      | ~ l1_pre_topc(X1)
% 11.41/1.99      | k2_tops_1(X1,X0) = X0
% 11.41/1.99      | k2_tops_1(sK0,k1_tops_1(sK0,X2)) != X0
% 11.41/1.99      | sK0 != X1 ),
% 11.41/1.99      inference(resolution_lifted,[status(thm)],[c_19,c_313]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_393,plain,
% 11.41/1.99      ( ~ v4_pre_topc(k2_tops_1(sK0,k1_tops_1(sK0,X0)),sK0)
% 11.41/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.99      | ~ m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.99      | ~ l1_pre_topc(sK0)
% 11.41/1.99      | k2_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,X0))) = k2_tops_1(sK0,k1_tops_1(sK0,X0)) ),
% 11.41/1.99      inference(unflattening,[status(thm)],[c_392]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_397,plain,
% 11.41/1.99      ( ~ m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.99      | ~ v4_pre_topc(k2_tops_1(sK0,k1_tops_1(sK0,X0)),sK0)
% 11.41/1.99      | k2_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,X0))) = k2_tops_1(sK0,k1_tops_1(sK0,X0)) ),
% 11.41/1.99      inference(global_propositional_subsumption,
% 11.41/1.99                [status(thm)],
% 11.41/1.99                [c_393,c_24]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_398,plain,
% 11.41/1.99      ( ~ v4_pre_topc(k2_tops_1(sK0,k1_tops_1(sK0,X0)),sK0)
% 11.41/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.99      | ~ m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.99      | k2_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,X0))) = k2_tops_1(sK0,k1_tops_1(sK0,X0)) ),
% 11.41/1.99      inference(renaming,[status(thm)],[c_397]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1374,plain,
% 11.41/1.99      ( k2_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,X0))) = k2_tops_1(sK0,k1_tops_1(sK0,X0))
% 11.41/1.99      | v4_pre_topc(k2_tops_1(sK0,k1_tops_1(sK0,X0)),sK0) != iProver_top
% 11.41/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.41/1.99      | m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_398]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_27,plain,
% 11.41/1.99      ( l1_pre_topc(sK0) = iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_394,plain,
% 11.41/1.99      ( k2_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,X0))) = k2_tops_1(sK0,k1_tops_1(sK0,X0))
% 11.41/1.99      | v4_pre_topc(k2_tops_1(sK0,k1_tops_1(sK0,X0)),sK0) != iProver_top
% 11.41/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.41/1.99      | m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.41/1.99      | l1_pre_topc(sK0) != iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_393]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_10,plain,
% 11.41/1.99      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
% 11.41/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.41/1.99      | ~ v2_pre_topc(X0)
% 11.41/1.99      | ~ l1_pre_topc(X0) ),
% 11.41/1.99      inference(cnf_transformation,[],[f66]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_343,plain,
% 11.41/1.99      ( v4_pre_topc(k2_tops_1(X0,X1),X0)
% 11.41/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 11.41/1.99      | ~ l1_pre_topc(X0)
% 11.41/1.99      | sK0 != X0 ),
% 11.41/1.99      inference(resolution_lifted,[status(thm)],[c_10,c_25]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_344,plain,
% 11.41/1.99      ( v4_pre_topc(k2_tops_1(sK0,X0),sK0)
% 11.41/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.99      | ~ l1_pre_topc(sK0) ),
% 11.41/1.99      inference(unflattening,[status(thm)],[c_343]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_348,plain,
% 11.41/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.99      | v4_pre_topc(k2_tops_1(sK0,X0),sK0) ),
% 11.41/1.99      inference(global_propositional_subsumption,
% 11.41/1.99                [status(thm)],
% 11.41/1.99                [c_344,c_24]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_349,plain,
% 11.41/1.99      ( v4_pre_topc(k2_tops_1(sK0,X0),sK0)
% 11.41/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.41/1.99      inference(renaming,[status(thm)],[c_348]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1376,plain,
% 11.41/1.99      ( v4_pre_topc(k2_tops_1(sK0,X0),sK0) = iProver_top
% 11.41/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_349]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_2332,plain,
% 11.41/1.99      ( v4_pre_topc(k2_tops_1(sK0,k1_tops_1(sK0,X0)),sK0) = iProver_top
% 11.41/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_1366,c_1376]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_4162,plain,
% 11.41/1.99      ( k2_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,X0))) = k2_tops_1(sK0,k1_tops_1(sK0,X0))
% 11.41/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.41/1.99      | m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,X0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.41/1.99      inference(global_propositional_subsumption,
% 11.41/1.99                [status(thm)],
% 11.41/1.99                [c_1374,c_27,c_394,c_2332]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_4171,plain,
% 11.41/1.99      ( k2_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,X0))) = k2_tops_1(sK0,k1_tops_1(sK0,X0))
% 11.41/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.41/1.99      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_1367,c_4162]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_646,plain,
% 11.41/1.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.41/1.99      | m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_645]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_18944,plain,
% 11.41/1.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.41/1.99      | k2_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,X0))) = k2_tops_1(sK0,k1_tops_1(sK0,X0)) ),
% 11.41/1.99      inference(global_propositional_subsumption,
% 11.41/1.99                [status(thm)],
% 11.41/1.99                [c_4171,c_646]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_18945,plain,
% 11.41/1.99      ( k2_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,X0))) = k2_tops_1(sK0,k1_tops_1(sK0,X0))
% 11.41/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.41/1.99      inference(renaming,[status(thm)],[c_18944]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_18952,plain,
% 11.41/1.99      ( k2_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_1378,c_18945]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_14,plain,
% 11.41/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.41/1.99      | ~ v2_pre_topc(X1)
% 11.41/1.99      | ~ l1_pre_topc(X1)
% 11.41/1.99      | k1_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X0))) = k1_xboole_0 ),
% 11.41/1.99      inference(cnf_transformation,[],[f70]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_361,plain,
% 11.41/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.41/1.99      | ~ l1_pre_topc(X1)
% 11.41/1.99      | k1_tops_1(X1,k2_tops_1(X1,k2_tops_1(X1,X0))) = k1_xboole_0
% 11.41/1.99      | sK0 != X1 ),
% 11.41/1.99      inference(resolution_lifted,[status(thm)],[c_14,c_25]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_362,plain,
% 11.41/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.99      | ~ l1_pre_topc(sK0)
% 11.41/1.99      | k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) = k1_xboole_0 ),
% 11.41/1.99      inference(unflattening,[status(thm)],[c_361]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_366,plain,
% 11.41/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.41/1.99      | k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) = k1_xboole_0 ),
% 11.41/1.99      inference(global_propositional_subsumption,
% 11.41/1.99                [status(thm)],
% 11.41/1.99                [c_362,c_24]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_1375,plain,
% 11.41/1.99      ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,X0))) = k1_xboole_0
% 11.41/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.41/1.99      inference(predicate_to_equality,[status(thm)],[c_366]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_2877,plain,
% 11.41/1.99      ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,X0)))) = k1_xboole_0
% 11.41/1.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_1366,c_1375]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_5448,plain,
% 11.41/1.99      ( k1_tops_1(sK0,k2_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1)))) = k1_xboole_0 ),
% 11.41/1.99      inference(superposition,[status(thm)],[c_1378,c_2877]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_19009,plain,
% 11.41/1.99      ( k1_tops_1(sK0,k2_tops_1(sK0,k1_tops_1(sK0,sK1))) = k1_xboole_0 ),
% 11.41/1.99      inference(demodulation,[status(thm)],[c_18952,c_5448]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_45038,plain,
% 11.41/1.99      ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) = k1_xboole_0 ),
% 11.41/1.99      inference(demodulation,[status(thm)],[c_44771,c_19009]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(c_21,negated_conjecture,
% 11.41/1.99      ( k1_tops_1(sK0,k2_tops_1(sK0,sK1)) != k1_xboole_0 ),
% 11.41/1.99      inference(cnf_transformation,[],[f81]) ).
% 11.41/1.99  
% 11.41/1.99  cnf(contradiction,plain,
% 11.41/1.99      ( $false ),
% 11.41/1.99      inference(minisat,[status(thm)],[c_45038,c_21]) ).
% 11.41/1.99  
% 11.41/1.99  
% 11.41/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.41/1.99  
% 11.41/1.99  ------                               Statistics
% 11.41/1.99  
% 11.41/1.99  ------ General
% 11.41/1.99  
% 11.41/1.99  abstr_ref_over_cycles:                  0
% 11.41/1.99  abstr_ref_under_cycles:                 0
% 11.41/1.99  gc_basic_clause_elim:                   0
% 11.41/1.99  forced_gc_time:                         0
% 11.41/1.99  parsing_time:                           0.009
% 11.41/1.99  unif_index_cands_time:                  0.
% 11.41/1.99  unif_index_add_time:                    0.
% 11.41/1.99  orderings_time:                         0.
% 11.41/1.99  out_proof_time:                         0.014
% 11.41/1.99  total_time:                             1.267
% 11.41/1.99  num_of_symbols:                         48
% 11.41/1.99  num_of_terms:                           49539
% 11.41/1.99  
% 11.41/1.99  ------ Preprocessing
% 11.41/1.99  
% 11.41/1.99  num_of_splits:                          0
% 11.41/1.99  num_of_split_atoms:                     0
% 11.41/1.99  num_of_reused_defs:                     0
% 11.41/1.99  num_eq_ax_congr_red:                    4
% 11.41/1.99  num_of_sem_filtered_clauses:            1
% 11.41/1.99  num_of_subtypes:                        0
% 11.41/1.99  monotx_restored_types:                  0
% 11.41/1.99  sat_num_of_epr_types:                   0
% 11.41/1.99  sat_num_of_non_cyclic_types:            0
% 11.41/1.99  sat_guarded_non_collapsed_types:        0
% 11.41/1.99  num_pure_diseq_elim:                    0
% 11.41/1.99  simp_replaced_by:                       0
% 11.41/1.99  res_preprocessed:                       102
% 11.41/1.99  prep_upred:                             0
% 11.41/1.99  prep_unflattend:                        28
% 11.41/1.99  smt_new_axioms:                         0
% 11.41/1.99  pred_elim_cands:                        3
% 11.41/1.99  pred_elim:                              5
% 11.41/1.99  pred_elim_cl:                           7
% 11.41/1.99  pred_elim_cycles:                       8
% 11.41/1.99  merged_defs:                            0
% 11.41/1.99  merged_defs_ncl:                        0
% 11.41/1.99  bin_hyper_res:                          0
% 11.41/1.99  prep_cycles:                            4
% 11.41/1.99  pred_elim_time:                         0.023
% 11.41/1.99  splitting_time:                         0.
% 11.41/1.99  sem_filter_time:                        0.
% 11.41/1.99  monotx_time:                            0.001
% 11.41/1.99  subtype_inf_time:                       0.
% 11.41/1.99  
% 11.41/1.99  ------ Problem properties
% 11.41/1.99  
% 11.41/1.99  clauses:                                18
% 11.41/1.99  conjectures:                            2
% 11.41/1.99  epr:                                    2
% 11.41/1.99  horn:                                   18
% 11.41/1.99  ground:                                 4
% 11.41/1.99  unary:                                  5
% 11.41/1.99  binary:                                 9
% 11.41/1.99  lits:                                   39
% 11.41/1.99  lits_eq:                                6
% 11.41/1.99  fd_pure:                                0
% 11.41/1.99  fd_pseudo:                              0
% 11.41/1.99  fd_cond:                                0
% 11.41/1.99  fd_pseudo_cond:                         1
% 11.41/1.99  ac_symbols:                             0
% 11.41/1.99  
% 11.41/1.99  ------ Propositional Solver
% 11.41/1.99  
% 11.41/1.99  prop_solver_calls:                      33
% 11.41/1.99  prop_fast_solver_calls:                 1557
% 11.41/1.99  smt_solver_calls:                       0
% 11.41/1.99  smt_fast_solver_calls:                  0
% 11.41/1.99  prop_num_of_clauses:                    15678
% 11.41/1.99  prop_preprocess_simplified:             25077
% 11.41/1.99  prop_fo_subsumed:                       76
% 11.41/1.99  prop_solver_time:                       0.
% 11.41/1.99  smt_solver_time:                        0.
% 11.41/1.99  smt_fast_solver_time:                   0.
% 11.41/1.99  prop_fast_solver_time:                  0.
% 11.41/1.99  prop_unsat_core_time:                   0.002
% 11.41/1.99  
% 11.41/1.99  ------ QBF
% 11.41/1.99  
% 11.41/1.99  qbf_q_res:                              0
% 11.41/1.99  qbf_num_tautologies:                    0
% 11.41/1.99  qbf_prep_cycles:                        0
% 11.41/1.99  
% 11.41/1.99  ------ BMC1
% 11.41/1.99  
% 11.41/1.99  bmc1_current_bound:                     -1
% 11.41/1.99  bmc1_last_solved_bound:                 -1
% 11.41/1.99  bmc1_unsat_core_size:                   -1
% 11.41/1.99  bmc1_unsat_core_parents_size:           -1
% 11.41/1.99  bmc1_merge_next_fun:                    0
% 11.41/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.41/1.99  
% 11.41/1.99  ------ Instantiation
% 11.41/1.99  
% 11.41/1.99  inst_num_of_clauses:                    5220
% 11.41/1.99  inst_num_in_passive:                    3279
% 11.41/1.99  inst_num_in_active:                     1806
% 11.41/1.99  inst_num_in_unprocessed:                135
% 11.41/1.99  inst_num_of_loops:                      1960
% 11.41/1.99  inst_num_of_learning_restarts:          0
% 11.41/1.99  inst_num_moves_active_passive:          151
% 11.41/1.99  inst_lit_activity:                      0
% 11.41/1.99  inst_lit_activity_moves:                2
% 11.41/1.99  inst_num_tautologies:                   0
% 11.41/1.99  inst_num_prop_implied:                  0
% 11.41/1.99  inst_num_existing_simplified:           0
% 11.41/1.99  inst_num_eq_res_simplified:             0
% 11.41/1.99  inst_num_child_elim:                    0
% 11.41/1.99  inst_num_of_dismatching_blockings:      7317
% 11.41/1.99  inst_num_of_non_proper_insts:           5752
% 11.41/1.99  inst_num_of_duplicates:                 0
% 11.41/1.99  inst_inst_num_from_inst_to_res:         0
% 11.41/1.99  inst_dismatching_checking_time:         0.
% 11.41/1.99  
% 11.41/1.99  ------ Resolution
% 11.41/1.99  
% 11.41/1.99  res_num_of_clauses:                     0
% 11.41/1.99  res_num_in_passive:                     0
% 11.41/1.99  res_num_in_active:                      0
% 11.41/1.99  res_num_of_loops:                       106
% 11.41/1.99  res_forward_subset_subsumed:            133
% 11.41/1.99  res_backward_subset_subsumed:           2
% 11.41/1.99  res_forward_subsumed:                   0
% 11.41/1.99  res_backward_subsumed:                  0
% 11.41/1.99  res_forward_subsumption_resolution:     1
% 11.41/1.99  res_backward_subsumption_resolution:    0
% 11.41/1.99  res_clause_to_clause_subsumption:       5664
% 11.41/1.99  res_orphan_elimination:                 0
% 11.41/1.99  res_tautology_del:                      139
% 11.41/1.99  res_num_eq_res_simplified:              0
% 11.41/1.99  res_num_sel_changes:                    0
% 11.41/1.99  res_moves_from_active_to_pass:          0
% 11.41/1.99  
% 11.41/1.99  ------ Superposition
% 11.41/1.99  
% 11.41/1.99  sup_time_total:                         0.
% 11.41/1.99  sup_time_generating:                    0.
% 11.41/1.99  sup_time_sim_full:                      0.
% 11.41/1.99  sup_time_sim_immed:                     0.
% 11.41/1.99  
% 11.41/1.99  sup_num_of_clauses:                     1042
% 11.41/1.99  sup_num_in_active:                      325
% 11.41/1.99  sup_num_in_passive:                     717
% 11.41/1.99  sup_num_of_loops:                       390
% 11.41/1.99  sup_fw_superposition:                   950
% 11.41/1.99  sup_bw_superposition:                   1091
% 11.41/1.99  sup_immediate_simplified:               1098
% 11.41/1.99  sup_given_eliminated:                   0
% 11.41/1.99  comparisons_done:                       0
% 11.41/1.99  comparisons_avoided:                    0
% 11.41/1.99  
% 11.41/1.99  ------ Simplifications
% 11.41/1.99  
% 11.41/1.99  
% 11.41/1.99  sim_fw_subset_subsumed:                 310
% 11.41/1.99  sim_bw_subset_subsumed:                 7
% 11.41/1.99  sim_fw_subsumed:                        369
% 11.41/1.99  sim_bw_subsumed:                        0
% 11.41/1.99  sim_fw_subsumption_res:                 0
% 11.41/1.99  sim_bw_subsumption_res:                 0
% 11.41/1.99  sim_tautology_del:                      15
% 11.41/1.99  sim_eq_tautology_del:                   106
% 11.41/1.99  sim_eq_res_simp:                        0
% 11.41/1.99  sim_fw_demodulated:                     19
% 11.41/1.99  sim_bw_demodulated:                     61
% 11.41/1.99  sim_light_normalised:                   751
% 11.41/1.99  sim_joinable_taut:                      0
% 11.41/1.99  sim_joinable_simp:                      0
% 11.41/1.99  sim_ac_normalised:                      0
% 11.41/1.99  sim_smt_subsumption:                    0
% 11.41/1.99  
%------------------------------------------------------------------------------
