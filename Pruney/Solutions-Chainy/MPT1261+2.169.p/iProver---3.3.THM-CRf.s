%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:48 EST 2020

% Result     : Theorem 11.62s
% Output     : CNFRefutation 11.62s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 922 expanded)
%              Number of clauses        :   86 ( 281 expanded)
%              Number of leaves         :   18 ( 197 expanded)
%              Depth                    :   20
%              Number of atoms          :  387 (3996 expanded)
%              Number of equality atoms :  186 (1242 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f38,plain,(
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

fof(f37,plain,
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

fof(f39,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).

fof(f60,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f59,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f49,f42])).

fof(f61,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
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

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f44,f42])).

fof(f58,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tops_1(X0,X1),X1)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f66,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f45,f42])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f46,f42])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f62,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_795,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_801,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_804,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2205,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k2_tops_1(X1,X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_801,c_804])).

cnf(c_1267,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_795,c_804])).

cnf(c_9,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_805,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_149,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_9])).

cnf(c_150,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_149])).

cnf(c_191,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X1)
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_150])).

cnf(c_790,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_191])).

cnf(c_32785,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_805,c_790])).

cnf(c_33942,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
    | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1267,c_32785])).

cnf(c_34655,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2205,c_33942])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_23,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_35014,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_34655,c_23])).

cnf(c_35015,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_35014])).

cnf(c_35024,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_795,c_35015])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_800,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2394,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_795,c_800])).

cnf(c_1078,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2535,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2394,c_20,c_19,c_1078])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_192,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_150])).

cnf(c_789,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_192])).

cnf(c_1460,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_1267,c_789])).

cnf(c_18,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_796,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1628,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1460,c_796])).

cnf(c_12,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_802,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2425,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_795,c_802])).

cnf(c_2539,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2425,c_23])).

cnf(c_2540,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2539])).

cnf(c_2545,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1628,c_2540])).

cnf(c_3,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_806,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3033,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2545,c_806])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_22,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_24,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1075,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1076,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | v4_pre_topc(sK1,sK0) = iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1075])).

cnf(c_15,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k2_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_799,plain,
    ( v4_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2046,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_795,c_799])).

cnf(c_2671,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2046,c_23])).

cnf(c_2672,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_2671])).

cnf(c_4108,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3033,c_22,c_23,c_24,c_1076,c_2672])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_808,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4113,plain,
    ( k5_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(k2_tops_1(sK0,sK1),sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4108,c_808])).

cnf(c_4,plain,
    ( k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_6717,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_4113,c_4])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_6724,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
    inference(demodulation,[status(thm)],[c_6717,c_2])).

cnf(c_35026,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_35024,c_2535,c_6724])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_798,plain,
    ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2233,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_795,c_798])).

cnf(c_2236,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2233,c_1460])).

cnf(c_2692,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2236,c_23])).

cnf(c_2696,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2692,c_806])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_189,plain,
    ( ~ r1_tarski(X0,X1)
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_150])).

cnf(c_792,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_189])).

cnf(c_14575,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_2696,c_792])).

cnf(c_14572,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_4108,c_792])).

cnf(c_14639,plain,
    ( k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_14572,c_2692])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_190,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_150])).

cnf(c_791,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_190])).

cnf(c_9856,plain,
    ( k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_4108,c_791])).

cnf(c_15390,plain,
    ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_14639,c_9856])).

cnf(c_21504,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_14575,c_15390])).

cnf(c_17,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_797,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1629,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) != k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1460,c_797])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_35026,c_21504,c_1629,c_1076,c_24,c_23,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:12:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 11.62/2.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.62/2.00  
% 11.62/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.62/2.00  
% 11.62/2.00  ------  iProver source info
% 11.62/2.00  
% 11.62/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.62/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.62/2.00  git: non_committed_changes: false
% 11.62/2.00  git: last_make_outside_of_git: false
% 11.62/2.00  
% 11.62/2.00  ------ 
% 11.62/2.00  ------ Parsing...
% 11.62/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.62/2.00  
% 11.62/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 11.62/2.00  
% 11.62/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.62/2.00  
% 11.62/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.62/2.00  ------ Proving...
% 11.62/2.00  ------ Problem Properties 
% 11.62/2.00  
% 11.62/2.00  
% 11.62/2.00  clauses                                 22
% 11.62/2.00  conjectures                             5
% 11.62/2.00  EPR                                     2
% 11.62/2.00  Horn                                    21
% 11.62/2.00  unary                                   6
% 11.62/2.00  binary                                  9
% 11.62/2.00  lits                                    49
% 11.62/2.00  lits eq                                 14
% 11.62/2.00  fd_pure                                 0
% 11.62/2.00  fd_pseudo                               0
% 11.62/2.00  fd_cond                                 0
% 11.62/2.00  fd_pseudo_cond                          0
% 11.62/2.00  AC symbols                              0
% 11.62/2.00  
% 11.62/2.00  ------ Input Options Time Limit: Unbounded
% 11.62/2.00  
% 11.62/2.00  
% 11.62/2.00  ------ 
% 11.62/2.00  Current options:
% 11.62/2.00  ------ 
% 11.62/2.00  
% 11.62/2.00  
% 11.62/2.00  
% 11.62/2.00  
% 11.62/2.00  ------ Proving...
% 11.62/2.00  
% 11.62/2.00  
% 11.62/2.00  % SZS status Theorem for theBenchmark.p
% 11.62/2.00  
% 11.62/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.62/2.00  
% 11.62/2.00  fof(f16,conjecture,(
% 11.62/2.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 11.62/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f17,negated_conjecture,(
% 11.62/2.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 11.62/2.00    inference(negated_conjecture,[],[f16])).
% 11.62/2.00  
% 11.62/2.00  fof(f31,plain,(
% 11.62/2.00    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 11.62/2.00    inference(ennf_transformation,[],[f17])).
% 11.62/2.00  
% 11.62/2.00  fof(f32,plain,(
% 11.62/2.00    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.62/2.00    inference(flattening,[],[f31])).
% 11.62/2.00  
% 11.62/2.00  fof(f35,plain,(
% 11.62/2.00    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.62/2.00    inference(nnf_transformation,[],[f32])).
% 11.62/2.00  
% 11.62/2.00  fof(f36,plain,(
% 11.62/2.00    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.62/2.00    inference(flattening,[],[f35])).
% 11.62/2.00  
% 11.62/2.00  fof(f38,plain,(
% 11.62/2.00    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.62/2.00    introduced(choice_axiom,[])).
% 11.62/2.00  
% 11.62/2.00  fof(f37,plain,(
% 11.62/2.00    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 11.62/2.00    introduced(choice_axiom,[])).
% 11.62/2.00  
% 11.62/2.00  fof(f39,plain,(
% 11.62/2.00    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 11.62/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f38,f37])).
% 11.62/2.00  
% 11.62/2.00  fof(f60,plain,(
% 11.62/2.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.62/2.00    inference(cnf_transformation,[],[f39])).
% 11.62/2.00  
% 11.62/2.00  fof(f12,axiom,(
% 11.62/2.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.62/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f25,plain,(
% 11.62/2.00    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.62/2.00    inference(ennf_transformation,[],[f12])).
% 11.62/2.00  
% 11.62/2.00  fof(f26,plain,(
% 11.62/2.00    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.62/2.00    inference(flattening,[],[f25])).
% 11.62/2.00  
% 11.62/2.00  fof(f54,plain,(
% 11.62/2.00    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f26])).
% 11.62/2.00  
% 11.62/2.00  fof(f10,axiom,(
% 11.62/2.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.62/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f34,plain,(
% 11.62/2.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.62/2.00    inference(nnf_transformation,[],[f10])).
% 11.62/2.00  
% 11.62/2.00  fof(f50,plain,(
% 11.62/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.62/2.00    inference(cnf_transformation,[],[f34])).
% 11.62/2.00  
% 11.62/2.00  fof(f51,plain,(
% 11.62/2.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f34])).
% 11.62/2.00  
% 11.62/2.00  fof(f8,axiom,(
% 11.62/2.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 11.62/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f20,plain,(
% 11.62/2.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 11.62/2.00    inference(ennf_transformation,[],[f8])).
% 11.62/2.00  
% 11.62/2.00  fof(f21,plain,(
% 11.62/2.00    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.62/2.00    inference(flattening,[],[f20])).
% 11.62/2.00  
% 11.62/2.00  fof(f48,plain,(
% 11.62/2.00    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.62/2.00    inference(cnf_transformation,[],[f21])).
% 11.62/2.00  
% 11.62/2.00  fof(f59,plain,(
% 11.62/2.00    l1_pre_topc(sK0)),
% 11.62/2.00    inference(cnf_transformation,[],[f39])).
% 11.62/2.00  
% 11.62/2.00  fof(f13,axiom,(
% 11.62/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 11.62/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f27,plain,(
% 11.62/2.00    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.62/2.00    inference(ennf_transformation,[],[f13])).
% 11.62/2.00  
% 11.62/2.00  fof(f55,plain,(
% 11.62/2.00    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f27])).
% 11.62/2.00  
% 11.62/2.00  fof(f9,axiom,(
% 11.62/2.00    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 11.62/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f22,plain,(
% 11.62/2.00    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.62/2.00    inference(ennf_transformation,[],[f9])).
% 11.62/2.00  
% 11.62/2.00  fof(f49,plain,(
% 11.62/2.00    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.62/2.00    inference(cnf_transformation,[],[f22])).
% 11.62/2.00  
% 11.62/2.00  fof(f2,axiom,(
% 11.62/2.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.62/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f42,plain,(
% 11.62/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.62/2.00    inference(cnf_transformation,[],[f2])).
% 11.62/2.00  
% 11.62/2.00  fof(f68,plain,(
% 11.62/2.00    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.62/2.00    inference(definition_unfolding,[],[f49,f42])).
% 11.62/2.00  
% 11.62/2.00  fof(f61,plain,(
% 11.62/2.00    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 11.62/2.00    inference(cnf_transformation,[],[f39])).
% 11.62/2.00  
% 11.62/2.00  fof(f11,axiom,(
% 11.62/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 11.62/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f23,plain,(
% 11.62/2.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.62/2.00    inference(ennf_transformation,[],[f11])).
% 11.62/2.00  
% 11.62/2.00  fof(f24,plain,(
% 11.62/2.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.62/2.00    inference(flattening,[],[f23])).
% 11.62/2.00  
% 11.62/2.00  fof(f52,plain,(
% 11.62/2.00    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f24])).
% 11.62/2.00  
% 11.62/2.00  fof(f4,axiom,(
% 11.62/2.00    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 11.62/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f44,plain,(
% 11.62/2.00    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f4])).
% 11.62/2.00  
% 11.62/2.00  fof(f65,plain,(
% 11.62/2.00    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 11.62/2.00    inference(definition_unfolding,[],[f44,f42])).
% 11.62/2.00  
% 11.62/2.00  fof(f58,plain,(
% 11.62/2.00    v2_pre_topc(sK0)),
% 11.62/2.00    inference(cnf_transformation,[],[f39])).
% 11.62/2.00  
% 11.62/2.00  fof(f53,plain,(
% 11.62/2.00    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f24])).
% 11.62/2.00  
% 11.62/2.00  fof(f14,axiom,(
% 11.62/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 11.62/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f28,plain,(
% 11.62/2.00    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.62/2.00    inference(ennf_transformation,[],[f14])).
% 11.62/2.00  
% 11.62/2.00  fof(f29,plain,(
% 11.62/2.00    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.62/2.00    inference(flattening,[],[f28])).
% 11.62/2.00  
% 11.62/2.00  fof(f56,plain,(
% 11.62/2.00    ( ! [X0,X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f29])).
% 11.62/2.00  
% 11.62/2.00  fof(f1,axiom,(
% 11.62/2.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 11.62/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f33,plain,(
% 11.62/2.00    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 11.62/2.00    inference(nnf_transformation,[],[f1])).
% 11.62/2.00  
% 11.62/2.00  fof(f41,plain,(
% 11.62/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f33])).
% 11.62/2.00  
% 11.62/2.00  fof(f63,plain,(
% 11.62/2.00    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 11.62/2.00    inference(definition_unfolding,[],[f41,f42])).
% 11.62/2.00  
% 11.62/2.00  fof(f5,axiom,(
% 11.62/2.00    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 11.62/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f45,plain,(
% 11.62/2.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 11.62/2.00    inference(cnf_transformation,[],[f5])).
% 11.62/2.00  
% 11.62/2.00  fof(f66,plain,(
% 11.62/2.00    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 11.62/2.00    inference(definition_unfolding,[],[f45,f42])).
% 11.62/2.00  
% 11.62/2.00  fof(f3,axiom,(
% 11.62/2.00    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 11.62/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f43,plain,(
% 11.62/2.00    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.62/2.00    inference(cnf_transformation,[],[f3])).
% 11.62/2.00  
% 11.62/2.00  fof(f15,axiom,(
% 11.62/2.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)))),
% 11.62/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f30,plain,(
% 11.62/2.00    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.62/2.00    inference(ennf_transformation,[],[f15])).
% 11.62/2.00  
% 11.62/2.00  fof(f57,plain,(
% 11.62/2.00    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.62/2.00    inference(cnf_transformation,[],[f30])).
% 11.62/2.00  
% 11.62/2.00  fof(f6,axiom,(
% 11.62/2.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 11.62/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f18,plain,(
% 11.62/2.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.62/2.00    inference(ennf_transformation,[],[f6])).
% 11.62/2.00  
% 11.62/2.00  fof(f46,plain,(
% 11.62/2.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.62/2.00    inference(cnf_transformation,[],[f18])).
% 11.62/2.00  
% 11.62/2.00  fof(f67,plain,(
% 11.62/2.00    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.62/2.00    inference(definition_unfolding,[],[f46,f42])).
% 11.62/2.00  
% 11.62/2.00  fof(f7,axiom,(
% 11.62/2.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 11.62/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.62/2.00  
% 11.62/2.00  fof(f19,plain,(
% 11.62/2.00    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.62/2.00    inference(ennf_transformation,[],[f7])).
% 11.62/2.00  
% 11.62/2.00  fof(f47,plain,(
% 11.62/2.00    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.62/2.00    inference(cnf_transformation,[],[f19])).
% 11.62/2.00  
% 11.62/2.00  fof(f62,plain,(
% 11.62/2.00    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 11.62/2.00    inference(cnf_transformation,[],[f39])).
% 11.62/2.00  
% 11.62/2.00  cnf(c_19,negated_conjecture,
% 11.62/2.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.62/2.00      inference(cnf_transformation,[],[f60]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_795,plain,
% 11.62/2.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_13,plain,
% 11.62/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.62/2.00      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.62/2.00      | ~ l1_pre_topc(X1) ),
% 11.62/2.00      inference(cnf_transformation,[],[f54]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_801,plain,
% 11.62/2.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.62/2.00      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 11.62/2.00      | l1_pre_topc(X1) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_10,plain,
% 11.62/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.62/2.00      inference(cnf_transformation,[],[f50]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_804,plain,
% 11.62/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.62/2.00      | r1_tarski(X0,X1) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2205,plain,
% 11.62/2.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.62/2.00      | r1_tarski(k2_tops_1(X1,X0),u1_struct_0(X1)) = iProver_top
% 11.62/2.00      | l1_pre_topc(X1) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_801,c_804]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_1267,plain,
% 11.62/2.00      ( r1_tarski(sK1,u1_struct_0(sK0)) = iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_795,c_804]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_9,plain,
% 11.62/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.62/2.00      inference(cnf_transformation,[],[f51]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_805,plain,
% 11.62/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 11.62/2.00      | r1_tarski(X0,X1) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_7,plain,
% 11.62/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.62/2.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 11.62/2.00      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 11.62/2.00      inference(cnf_transformation,[],[f48]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_149,plain,
% 11.62/2.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 11.62/2.00      inference(prop_impl,[status(thm)],[c_9]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_150,plain,
% 11.62/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.62/2.00      inference(renaming,[status(thm)],[c_149]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_191,plain,
% 11.62/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.62/2.00      | ~ r1_tarski(X2,X1)
% 11.62/2.00      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 11.62/2.00      inference(bin_hyper_res,[status(thm)],[c_7,c_150]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_790,plain,
% 11.62/2.00      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 11.62/2.00      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 11.62/2.00      | r1_tarski(X1,X0) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_191]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_32785,plain,
% 11.62/2.00      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 11.62/2.00      | r1_tarski(X2,X0) != iProver_top
% 11.62/2.00      | r1_tarski(X1,X0) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_805,c_790]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_33942,plain,
% 11.62/2.00      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
% 11.62/2.00      | r1_tarski(X0,u1_struct_0(sK0)) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_1267,c_32785]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_34655,plain,
% 11.62/2.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
% 11.62/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.62/2.00      | l1_pre_topc(sK0) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_2205,c_33942]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_20,negated_conjecture,
% 11.62/2.00      ( l1_pre_topc(sK0) ),
% 11.62/2.00      inference(cnf_transformation,[],[f59]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_23,plain,
% 11.62/2.00      ( l1_pre_topc(sK0) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_35014,plain,
% 11.62/2.00      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.62/2.00      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0)) ),
% 11.62/2.00      inference(global_propositional_subsumption,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_34655,c_23]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_35015,plain,
% 11.62/2.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
% 11.62/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.62/2.00      inference(renaming,[status(thm)],[c_35014]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_35024,plain,
% 11.62/2.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_795,c_35015]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_14,plain,
% 11.62/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.62/2.00      | ~ l1_pre_topc(X1)
% 11.62/2.00      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 11.62/2.00      inference(cnf_transformation,[],[f55]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_800,plain,
% 11.62/2.00      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 11.62/2.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.62/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2394,plain,
% 11.62/2.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 11.62/2.00      | l1_pre_topc(sK0) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_795,c_800]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_1078,plain,
% 11.62/2.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.62/2.00      | ~ l1_pre_topc(sK0)
% 11.62/2.00      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 11.62/2.00      inference(instantiation,[status(thm)],[c_14]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2535,plain,
% 11.62/2.00      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 11.62/2.00      inference(global_propositional_subsumption,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_2394,c_20,c_19,c_1078]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_8,plain,
% 11.62/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.62/2.00      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 11.62/2.00      inference(cnf_transformation,[],[f68]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_192,plain,
% 11.62/2.00      ( ~ r1_tarski(X0,X1)
% 11.62/2.00      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 11.62/2.00      inference(bin_hyper_res,[status(thm)],[c_8,c_150]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_789,plain,
% 11.62/2.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
% 11.62/2.00      | r1_tarski(X0,X2) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_192]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_1460,plain,
% 11.62/2.00      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_1267,c_789]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_18,negated_conjecture,
% 11.62/2.00      ( v4_pre_topc(sK1,sK0)
% 11.62/2.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.62/2.00      inference(cnf_transformation,[],[f61]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_796,plain,
% 11.62/2.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 11.62/2.00      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_1628,plain,
% 11.62/2.00      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1)
% 11.62/2.00      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 11.62/2.00      inference(demodulation,[status(thm)],[c_1460,c_796]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_12,plain,
% 11.62/2.00      ( ~ v4_pre_topc(X0,X1)
% 11.62/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.62/2.00      | ~ l1_pre_topc(X1)
% 11.62/2.00      | k2_pre_topc(X1,X0) = X0 ),
% 11.62/2.00      inference(cnf_transformation,[],[f52]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_802,plain,
% 11.62/2.00      ( k2_pre_topc(X0,X1) = X1
% 11.62/2.00      | v4_pre_topc(X1,X0) != iProver_top
% 11.62/2.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.62/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2425,plain,
% 11.62/2.00      ( k2_pre_topc(sK0,sK1) = sK1
% 11.62/2.00      | v4_pre_topc(sK1,sK0) != iProver_top
% 11.62/2.00      | l1_pre_topc(sK0) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_795,c_802]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2539,plain,
% 11.62/2.00      ( v4_pre_topc(sK1,sK0) != iProver_top
% 11.62/2.00      | k2_pre_topc(sK0,sK1) = sK1 ),
% 11.62/2.00      inference(global_propositional_subsumption,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_2425,c_23]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2540,plain,
% 11.62/2.00      ( k2_pre_topc(sK0,sK1) = sK1
% 11.62/2.00      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 11.62/2.00      inference(renaming,[status(thm)],[c_2539]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2545,plain,
% 11.62/2.00      ( k2_pre_topc(sK0,sK1) = sK1
% 11.62/2.00      | k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_1628,c_2540]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_3,plain,
% 11.62/2.00      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 11.62/2.00      inference(cnf_transformation,[],[f65]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_806,plain,
% 11.62/2.00      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_3033,plain,
% 11.62/2.00      ( k2_pre_topc(sK0,sK1) = sK1
% 11.62/2.00      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_2545,c_806]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_21,negated_conjecture,
% 11.62/2.00      ( v2_pre_topc(sK0) ),
% 11.62/2.00      inference(cnf_transformation,[],[f58]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_22,plain,
% 11.62/2.00      ( v2_pre_topc(sK0) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_24,plain,
% 11.62/2.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_11,plain,
% 11.62/2.00      ( v4_pre_topc(X0,X1)
% 11.62/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.62/2.00      | ~ l1_pre_topc(X1)
% 11.62/2.00      | ~ v2_pre_topc(X1)
% 11.62/2.00      | k2_pre_topc(X1,X0) != X0 ),
% 11.62/2.00      inference(cnf_transformation,[],[f53]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_1075,plain,
% 11.62/2.00      ( v4_pre_topc(sK1,sK0)
% 11.62/2.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.62/2.00      | ~ l1_pre_topc(sK0)
% 11.62/2.00      | ~ v2_pre_topc(sK0)
% 11.62/2.00      | k2_pre_topc(sK0,sK1) != sK1 ),
% 11.62/2.00      inference(instantiation,[status(thm)],[c_11]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_1076,plain,
% 11.62/2.00      ( k2_pre_topc(sK0,sK1) != sK1
% 11.62/2.00      | v4_pre_topc(sK1,sK0) = iProver_top
% 11.62/2.00      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.62/2.00      | l1_pre_topc(sK0) != iProver_top
% 11.62/2.00      | v2_pre_topc(sK0) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_1075]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_15,plain,
% 11.62/2.00      ( ~ v4_pre_topc(X0,X1)
% 11.62/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.62/2.00      | r1_tarski(k2_tops_1(X1,X0),X0)
% 11.62/2.00      | ~ l1_pre_topc(X1) ),
% 11.62/2.00      inference(cnf_transformation,[],[f56]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_799,plain,
% 11.62/2.00      ( v4_pre_topc(X0,X1) != iProver_top
% 11.62/2.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.62/2.00      | r1_tarski(k2_tops_1(X1,X0),X0) = iProver_top
% 11.62/2.00      | l1_pre_topc(X1) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2046,plain,
% 11.62/2.00      ( v4_pre_topc(sK1,sK0) != iProver_top
% 11.62/2.00      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
% 11.62/2.00      | l1_pre_topc(sK0) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_795,c_799]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2671,plain,
% 11.62/2.00      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top
% 11.62/2.00      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 11.62/2.00      inference(global_propositional_subsumption,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_2046,c_23]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2672,plain,
% 11.62/2.00      ( v4_pre_topc(sK1,sK0) != iProver_top
% 11.62/2.00      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 11.62/2.00      inference(renaming,[status(thm)],[c_2671]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_4108,plain,
% 11.62/2.00      ( r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 11.62/2.00      inference(global_propositional_subsumption,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_3033,c_22,c_23,c_24,c_1076,c_2672]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_0,plain,
% 11.62/2.00      ( ~ r1_tarski(X0,X1)
% 11.62/2.00      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0 ),
% 11.62/2.00      inference(cnf_transformation,[],[f63]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_808,plain,
% 11.62/2.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k1_xboole_0
% 11.62/2.00      | r1_tarski(X0,X1) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_4113,plain,
% 11.62/2.00      ( k5_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(k2_tops_1(sK0,sK1),sK1)) = k1_xboole_0 ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_4108,c_808]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_4,plain,
% 11.62/2.00      ( k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
% 11.62/2.00      inference(cnf_transformation,[],[f66]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_6717,plain,
% 11.62/2.00      ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k1_xboole_0) ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_4113,c_4]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2,plain,
% 11.62/2.00      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 11.62/2.00      inference(cnf_transformation,[],[f43]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_6724,plain,
% 11.62/2.00      ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
% 11.62/2.00      inference(demodulation,[status(thm)],[c_6717,c_2]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_35026,plain,
% 11.62/2.00      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 11.62/2.00      inference(light_normalisation,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_35024,c_2535,c_6724]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_16,plain,
% 11.62/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.62/2.00      | ~ l1_pre_topc(X1)
% 11.62/2.00      | k7_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k1_tops_1(X1,X0) ),
% 11.62/2.00      inference(cnf_transformation,[],[f57]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_798,plain,
% 11.62/2.00      ( k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k1_tops_1(X0,X1)
% 11.62/2.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.62/2.00      | l1_pre_topc(X0) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2233,plain,
% 11.62/2.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1)
% 11.62/2.00      | l1_pre_topc(sK0) != iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_795,c_798]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2236,plain,
% 11.62/2.00      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1)
% 11.62/2.00      | l1_pre_topc(sK0) != iProver_top ),
% 11.62/2.00      inference(demodulation,[status(thm)],[c_2233,c_1460]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2692,plain,
% 11.62/2.00      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k1_tops_1(sK0,sK1) ),
% 11.62/2.00      inference(global_propositional_subsumption,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_2236,c_23]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_2696,plain,
% 11.62/2.00      ( r1_tarski(k1_tops_1(sK0,sK1),sK1) = iProver_top ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_2692,c_806]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_5,plain,
% 11.62/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.62/2.00      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 11.62/2.00      inference(cnf_transformation,[],[f67]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_189,plain,
% 11.62/2.00      ( ~ r1_tarski(X0,X1)
% 11.62/2.00      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 11.62/2.00      inference(bin_hyper_res,[status(thm)],[c_5,c_150]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_792,plain,
% 11.62/2.00      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 11.62/2.00      | r1_tarski(X1,X0) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_189]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_14575,plain,
% 11.62/2.00      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_2696,c_792]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_14572,plain,
% 11.62/2.00      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_4108,c_792]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_14639,plain,
% 11.62/2.00      ( k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k1_tops_1(sK0,sK1) ),
% 11.62/2.00      inference(light_normalisation,[status(thm)],[c_14572,c_2692]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_6,plain,
% 11.62/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.62/2.00      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 11.62/2.00      inference(cnf_transformation,[],[f47]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_190,plain,
% 11.62/2.00      ( ~ r1_tarski(X0,X1) | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 11.62/2.00      inference(bin_hyper_res,[status(thm)],[c_6,c_150]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_791,plain,
% 11.62/2.00      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 11.62/2.00      | r1_tarski(X1,X0) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_190]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_9856,plain,
% 11.62/2.00      ( k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
% 11.62/2.00      inference(superposition,[status(thm)],[c_4108,c_791]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_15390,plain,
% 11.62/2.00      ( k3_subset_1(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.62/2.00      inference(demodulation,[status(thm)],[c_14639,c_9856]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_21504,plain,
% 11.62/2.00      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
% 11.62/2.00      inference(light_normalisation,[status(thm)],[c_14575,c_15390]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_17,negated_conjecture,
% 11.62/2.00      ( ~ v4_pre_topc(sK1,sK0)
% 11.62/2.00      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 11.62/2.00      inference(cnf_transformation,[],[f62]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_797,plain,
% 11.62/2.00      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 11.62/2.00      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 11.62/2.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(c_1629,plain,
% 11.62/2.00      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) != k2_tops_1(sK0,sK1)
% 11.62/2.00      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 11.62/2.00      inference(demodulation,[status(thm)],[c_1460,c_797]) ).
% 11.62/2.00  
% 11.62/2.00  cnf(contradiction,plain,
% 11.62/2.00      ( $false ),
% 11.62/2.00      inference(minisat,
% 11.62/2.00                [status(thm)],
% 11.62/2.00                [c_35026,c_21504,c_1629,c_1076,c_24,c_23,c_22]) ).
% 11.62/2.00  
% 11.62/2.00  
% 11.62/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.62/2.00  
% 11.62/2.00  ------                               Statistics
% 11.62/2.00  
% 11.62/2.00  ------ Selected
% 11.62/2.00  
% 11.62/2.00  total_time:                             1.12
% 11.62/2.00  
%------------------------------------------------------------------------------
