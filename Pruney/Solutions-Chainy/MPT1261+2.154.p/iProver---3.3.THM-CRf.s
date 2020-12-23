%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:46 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 794 expanded)
%              Number of clauses        :   70 ( 228 expanded)
%              Number of leaves         :   17 ( 172 expanded)
%              Depth                    :   20
%              Number of atoms          :  333 (3547 expanded)
%              Number of equality atoms :  161 (1162 expanded)
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

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

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
    inference(nnf_transformation,[],[f35])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f39,plain,(
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

fof(f38,plain,
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

fof(f40,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f39,f38])).

fof(f59,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f26,plain,(
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

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f10])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_subset_1(X0,X1,k2_subset_1(X0)) = k2_subset_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_subset_1(X0,X1,k2_subset_1(X0)) = k2_subset_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_subset_1(X0,X1,k2_subset_1(X0)) = k2_subset_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f21])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f62,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(definition_unfolding,[],[f43,f42])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k3_tarski(k1_enumset1(X1,X1,X2)) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f47,f62])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f19])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f57,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_668,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_679,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1307,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_668,c_679])).

cnf(c_15,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_669,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1497,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1307,c_669])).

cnf(c_9,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_675,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2364,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_668,c_675])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_20,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2537,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2364,c_20])).

cnf(c_2538,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2537])).

cnf(c_2543,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_1497,c_2538])).

cnf(c_0,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_683,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_677,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,k2_subset_1(X1)) = k2_subset_1(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_678,plain,
    ( k4_subset_1(X0,X1,k2_subset_1(X0)) = k2_subset_1(X0)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_701,plain,
    ( k4_subset_1(X0,X1,X0) = X0
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_678,c_2])).

cnf(c_1288,plain,
    ( k4_subset_1(X0,X1,X0) = X0
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_677,c_701])).

cnf(c_1898,plain,
    ( k4_subset_1(X0,k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_683,c_1288])).

cnf(c_3719,plain,
    ( k4_subset_1(sK1,k2_tops_1(sK0,sK1),sK1) = sK1
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_2543,c_1898])).

cnf(c_3720,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2543,c_683])).

cnf(c_3,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_681,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_692,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_681,c_2])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k3_tarski(k1_enumset1(X2,X2,X0)) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_680,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = k4_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2117,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = k4_subset_1(X1,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_692,c_680])).

cnf(c_4902,plain,
    ( k3_tarski(k1_enumset1(X0,X0,X1)) = k4_subset_1(X1,X0,X1)
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_677,c_2117])).

cnf(c_5145,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_tarski(k1_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) = k4_subset_1(sK1,k2_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[status(thm)],[c_3720,c_4902])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_674,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2116,plain,
    ( k3_tarski(k1_enumset1(X0,X0,sK1)) = k4_subset_1(u1_struct_0(sK0),X0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_668,c_680])).

cnf(c_2756,plain,
    ( k3_tarski(k1_enumset1(k2_tops_1(sK0,X0),k2_tops_1(sK0,X0),sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_674,c_2116])).

cnf(c_3573,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k3_tarski(k1_enumset1(k2_tops_1(sK0,X0),k2_tops_1(sK0,X0),sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2756,c_20])).

cnf(c_3574,plain,
    ( k3_tarski(k1_enumset1(k2_tops_1(sK0,X0),k2_tops_1(sK0,X0),sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3573])).

cnf(c_3583,plain,
    ( k3_tarski(k1_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) ),
    inference(superposition,[status(thm)],[c_668,c_3574])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k4_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_682,plain,
    ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2076,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_668,c_682])).

cnf(c_2633,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_674,c_2076])).

cnf(c_3450,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2633,c_20])).

cnf(c_3451,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),sK1)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3450])).

cnf(c_3460,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_668,c_3451])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_671,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1142,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_668,c_671])).

cnf(c_911,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1510,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1142,c_17,c_16,c_911])).

cnf(c_3465,plain,
    ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_3460,c_1510])).

cnf(c_3588,plain,
    ( k3_tarski(k1_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_3583,c_3465])).

cnf(c_5148,plain,
    ( k4_subset_1(sK1,k2_tops_1(sK0,sK1),sK1) = k2_pre_topc(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_5145,c_3588])).

cnf(c_5667,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_3719,c_5148])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_672,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1906,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_668,c_672])).

cnf(c_950,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2545,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1906,c_17,c_16,c_950])).

cnf(c_5732,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_5667,c_2545])).

cnf(c_8,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_905,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_14,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_18,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5732,c_5667,c_905,c_14,c_16,c_17,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:03:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.95/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/0.99  
% 3.95/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.95/0.99  
% 3.95/0.99  ------  iProver source info
% 3.95/0.99  
% 3.95/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.95/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.95/0.99  git: non_committed_changes: false
% 3.95/0.99  git: last_make_outside_of_git: false
% 3.95/0.99  
% 3.95/0.99  ------ 
% 3.95/0.99  ------ Parsing...
% 3.95/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.95/0.99  
% 3.95/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.95/0.99  
% 3.95/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.95/0.99  
% 3.95/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.95/0.99  ------ Proving...
% 3.95/0.99  ------ Problem Properties 
% 3.95/0.99  
% 3.95/0.99  
% 3.95/0.99  clauses                                 19
% 3.95/0.99  conjectures                             5
% 3.95/0.99  EPR                                     2
% 3.95/0.99  Horn                                    18
% 3.95/0.99  unary                                   6
% 3.95/0.99  binary                                  5
% 3.95/0.99  lits                                    44
% 3.95/0.99  lits eq                                 11
% 3.95/0.99  fd_pure                                 0
% 3.95/0.99  fd_pseudo                               0
% 3.95/0.99  fd_cond                                 0
% 3.95/0.99  fd_pseudo_cond                          0
% 3.95/0.99  AC symbols                              0
% 3.95/0.99  
% 3.95/0.99  ------ Input Options Time Limit: Unbounded
% 3.95/0.99  
% 3.95/0.99  
% 3.95/0.99  ------ 
% 3.95/0.99  Current options:
% 3.95/0.99  ------ 
% 3.95/0.99  
% 3.95/0.99  
% 3.95/0.99  
% 3.95/0.99  
% 3.95/0.99  ------ Proving...
% 3.95/0.99  
% 3.95/0.99  
% 3.95/0.99  % SZS status Theorem for theBenchmark.p
% 3.95/0.99  
% 3.95/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.95/0.99  
% 3.95/0.99  fof(f16,conjecture,(
% 3.95/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 3.95/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/0.99  
% 3.95/0.99  fof(f17,negated_conjecture,(
% 3.95/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 3.95/0.99    inference(negated_conjecture,[],[f16])).
% 3.95/0.99  
% 3.95/0.99  fof(f34,plain,(
% 3.95/0.99    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.95/0.99    inference(ennf_transformation,[],[f17])).
% 3.95/0.99  
% 3.95/0.99  fof(f35,plain,(
% 3.95/0.99    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.95/0.99    inference(flattening,[],[f34])).
% 3.95/0.99  
% 3.95/0.99  fof(f36,plain,(
% 3.95/0.99    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.95/0.99    inference(nnf_transformation,[],[f35])).
% 3.95/0.99  
% 3.95/0.99  fof(f37,plain,(
% 3.95/0.99    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.95/0.99    inference(flattening,[],[f36])).
% 3.95/0.99  
% 3.95/0.99  fof(f39,plain,(
% 3.95/0.99    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.95/0.99    introduced(choice_axiom,[])).
% 3.95/0.99  
% 3.95/0.99  fof(f38,plain,(
% 3.95/0.99    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.95/0.99    introduced(choice_axiom,[])).
% 3.95/0.99  
% 3.95/0.99  fof(f40,plain,(
% 3.95/0.99    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.95/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f39,f38])).
% 3.95/0.99  
% 3.95/0.99  fof(f59,plain,(
% 3.95/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.95/0.99    inference(cnf_transformation,[],[f40])).
% 3.95/0.99  
% 3.95/0.99  fof(f8,axiom,(
% 3.95/0.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.95/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/0.99  
% 3.95/0.99  fof(f23,plain,(
% 3.95/0.99    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.95/0.99    inference(ennf_transformation,[],[f8])).
% 3.95/0.99  
% 3.95/0.99  fof(f48,plain,(
% 3.95/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.95/0.99    inference(cnf_transformation,[],[f23])).
% 3.95/0.99  
% 3.95/0.99  fof(f60,plain,(
% 3.95/0.99    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 3.95/0.99    inference(cnf_transformation,[],[f40])).
% 3.95/0.99  
% 3.95/0.99  fof(f11,axiom,(
% 3.95/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.95/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/0.99  
% 3.95/0.99  fof(f26,plain,(
% 3.95/0.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.95/0.99    inference(ennf_transformation,[],[f11])).
% 3.95/0.99  
% 3.95/0.99  fof(f27,plain,(
% 3.95/0.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.95/0.99    inference(flattening,[],[f26])).
% 3.95/0.99  
% 3.95/0.99  fof(f51,plain,(
% 3.95/0.99    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.95/0.99    inference(cnf_transformation,[],[f27])).
% 3.95/0.99  
% 3.95/0.99  fof(f58,plain,(
% 3.95/0.99    l1_pre_topc(sK0)),
% 3.95/0.99    inference(cnf_transformation,[],[f40])).
% 3.95/0.99  
% 3.95/0.99  fof(f1,axiom,(
% 3.95/0.99    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.95/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/0.99  
% 3.95/0.99  fof(f41,plain,(
% 3.95/0.99    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.95/0.99    inference(cnf_transformation,[],[f1])).
% 3.95/0.99  
% 3.95/0.99  fof(f10,axiom,(
% 3.95/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.95/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/0.99  
% 3.95/0.99  fof(f18,plain,(
% 3.95/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 3.95/0.99    inference(unused_predicate_definition_removal,[],[f10])).
% 3.95/0.99  
% 3.95/0.99  fof(f25,plain,(
% 3.95/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 3.95/0.99    inference(ennf_transformation,[],[f18])).
% 3.95/0.99  
% 3.95/0.99  fof(f50,plain,(
% 3.95/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.95/0.99    inference(cnf_transformation,[],[f25])).
% 3.95/0.99  
% 3.95/0.99  fof(f9,axiom,(
% 3.95/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_subset_1(X0,X1,k2_subset_1(X0)) = k2_subset_1(X0))),
% 3.95/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/0.99  
% 3.95/0.99  fof(f24,plain,(
% 3.95/0.99    ! [X0,X1] : (k4_subset_1(X0,X1,k2_subset_1(X0)) = k2_subset_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.95/0.99    inference(ennf_transformation,[],[f9])).
% 3.95/0.99  
% 3.95/0.99  fof(f49,plain,(
% 3.95/0.99    ( ! [X0,X1] : (k4_subset_1(X0,X1,k2_subset_1(X0)) = k2_subset_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.95/0.99    inference(cnf_transformation,[],[f24])).
% 3.95/0.99  
% 3.95/0.99  fof(f5,axiom,(
% 3.95/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 3.95/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/0.99  
% 3.95/0.99  fof(f45,plain,(
% 3.95/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 3.95/0.99    inference(cnf_transformation,[],[f5])).
% 3.95/0.99  
% 3.95/0.99  fof(f6,axiom,(
% 3.95/0.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 3.95/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/0.99  
% 3.95/0.99  fof(f46,plain,(
% 3.95/0.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 3.95/0.99    inference(cnf_transformation,[],[f6])).
% 3.95/0.99  
% 3.95/0.99  fof(f7,axiom,(
% 3.95/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.95/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/0.99  
% 3.95/0.99  fof(f21,plain,(
% 3.95/0.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.95/0.99    inference(ennf_transformation,[],[f7])).
% 3.95/0.99  
% 3.95/0.99  fof(f22,plain,(
% 3.95/0.99    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.95/0.99    inference(flattening,[],[f21])).
% 3.95/0.99  
% 3.95/0.99  fof(f47,plain,(
% 3.95/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.95/0.99    inference(cnf_transformation,[],[f22])).
% 3.95/0.99  
% 3.95/0.99  fof(f3,axiom,(
% 3.95/0.99    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 3.95/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/0.99  
% 3.95/0.99  fof(f43,plain,(
% 3.95/0.99    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 3.95/0.99    inference(cnf_transformation,[],[f3])).
% 3.95/0.99  
% 3.95/0.99  fof(f2,axiom,(
% 3.95/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.95/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/0.99  
% 3.95/0.99  fof(f42,plain,(
% 3.95/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.95/0.99    inference(cnf_transformation,[],[f2])).
% 3.95/0.99  
% 3.95/0.99  fof(f62,plain,(
% 3.95/0.99    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = k2_xboole_0(X0,X1)) )),
% 3.95/0.99    inference(definition_unfolding,[],[f43,f42])).
% 3.95/0.99  
% 3.95/0.99  fof(f63,plain,(
% 3.95/0.99    ( ! [X2,X0,X1] : (k3_tarski(k1_enumset1(X1,X1,X2)) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.95/0.99    inference(definition_unfolding,[],[f47,f62])).
% 3.95/0.99  
% 3.95/0.99  fof(f12,axiom,(
% 3.95/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.95/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/0.99  
% 3.95/0.99  fof(f28,plain,(
% 3.95/0.99    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.95/0.99    inference(ennf_transformation,[],[f12])).
% 3.95/0.99  
% 3.95/0.99  fof(f29,plain,(
% 3.95/0.99    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.95/0.99    inference(flattening,[],[f28])).
% 3.95/0.99  
% 3.95/0.99  fof(f53,plain,(
% 3.95/0.99    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.95/0.99    inference(cnf_transformation,[],[f29])).
% 3.95/0.99  
% 3.95/0.99  fof(f4,axiom,(
% 3.95/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1))),
% 3.95/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/0.99  
% 3.95/0.99  fof(f19,plain,(
% 3.95/0.99    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.95/0.99    inference(ennf_transformation,[],[f4])).
% 3.95/0.99  
% 3.95/0.99  fof(f20,plain,(
% 3.95/0.99    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.95/0.99    inference(flattening,[],[f19])).
% 3.95/0.99  
% 3.95/0.99  fof(f44,plain,(
% 3.95/0.99    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.95/0.99    inference(cnf_transformation,[],[f20])).
% 3.95/0.99  
% 3.95/0.99  fof(f15,axiom,(
% 3.95/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 3.95/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/0.99  
% 3.95/0.99  fof(f33,plain,(
% 3.95/0.99    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.95/0.99    inference(ennf_transformation,[],[f15])).
% 3.95/0.99  
% 3.95/0.99  fof(f56,plain,(
% 3.95/0.99    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.95/0.99    inference(cnf_transformation,[],[f33])).
% 3.95/0.99  
% 3.95/0.99  fof(f14,axiom,(
% 3.95/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 3.95/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/0.99  
% 3.95/0.99  fof(f32,plain,(
% 3.95/0.99    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.95/0.99    inference(ennf_transformation,[],[f14])).
% 3.95/0.99  
% 3.95/0.99  fof(f55,plain,(
% 3.95/0.99    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.95/0.99    inference(cnf_transformation,[],[f32])).
% 3.95/0.99  
% 3.95/0.99  fof(f52,plain,(
% 3.95/0.99    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.95/0.99    inference(cnf_transformation,[],[f27])).
% 3.95/0.99  
% 3.95/0.99  fof(f61,plain,(
% 3.95/0.99    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 3.95/0.99    inference(cnf_transformation,[],[f40])).
% 3.95/0.99  
% 3.95/0.99  fof(f57,plain,(
% 3.95/0.99    v2_pre_topc(sK0)),
% 3.95/0.99    inference(cnf_transformation,[],[f40])).
% 3.95/0.99  
% 3.95/0.99  cnf(c_16,negated_conjecture,
% 3.95/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.95/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_668,plain,
% 3.95/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.95/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_5,plain,
% 3.95/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.95/0.99      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 3.95/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_679,plain,
% 3.95/0.99      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 3.95/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.95/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_1307,plain,
% 3.95/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 3.95/0.99      inference(superposition,[status(thm)],[c_668,c_679]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_15,negated_conjecture,
% 3.95/0.99      ( v4_pre_topc(sK1,sK0)
% 3.95/0.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.95/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_669,plain,
% 3.95/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.95/0.99      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 3.95/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_1497,plain,
% 3.95/0.99      ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.95/0.99      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 3.95/0.99      inference(demodulation,[status(thm)],[c_1307,c_669]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_9,plain,
% 3.95/0.99      ( ~ v4_pre_topc(X0,X1)
% 3.95/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.95/0.99      | ~ l1_pre_topc(X1)
% 3.95/0.99      | k2_pre_topc(X1,X0) = X0 ),
% 3.95/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_675,plain,
% 3.95/0.99      ( k2_pre_topc(X0,X1) = X1
% 3.95/0.99      | v4_pre_topc(X1,X0) != iProver_top
% 3.95/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.95/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.95/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_2364,plain,
% 3.95/0.99      ( k2_pre_topc(sK0,sK1) = sK1
% 3.95/0.99      | v4_pre_topc(sK1,sK0) != iProver_top
% 3.95/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.95/0.99      inference(superposition,[status(thm)],[c_668,c_675]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_17,negated_conjecture,
% 3.95/0.99      ( l1_pre_topc(sK0) ),
% 3.95/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_20,plain,
% 3.95/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 3.95/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_2537,plain,
% 3.95/0.99      ( v4_pre_topc(sK1,sK0) != iProver_top
% 3.95/0.99      | k2_pre_topc(sK0,sK1) = sK1 ),
% 3.95/0.99      inference(global_propositional_subsumption,
% 3.95/0.99                [status(thm)],
% 3.95/0.99                [c_2364,c_20]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_2538,plain,
% 3.95/0.99      ( k2_pre_topc(sK0,sK1) = sK1
% 3.95/0.99      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.95/0.99      inference(renaming,[status(thm)],[c_2537]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_2543,plain,
% 3.95/0.99      ( k2_pre_topc(sK0,sK1) = sK1
% 3.95/0.99      | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.95/0.99      inference(superposition,[status(thm)],[c_1497,c_2538]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_0,plain,
% 3.95/0.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 3.95/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_683,plain,
% 3.95/0.99      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 3.95/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_7,plain,
% 3.95/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.95/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_677,plain,
% 3.95/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.95/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.95/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_6,plain,
% 3.95/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.95/0.99      | k4_subset_1(X1,X0,k2_subset_1(X1)) = k2_subset_1(X1) ),
% 3.95/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_678,plain,
% 3.95/0.99      ( k4_subset_1(X0,X1,k2_subset_1(X0)) = k2_subset_1(X0)
% 3.95/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.95/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_2,plain,
% 3.95/0.99      ( k2_subset_1(X0) = X0 ),
% 3.95/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_701,plain,
% 3.95/0.99      ( k4_subset_1(X0,X1,X0) = X0
% 3.95/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 3.95/0.99      inference(light_normalisation,[status(thm)],[c_678,c_2]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_1288,plain,
% 3.95/0.99      ( k4_subset_1(X0,X1,X0) = X0 | r1_tarski(X1,X0) != iProver_top ),
% 3.95/0.99      inference(superposition,[status(thm)],[c_677,c_701]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_1898,plain,
% 3.95/0.99      ( k4_subset_1(X0,k4_xboole_0(X0,X1),X0) = X0 ),
% 3.95/0.99      inference(superposition,[status(thm)],[c_683,c_1288]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_3719,plain,
% 3.95/0.99      ( k4_subset_1(sK1,k2_tops_1(sK0,sK1),sK1) = sK1
% 3.95/0.99      | k2_pre_topc(sK0,sK1) = sK1 ),
% 3.95/0.99      inference(superposition,[status(thm)],[c_2543,c_1898]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_3720,plain,
% 3.95/0.99      ( k2_pre_topc(sK0,sK1) = sK1
% 3.95/0.99      | r1_tarski(k2_tops_1(sK0,sK1),sK1) = iProver_top ),
% 3.95/0.99      inference(superposition,[status(thm)],[c_2543,c_683]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_3,plain,
% 3.95/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 3.95/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_681,plain,
% 3.95/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.95/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_692,plain,
% 3.95/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.95/0.99      inference(light_normalisation,[status(thm)],[c_681,c_2]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_4,plain,
% 3.95/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.95/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.95/0.99      | k3_tarski(k1_enumset1(X2,X2,X0)) = k4_subset_1(X1,X2,X0) ),
% 3.95/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_680,plain,
% 3.95/0.99      ( k3_tarski(k1_enumset1(X0,X0,X1)) = k4_subset_1(X2,X0,X1)
% 3.95/0.99      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top
% 3.95/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 3.95/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_2117,plain,
% 3.95/0.99      ( k3_tarski(k1_enumset1(X0,X0,X1)) = k4_subset_1(X1,X0,X1)
% 3.95/0.99      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 3.95/0.99      inference(superposition,[status(thm)],[c_692,c_680]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_4902,plain,
% 3.95/0.99      ( k3_tarski(k1_enumset1(X0,X0,X1)) = k4_subset_1(X1,X0,X1)
% 3.95/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.95/0.99      inference(superposition,[status(thm)],[c_677,c_2117]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_5145,plain,
% 3.95/0.99      ( k2_pre_topc(sK0,sK1) = sK1
% 3.95/0.99      | k3_tarski(k1_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) = k4_subset_1(sK1,k2_tops_1(sK0,sK1),sK1) ),
% 3.95/0.99      inference(superposition,[status(thm)],[c_3720,c_4902]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_10,plain,
% 3.95/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.95/0.99      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.95/0.99      | ~ l1_pre_topc(X1) ),
% 3.95/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_674,plain,
% 3.95/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.95/0.99      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.95/0.99      | l1_pre_topc(X1) != iProver_top ),
% 3.95/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_2116,plain,
% 3.95/0.99      ( k3_tarski(k1_enumset1(X0,X0,sK1)) = k4_subset_1(u1_struct_0(sK0),X0,sK1)
% 3.95/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.95/0.99      inference(superposition,[status(thm)],[c_668,c_680]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_2756,plain,
% 3.95/0.99      ( k3_tarski(k1_enumset1(k2_tops_1(sK0,X0),k2_tops_1(sK0,X0),sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),sK1)
% 3.95/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.95/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.95/0.99      inference(superposition,[status(thm)],[c_674,c_2116]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_3573,plain,
% 3.95/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.95/0.99      | k3_tarski(k1_enumset1(k2_tops_1(sK0,X0),k2_tops_1(sK0,X0),sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),sK1) ),
% 3.95/0.99      inference(global_propositional_subsumption,
% 3.95/0.99                [status(thm)],
% 3.95/0.99                [c_2756,c_20]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_3574,plain,
% 3.95/0.99      ( k3_tarski(k1_enumset1(k2_tops_1(sK0,X0),k2_tops_1(sK0,X0),sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),sK1)
% 3.95/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.95/0.99      inference(renaming,[status(thm)],[c_3573]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_3583,plain,
% 3.95/0.99      ( k3_tarski(k1_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) ),
% 3.95/0.99      inference(superposition,[status(thm)],[c_668,c_3574]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_1,plain,
% 3.95/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.95/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.95/0.99      | k4_subset_1(X1,X0,X2) = k4_subset_1(X1,X2,X0) ),
% 3.95/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_682,plain,
% 3.95/0.99      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
% 3.95/0.99      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 3.95/0.99      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 3.95/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_2076,plain,
% 3.95/0.99      ( k4_subset_1(u1_struct_0(sK0),X0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,X0)
% 3.95/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.95/0.99      inference(superposition,[status(thm)],[c_668,c_682]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_2633,plain,
% 3.95/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),sK1)
% 3.95/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.95/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.95/0.99      inference(superposition,[status(thm)],[c_674,c_2076]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_3450,plain,
% 3.95/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.95/0.99      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),sK1) ),
% 3.95/0.99      inference(global_propositional_subsumption,
% 3.95/0.99                [status(thm)],
% 3.95/0.99                [c_2633,c_20]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_3451,plain,
% 3.95/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,X0),sK1)
% 3.95/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.95/0.99      inference(renaming,[status(thm)],[c_3450]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_3460,plain,
% 3.95/0.99      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
% 3.95/0.99      inference(superposition,[status(thm)],[c_668,c_3451]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_13,plain,
% 3.95/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.95/0.99      | ~ l1_pre_topc(X1)
% 3.95/0.99      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 3.95/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_671,plain,
% 3.95/0.99      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 3.95/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.95/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.95/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_1142,plain,
% 3.95/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 3.95/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.95/0.99      inference(superposition,[status(thm)],[c_668,c_671]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_911,plain,
% 3.95/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.95/0.99      | ~ l1_pre_topc(sK0)
% 3.95/0.99      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 3.95/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_1510,plain,
% 3.95/0.99      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 3.95/0.99      inference(global_propositional_subsumption,
% 3.95/0.99                [status(thm)],
% 3.95/0.99                [c_1142,c_17,c_16,c_911]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_3465,plain,
% 3.95/0.99      ( k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),sK1) = k2_pre_topc(sK0,sK1) ),
% 3.95/0.99      inference(light_normalisation,[status(thm)],[c_3460,c_1510]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_3588,plain,
% 3.95/0.99      ( k3_tarski(k1_enumset1(k2_tops_1(sK0,sK1),k2_tops_1(sK0,sK1),sK1)) = k2_pre_topc(sK0,sK1) ),
% 3.95/0.99      inference(light_normalisation,[status(thm)],[c_3583,c_3465]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_5148,plain,
% 3.95/0.99      ( k4_subset_1(sK1,k2_tops_1(sK0,sK1),sK1) = k2_pre_topc(sK0,sK1)
% 3.95/0.99      | k2_pre_topc(sK0,sK1) = sK1 ),
% 3.95/0.99      inference(light_normalisation,[status(thm)],[c_5145,c_3588]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_5667,plain,
% 3.95/0.99      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 3.95/0.99      inference(superposition,[status(thm)],[c_3719,c_5148]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_12,plain,
% 3.95/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.95/0.99      | ~ l1_pre_topc(X1)
% 3.95/0.99      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 3.95/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_672,plain,
% 3.95/0.99      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 3.95/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.95/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.95/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_1906,plain,
% 3.95/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 3.95/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.95/0.99      inference(superposition,[status(thm)],[c_668,c_672]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_950,plain,
% 3.95/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.95/0.99      | ~ l1_pre_topc(sK0)
% 3.95/0.99      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.95/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_2545,plain,
% 3.95/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.95/0.99      inference(global_propositional_subsumption,
% 3.95/0.99                [status(thm)],
% 3.95/0.99                [c_1906,c_17,c_16,c_950]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_5732,plain,
% 3.95/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 3.95/0.99      inference(demodulation,[status(thm)],[c_5667,c_2545]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_8,plain,
% 3.95/0.99      ( v4_pre_topc(X0,X1)
% 3.95/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.95/0.99      | ~ l1_pre_topc(X1)
% 3.95/0.99      | ~ v2_pre_topc(X1)
% 3.95/0.99      | k2_pre_topc(X1,X0) != X0 ),
% 3.95/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_905,plain,
% 3.95/0.99      ( v4_pre_topc(sK1,sK0)
% 3.95/0.99      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.95/0.99      | ~ l1_pre_topc(sK0)
% 3.95/0.99      | ~ v2_pre_topc(sK0)
% 3.95/0.99      | k2_pre_topc(sK0,sK1) != sK1 ),
% 3.95/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_14,negated_conjecture,
% 3.95/0.99      ( ~ v4_pre_topc(sK1,sK0)
% 3.95/0.99      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 3.95/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(c_18,negated_conjecture,
% 3.95/0.99      ( v2_pre_topc(sK0) ),
% 3.95/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.95/0.99  
% 3.95/0.99  cnf(contradiction,plain,
% 3.95/0.99      ( $false ),
% 3.95/0.99      inference(minisat,
% 3.95/0.99                [status(thm)],
% 3.95/0.99                [c_5732,c_5667,c_905,c_14,c_16,c_17,c_18]) ).
% 3.95/0.99  
% 3.95/0.99  
% 3.95/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.95/0.99  
% 3.95/0.99  ------                               Statistics
% 3.95/0.99  
% 3.95/0.99  ------ Selected
% 3.95/0.99  
% 3.95/0.99  total_time:                             0.216
% 3.95/0.99  
%------------------------------------------------------------------------------
