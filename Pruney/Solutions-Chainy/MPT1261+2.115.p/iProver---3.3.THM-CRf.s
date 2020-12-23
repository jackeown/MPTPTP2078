%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:40 EST 2020

% Result     : Theorem 15.91s
% Output     : CNFRefutation 15.91s
% Verified   : 
% Statistics : Number of formulae       :  153 (1506 expanded)
%              Number of clauses        :   90 ( 461 expanded)
%              Number of leaves         :   18 ( 344 expanded)
%              Depth                    :   26
%              Number of atoms          :  369 (5005 expanded)
%              Number of equality atoms :  183 (1846 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f42,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f41,f40])).

fof(f64,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f13,axiom,(
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

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f63,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f52,f44])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f45,f44])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f12])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f46,f44])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f47,f44,f44])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f49,f44])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f65,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f61,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_18,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_151,plain,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_18])).

cnf(c_12,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_354,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_355,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_401,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,X0) = X0
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_151,c_355])).

cnf(c_402,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_401])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_404,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_402,c_19])).

cnf(c_499,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_404])).

cnf(c_500,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(renaming,[status(thm)],[c_499])).

cnf(c_901,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_903,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4646,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_901,c_903])).

cnf(c_4853,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_500,c_4646])).

cnf(c_2,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_261,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 != X2
    | k5_xboole_0(X2,k3_xboole_0(X2,X3)) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_10])).

cnf(c_262,plain,
    ( m1_subset_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k1_zfmisc_1(X0)) ),
    inference(unflattening,[status(thm)],[c_261])).

cnf(c_900,plain,
    ( m1_subset_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_262])).

cnf(c_4647,plain,
    ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)) = k7_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) ),
    inference(superposition,[status(thm)],[c_900,c_903])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_22572,plain,
    ( k2_xboole_0(X0,k7_subset_1(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)),X0)) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
    inference(superposition,[status(thm)],[c_4647,c_3])).

cnf(c_22705,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1)))) = k2_xboole_0(X0,k7_subset_1(sK1,k2_tops_1(sK0,sK1),X0)) ),
    inference(superposition,[status(thm)],[c_4853,c_22572])).

cnf(c_43613,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))),X0) = k2_xboole_0(X0,k7_subset_1(sK1,k2_tops_1(sK0,sK1),X0)) ),
    inference(superposition,[status(thm)],[c_22705,c_1])).

cnf(c_43623,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(X0,k7_subset_1(sK1,k2_tops_1(sK0,sK1),X0)) = k2_xboole_0(k2_tops_1(sK0,sK1),X0) ),
    inference(superposition,[status(thm)],[c_4853,c_43613])).

cnf(c_44875,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))),X0) = k2_xboole_0(k2_tops_1(sK0,sK1),X0) ),
    inference(superposition,[status(thm)],[c_43623,c_43613])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_906,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3659,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_900,c_906])).

cnf(c_3671,plain,
    ( k3_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_3659,c_0])).

cnf(c_3818,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_subset_1(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_3671])).

cnf(c_11215,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_subset_1(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_4853,c_3818])).

cnf(c_3962,plain,
    ( k5_xboole_0(X0,k3_subset_1(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_3818,c_0])).

cnf(c_16347,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k3_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_11215,c_3962])).

cnf(c_22708,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(X0,k7_subset_1(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1)),X0)) = k2_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1)))) ),
    inference(superposition,[status(thm)],[c_16347,c_22572])).

cnf(c_3650,plain,
    ( m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_900])).

cnf(c_4651,plain,
    ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k7_subset_1(X0,k3_xboole_0(X0,X1),X2) ),
    inference(superposition,[status(thm)],[c_3650,c_903])).

cnf(c_9821,plain,
    ( k2_xboole_0(X0,k7_subset_1(X1,k3_xboole_0(X1,X2),X0)) = k2_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(superposition,[status(thm)],[c_4651,c_3])).

cnf(c_22724,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1)))) = k2_xboole_0(X0,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) ),
    inference(demodulation,[status(thm)],[c_22708,c_9821])).

cnf(c_46506,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))),k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k2_xboole_0(k2_tops_1(sK0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1)))) ),
    inference(superposition,[status(thm)],[c_44875,c_22724])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_904,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5520,plain,
    ( k4_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_900,c_904])).

cnf(c_38267,plain,
    ( k4_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X2)) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_3650,c_5520])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,k3_subset_1(X1,X0)) = k2_subset_1(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_902,plain,
    ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_907,plain,
    ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_902,c_4])).

cnf(c_3660,plain,
    ( k4_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
    inference(superposition,[status(thm)],[c_900,c_907])).

cnf(c_3672,plain,
    ( k4_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = X0 ),
    inference(demodulation,[status(thm)],[c_3671,c_3660])).

cnf(c_39265,plain,
    ( k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_38267,c_3672])).

cnf(c_46510,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_46506,c_3,c_39265])).

cnf(c_46519,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_1,c_46510])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_342,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_343,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_897,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_343])).

cnf(c_5519,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_901,c_904])).

cnf(c_5570,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_897,c_5519])).

cnf(c_6449,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_901,c_5570])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_318,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_20])).

cnf(c_319,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_318])).

cnf(c_899,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_319])).

cnf(c_1057,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_901,c_899])).

cnf(c_6456,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_6449,c_1057])).

cnf(c_46523,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_46519,c_6456])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_330,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_331,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_330])).

cnf(c_898,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_331])).

cnf(c_1111,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_901,c_898])).

cnf(c_47496,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_46523,c_1111])).

cnf(c_17,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_149,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_17])).

cnf(c_11,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_290,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_291,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_290])).

cnf(c_295,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(X0,sK0)
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_291,c_20])).

cnf(c_296,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(renaming,[status(thm)],[c_295])).

cnf(c_412,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,X0) != X0
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_149,c_296])).

cnf(c_413,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(unflattening,[status(thm)],[c_412])).

cnf(c_415,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_413,c_19])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_47496,c_46523,c_415])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:56:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.91/2.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.91/2.49  
% 15.91/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.91/2.49  
% 15.91/2.49  ------  iProver source info
% 15.91/2.49  
% 15.91/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.91/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.91/2.49  git: non_committed_changes: false
% 15.91/2.49  git: last_make_outside_of_git: false
% 15.91/2.49  
% 15.91/2.49  ------ 
% 15.91/2.49  
% 15.91/2.49  ------ Input Options
% 15.91/2.49  
% 15.91/2.49  --out_options                           all
% 15.91/2.49  --tptp_safe_out                         true
% 15.91/2.49  --problem_path                          ""
% 15.91/2.49  --include_path                          ""
% 15.91/2.49  --clausifier                            res/vclausify_rel
% 15.91/2.49  --clausifier_options                    ""
% 15.91/2.49  --stdin                                 false
% 15.91/2.49  --stats_out                             all
% 15.91/2.49  
% 15.91/2.49  ------ General Options
% 15.91/2.49  
% 15.91/2.49  --fof                                   false
% 15.91/2.49  --time_out_real                         305.
% 15.91/2.49  --time_out_virtual                      -1.
% 15.91/2.49  --symbol_type_check                     false
% 15.91/2.49  --clausify_out                          false
% 15.91/2.49  --sig_cnt_out                           false
% 15.91/2.49  --trig_cnt_out                          false
% 15.91/2.49  --trig_cnt_out_tolerance                1.
% 15.91/2.49  --trig_cnt_out_sk_spl                   false
% 15.91/2.49  --abstr_cl_out                          false
% 15.91/2.49  
% 15.91/2.49  ------ Global Options
% 15.91/2.49  
% 15.91/2.49  --schedule                              default
% 15.91/2.49  --add_important_lit                     false
% 15.91/2.49  --prop_solver_per_cl                    1000
% 15.91/2.49  --min_unsat_core                        false
% 15.91/2.49  --soft_assumptions                      false
% 15.91/2.49  --soft_lemma_size                       3
% 15.91/2.49  --prop_impl_unit_size                   0
% 15.91/2.49  --prop_impl_unit                        []
% 15.91/2.49  --share_sel_clauses                     true
% 15.91/2.49  --reset_solvers                         false
% 15.91/2.49  --bc_imp_inh                            [conj_cone]
% 15.91/2.49  --conj_cone_tolerance                   3.
% 15.91/2.49  --extra_neg_conj                        none
% 15.91/2.49  --large_theory_mode                     true
% 15.91/2.49  --prolific_symb_bound                   200
% 15.91/2.49  --lt_threshold                          2000
% 15.91/2.49  --clause_weak_htbl                      true
% 15.91/2.49  --gc_record_bc_elim                     false
% 15.91/2.49  
% 15.91/2.49  ------ Preprocessing Options
% 15.91/2.50  
% 15.91/2.50  --preprocessing_flag                    true
% 15.91/2.50  --time_out_prep_mult                    0.1
% 15.91/2.50  --splitting_mode                        input
% 15.91/2.50  --splitting_grd                         true
% 15.91/2.50  --splitting_cvd                         false
% 15.91/2.50  --splitting_cvd_svl                     false
% 15.91/2.50  --splitting_nvd                         32
% 15.91/2.50  --sub_typing                            true
% 15.91/2.50  --prep_gs_sim                           true
% 15.91/2.50  --prep_unflatten                        true
% 15.91/2.50  --prep_res_sim                          true
% 15.91/2.50  --prep_upred                            true
% 15.91/2.50  --prep_sem_filter                       exhaustive
% 15.91/2.50  --prep_sem_filter_out                   false
% 15.91/2.50  --pred_elim                             true
% 15.91/2.50  --res_sim_input                         true
% 15.91/2.50  --eq_ax_congr_red                       true
% 15.91/2.50  --pure_diseq_elim                       true
% 15.91/2.50  --brand_transform                       false
% 15.91/2.50  --non_eq_to_eq                          false
% 15.91/2.50  --prep_def_merge                        true
% 15.91/2.50  --prep_def_merge_prop_impl              false
% 15.91/2.50  --prep_def_merge_mbd                    true
% 15.91/2.50  --prep_def_merge_tr_red                 false
% 15.91/2.50  --prep_def_merge_tr_cl                  false
% 15.91/2.50  --smt_preprocessing                     true
% 15.91/2.50  --smt_ac_axioms                         fast
% 15.91/2.50  --preprocessed_out                      false
% 15.91/2.50  --preprocessed_stats                    false
% 15.91/2.50  
% 15.91/2.50  ------ Abstraction refinement Options
% 15.91/2.50  
% 15.91/2.50  --abstr_ref                             []
% 15.91/2.50  --abstr_ref_prep                        false
% 15.91/2.50  --abstr_ref_until_sat                   false
% 15.91/2.50  --abstr_ref_sig_restrict                funpre
% 15.91/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 15.91/2.50  --abstr_ref_under                       []
% 15.91/2.50  
% 15.91/2.50  ------ SAT Options
% 15.91/2.50  
% 15.91/2.50  --sat_mode                              false
% 15.91/2.50  --sat_fm_restart_options                ""
% 15.91/2.50  --sat_gr_def                            false
% 15.91/2.50  --sat_epr_types                         true
% 15.91/2.50  --sat_non_cyclic_types                  false
% 15.91/2.50  --sat_finite_models                     false
% 15.91/2.50  --sat_fm_lemmas                         false
% 15.91/2.50  --sat_fm_prep                           false
% 15.91/2.50  --sat_fm_uc_incr                        true
% 15.91/2.50  --sat_out_model                         small
% 15.91/2.50  --sat_out_clauses                       false
% 15.91/2.50  
% 15.91/2.50  ------ QBF Options
% 15.91/2.50  
% 15.91/2.50  --qbf_mode                              false
% 15.91/2.50  --qbf_elim_univ                         false
% 15.91/2.50  --qbf_dom_inst                          none
% 15.91/2.50  --qbf_dom_pre_inst                      false
% 15.91/2.50  --qbf_sk_in                             false
% 15.91/2.50  --qbf_pred_elim                         true
% 15.91/2.50  --qbf_split                             512
% 15.91/2.50  
% 15.91/2.50  ------ BMC1 Options
% 15.91/2.50  
% 15.91/2.50  --bmc1_incremental                      false
% 15.91/2.50  --bmc1_axioms                           reachable_all
% 15.91/2.50  --bmc1_min_bound                        0
% 15.91/2.50  --bmc1_max_bound                        -1
% 15.91/2.50  --bmc1_max_bound_default                -1
% 15.91/2.50  --bmc1_symbol_reachability              true
% 15.91/2.50  --bmc1_property_lemmas                  false
% 15.91/2.50  --bmc1_k_induction                      false
% 15.91/2.50  --bmc1_non_equiv_states                 false
% 15.91/2.50  --bmc1_deadlock                         false
% 15.91/2.50  --bmc1_ucm                              false
% 15.91/2.50  --bmc1_add_unsat_core                   none
% 15.91/2.50  --bmc1_unsat_core_children              false
% 15.91/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 15.91/2.50  --bmc1_out_stat                         full
% 15.91/2.50  --bmc1_ground_init                      false
% 15.91/2.50  --bmc1_pre_inst_next_state              false
% 15.91/2.50  --bmc1_pre_inst_state                   false
% 15.91/2.50  --bmc1_pre_inst_reach_state             false
% 15.91/2.50  --bmc1_out_unsat_core                   false
% 15.91/2.50  --bmc1_aig_witness_out                  false
% 15.91/2.50  --bmc1_verbose                          false
% 15.91/2.50  --bmc1_dump_clauses_tptp                false
% 15.91/2.50  --bmc1_dump_unsat_core_tptp             false
% 15.91/2.50  --bmc1_dump_file                        -
% 15.91/2.50  --bmc1_ucm_expand_uc_limit              128
% 15.91/2.50  --bmc1_ucm_n_expand_iterations          6
% 15.91/2.50  --bmc1_ucm_extend_mode                  1
% 15.91/2.50  --bmc1_ucm_init_mode                    2
% 15.91/2.50  --bmc1_ucm_cone_mode                    none
% 15.91/2.50  --bmc1_ucm_reduced_relation_type        0
% 15.91/2.50  --bmc1_ucm_relax_model                  4
% 15.91/2.50  --bmc1_ucm_full_tr_after_sat            true
% 15.91/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 15.91/2.50  --bmc1_ucm_layered_model                none
% 15.91/2.50  --bmc1_ucm_max_lemma_size               10
% 15.91/2.50  
% 15.91/2.50  ------ AIG Options
% 15.91/2.50  
% 15.91/2.50  --aig_mode                              false
% 15.91/2.50  
% 15.91/2.50  ------ Instantiation Options
% 15.91/2.50  
% 15.91/2.50  --instantiation_flag                    true
% 15.91/2.50  --inst_sos_flag                         true
% 15.91/2.50  --inst_sos_phase                        true
% 15.91/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.91/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.91/2.50  --inst_lit_sel_side                     num_symb
% 15.91/2.50  --inst_solver_per_active                1400
% 15.91/2.50  --inst_solver_calls_frac                1.
% 15.91/2.50  --inst_passive_queue_type               priority_queues
% 15.91/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.91/2.50  --inst_passive_queues_freq              [25;2]
% 15.91/2.50  --inst_dismatching                      true
% 15.91/2.50  --inst_eager_unprocessed_to_passive     true
% 15.91/2.50  --inst_prop_sim_given                   true
% 15.91/2.50  --inst_prop_sim_new                     false
% 15.91/2.50  --inst_subs_new                         false
% 15.91/2.50  --inst_eq_res_simp                      false
% 15.91/2.50  --inst_subs_given                       false
% 15.91/2.50  --inst_orphan_elimination               true
% 15.91/2.50  --inst_learning_loop_flag               true
% 15.91/2.50  --inst_learning_start                   3000
% 15.91/2.50  --inst_learning_factor                  2
% 15.91/2.50  --inst_start_prop_sim_after_learn       3
% 15.91/2.50  --inst_sel_renew                        solver
% 15.91/2.50  --inst_lit_activity_flag                true
% 15.91/2.50  --inst_restr_to_given                   false
% 15.91/2.50  --inst_activity_threshold               500
% 15.91/2.50  --inst_out_proof                        true
% 15.91/2.50  
% 15.91/2.50  ------ Resolution Options
% 15.91/2.50  
% 15.91/2.50  --resolution_flag                       true
% 15.91/2.50  --res_lit_sel                           adaptive
% 15.91/2.50  --res_lit_sel_side                      none
% 15.91/2.50  --res_ordering                          kbo
% 15.91/2.50  --res_to_prop_solver                    active
% 15.91/2.50  --res_prop_simpl_new                    false
% 15.91/2.50  --res_prop_simpl_given                  true
% 15.91/2.50  --res_passive_queue_type                priority_queues
% 15.91/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.91/2.50  --res_passive_queues_freq               [15;5]
% 15.91/2.50  --res_forward_subs                      full
% 15.91/2.50  --res_backward_subs                     full
% 15.91/2.50  --res_forward_subs_resolution           true
% 15.91/2.50  --res_backward_subs_resolution          true
% 15.91/2.50  --res_orphan_elimination                true
% 15.91/2.50  --res_time_limit                        2.
% 15.91/2.50  --res_out_proof                         true
% 15.91/2.50  
% 15.91/2.50  ------ Superposition Options
% 15.91/2.50  
% 15.91/2.50  --superposition_flag                    true
% 15.91/2.50  --sup_passive_queue_type                priority_queues
% 15.91/2.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.91/2.50  --sup_passive_queues_freq               [8;1;4]
% 15.91/2.50  --demod_completeness_check              fast
% 15.91/2.50  --demod_use_ground                      true
% 15.91/2.50  --sup_to_prop_solver                    passive
% 15.91/2.50  --sup_prop_simpl_new                    true
% 15.91/2.50  --sup_prop_simpl_given                  true
% 15.91/2.50  --sup_fun_splitting                     true
% 15.91/2.50  --sup_smt_interval                      50000
% 15.91/2.50  
% 15.91/2.50  ------ Superposition Simplification Setup
% 15.91/2.50  
% 15.91/2.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.91/2.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.91/2.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.91/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.91/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 15.91/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.91/2.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.91/2.50  --sup_immed_triv                        [TrivRules]
% 15.91/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.91/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.91/2.50  --sup_immed_bw_main                     []
% 15.91/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.91/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 15.91/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.91/2.50  --sup_input_bw                          []
% 15.91/2.50  
% 15.91/2.50  ------ Combination Options
% 15.91/2.50  
% 15.91/2.50  --comb_res_mult                         3
% 15.91/2.50  --comb_sup_mult                         2
% 15.91/2.50  --comb_inst_mult                        10
% 15.91/2.50  
% 15.91/2.50  ------ Debug Options
% 15.91/2.50  
% 15.91/2.50  --dbg_backtrace                         false
% 15.91/2.50  --dbg_dump_prop_clauses                 false
% 15.91/2.50  --dbg_dump_prop_clauses_file            -
% 15.91/2.50  --dbg_out_stat                          false
% 15.91/2.50  ------ Parsing...
% 15.91/2.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.91/2.50  
% 15.91/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 15.91/2.50  
% 15.91/2.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.91/2.50  
% 15.91/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.91/2.50  ------ Proving...
% 15.91/2.50  ------ Problem Properties 
% 15.91/2.50  
% 15.91/2.50  
% 15.91/2.50  clauses                                 18
% 15.91/2.50  conjectures                             1
% 15.91/2.50  EPR                                     0
% 15.91/2.50  Horn                                    17
% 15.91/2.50  unary                                   6
% 15.91/2.50  binary                                  9
% 15.91/2.50  lits                                    33
% 15.91/2.50  lits eq                                 17
% 15.91/2.50  fd_pure                                 0
% 15.91/2.50  fd_pseudo                               0
% 15.91/2.50  fd_cond                                 0
% 15.91/2.50  fd_pseudo_cond                          0
% 15.91/2.50  AC symbols                              0
% 15.91/2.50  
% 15.91/2.50  ------ Schedule dynamic 5 is on 
% 15.91/2.50  
% 15.91/2.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.91/2.50  
% 15.91/2.50  
% 15.91/2.50  ------ 
% 15.91/2.50  Current options:
% 15.91/2.50  ------ 
% 15.91/2.50  
% 15.91/2.50  ------ Input Options
% 15.91/2.50  
% 15.91/2.50  --out_options                           all
% 15.91/2.50  --tptp_safe_out                         true
% 15.91/2.50  --problem_path                          ""
% 15.91/2.50  --include_path                          ""
% 15.91/2.50  --clausifier                            res/vclausify_rel
% 15.91/2.50  --clausifier_options                    ""
% 15.91/2.50  --stdin                                 false
% 15.91/2.50  --stats_out                             all
% 15.91/2.50  
% 15.91/2.50  ------ General Options
% 15.91/2.50  
% 15.91/2.50  --fof                                   false
% 15.91/2.50  --time_out_real                         305.
% 15.91/2.50  --time_out_virtual                      -1.
% 15.91/2.50  --symbol_type_check                     false
% 15.91/2.50  --clausify_out                          false
% 15.91/2.50  --sig_cnt_out                           false
% 15.91/2.50  --trig_cnt_out                          false
% 15.91/2.50  --trig_cnt_out_tolerance                1.
% 15.91/2.50  --trig_cnt_out_sk_spl                   false
% 15.91/2.50  --abstr_cl_out                          false
% 15.91/2.50  
% 15.91/2.50  ------ Global Options
% 15.91/2.50  
% 15.91/2.50  --schedule                              default
% 15.91/2.50  --add_important_lit                     false
% 15.91/2.50  --prop_solver_per_cl                    1000
% 15.91/2.50  --min_unsat_core                        false
% 15.91/2.50  --soft_assumptions                      false
% 15.91/2.50  --soft_lemma_size                       3
% 15.91/2.50  --prop_impl_unit_size                   0
% 15.91/2.50  --prop_impl_unit                        []
% 15.91/2.50  --share_sel_clauses                     true
% 15.91/2.50  --reset_solvers                         false
% 15.91/2.50  --bc_imp_inh                            [conj_cone]
% 15.91/2.50  --conj_cone_tolerance                   3.
% 15.91/2.50  --extra_neg_conj                        none
% 15.91/2.50  --large_theory_mode                     true
% 15.91/2.50  --prolific_symb_bound                   200
% 15.91/2.50  --lt_threshold                          2000
% 15.91/2.50  --clause_weak_htbl                      true
% 15.91/2.50  --gc_record_bc_elim                     false
% 15.91/2.50  
% 15.91/2.50  ------ Preprocessing Options
% 15.91/2.50  
% 15.91/2.50  --preprocessing_flag                    true
% 15.91/2.50  --time_out_prep_mult                    0.1
% 15.91/2.50  --splitting_mode                        input
% 15.91/2.50  --splitting_grd                         true
% 15.91/2.50  --splitting_cvd                         false
% 15.91/2.50  --splitting_cvd_svl                     false
% 15.91/2.50  --splitting_nvd                         32
% 15.91/2.50  --sub_typing                            true
% 15.91/2.50  --prep_gs_sim                           true
% 15.91/2.50  --prep_unflatten                        true
% 15.91/2.50  --prep_res_sim                          true
% 15.91/2.50  --prep_upred                            true
% 15.91/2.50  --prep_sem_filter                       exhaustive
% 15.91/2.50  --prep_sem_filter_out                   false
% 15.91/2.50  --pred_elim                             true
% 15.91/2.50  --res_sim_input                         true
% 15.91/2.50  --eq_ax_congr_red                       true
% 15.91/2.50  --pure_diseq_elim                       true
% 15.91/2.50  --brand_transform                       false
% 15.91/2.50  --non_eq_to_eq                          false
% 15.91/2.50  --prep_def_merge                        true
% 15.91/2.50  --prep_def_merge_prop_impl              false
% 15.91/2.50  --prep_def_merge_mbd                    true
% 15.91/2.50  --prep_def_merge_tr_red                 false
% 15.91/2.50  --prep_def_merge_tr_cl                  false
% 15.91/2.50  --smt_preprocessing                     true
% 15.91/2.50  --smt_ac_axioms                         fast
% 15.91/2.50  --preprocessed_out                      false
% 15.91/2.50  --preprocessed_stats                    false
% 15.91/2.50  
% 15.91/2.50  ------ Abstraction refinement Options
% 15.91/2.50  
% 15.91/2.50  --abstr_ref                             []
% 15.91/2.50  --abstr_ref_prep                        false
% 15.91/2.50  --abstr_ref_until_sat                   false
% 15.91/2.50  --abstr_ref_sig_restrict                funpre
% 15.91/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 15.91/2.50  --abstr_ref_under                       []
% 15.91/2.50  
% 15.91/2.50  ------ SAT Options
% 15.91/2.50  
% 15.91/2.50  --sat_mode                              false
% 15.91/2.50  --sat_fm_restart_options                ""
% 15.91/2.50  --sat_gr_def                            false
% 15.91/2.50  --sat_epr_types                         true
% 15.91/2.50  --sat_non_cyclic_types                  false
% 15.91/2.50  --sat_finite_models                     false
% 15.91/2.50  --sat_fm_lemmas                         false
% 15.91/2.50  --sat_fm_prep                           false
% 15.91/2.50  --sat_fm_uc_incr                        true
% 15.91/2.50  --sat_out_model                         small
% 15.91/2.50  --sat_out_clauses                       false
% 15.91/2.50  
% 15.91/2.50  ------ QBF Options
% 15.91/2.50  
% 15.91/2.50  --qbf_mode                              false
% 15.91/2.50  --qbf_elim_univ                         false
% 15.91/2.50  --qbf_dom_inst                          none
% 15.91/2.50  --qbf_dom_pre_inst                      false
% 15.91/2.50  --qbf_sk_in                             false
% 15.91/2.50  --qbf_pred_elim                         true
% 15.91/2.50  --qbf_split                             512
% 15.91/2.50  
% 15.91/2.50  ------ BMC1 Options
% 15.91/2.50  
% 15.91/2.50  --bmc1_incremental                      false
% 15.91/2.50  --bmc1_axioms                           reachable_all
% 15.91/2.50  --bmc1_min_bound                        0
% 15.91/2.50  --bmc1_max_bound                        -1
% 15.91/2.50  --bmc1_max_bound_default                -1
% 15.91/2.50  --bmc1_symbol_reachability              true
% 15.91/2.50  --bmc1_property_lemmas                  false
% 15.91/2.50  --bmc1_k_induction                      false
% 15.91/2.50  --bmc1_non_equiv_states                 false
% 15.91/2.50  --bmc1_deadlock                         false
% 15.91/2.50  --bmc1_ucm                              false
% 15.91/2.50  --bmc1_add_unsat_core                   none
% 15.91/2.50  --bmc1_unsat_core_children              false
% 15.91/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 15.91/2.50  --bmc1_out_stat                         full
% 15.91/2.50  --bmc1_ground_init                      false
% 15.91/2.50  --bmc1_pre_inst_next_state              false
% 15.91/2.50  --bmc1_pre_inst_state                   false
% 15.91/2.50  --bmc1_pre_inst_reach_state             false
% 15.91/2.50  --bmc1_out_unsat_core                   false
% 15.91/2.50  --bmc1_aig_witness_out                  false
% 15.91/2.50  --bmc1_verbose                          false
% 15.91/2.50  --bmc1_dump_clauses_tptp                false
% 15.91/2.50  --bmc1_dump_unsat_core_tptp             false
% 15.91/2.50  --bmc1_dump_file                        -
% 15.91/2.50  --bmc1_ucm_expand_uc_limit              128
% 15.91/2.50  --bmc1_ucm_n_expand_iterations          6
% 15.91/2.50  --bmc1_ucm_extend_mode                  1
% 15.91/2.50  --bmc1_ucm_init_mode                    2
% 15.91/2.50  --bmc1_ucm_cone_mode                    none
% 15.91/2.50  --bmc1_ucm_reduced_relation_type        0
% 15.91/2.50  --bmc1_ucm_relax_model                  4
% 15.91/2.50  --bmc1_ucm_full_tr_after_sat            true
% 15.91/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 15.91/2.50  --bmc1_ucm_layered_model                none
% 15.91/2.50  --bmc1_ucm_max_lemma_size               10
% 15.91/2.50  
% 15.91/2.50  ------ AIG Options
% 15.91/2.50  
% 15.91/2.50  --aig_mode                              false
% 15.91/2.50  
% 15.91/2.50  ------ Instantiation Options
% 15.91/2.50  
% 15.91/2.50  --instantiation_flag                    true
% 15.91/2.50  --inst_sos_flag                         true
% 15.91/2.50  --inst_sos_phase                        true
% 15.91/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.91/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.91/2.50  --inst_lit_sel_side                     none
% 15.91/2.50  --inst_solver_per_active                1400
% 15.91/2.50  --inst_solver_calls_frac                1.
% 15.91/2.50  --inst_passive_queue_type               priority_queues
% 15.91/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.91/2.50  --inst_passive_queues_freq              [25;2]
% 15.91/2.50  --inst_dismatching                      true
% 15.91/2.50  --inst_eager_unprocessed_to_passive     true
% 15.91/2.50  --inst_prop_sim_given                   true
% 15.91/2.50  --inst_prop_sim_new                     false
% 15.91/2.50  --inst_subs_new                         false
% 15.91/2.50  --inst_eq_res_simp                      false
% 15.91/2.50  --inst_subs_given                       false
% 15.91/2.50  --inst_orphan_elimination               true
% 15.91/2.50  --inst_learning_loop_flag               true
% 15.91/2.50  --inst_learning_start                   3000
% 15.91/2.50  --inst_learning_factor                  2
% 15.91/2.50  --inst_start_prop_sim_after_learn       3
% 15.91/2.50  --inst_sel_renew                        solver
% 15.91/2.50  --inst_lit_activity_flag                true
% 15.91/2.50  --inst_restr_to_given                   false
% 15.91/2.50  --inst_activity_threshold               500
% 15.91/2.50  --inst_out_proof                        true
% 15.91/2.50  
% 15.91/2.50  ------ Resolution Options
% 15.91/2.50  
% 15.91/2.50  --resolution_flag                       false
% 15.91/2.50  --res_lit_sel                           adaptive
% 15.91/2.50  --res_lit_sel_side                      none
% 15.91/2.50  --res_ordering                          kbo
% 15.91/2.50  --res_to_prop_solver                    active
% 15.91/2.50  --res_prop_simpl_new                    false
% 15.91/2.50  --res_prop_simpl_given                  true
% 15.91/2.50  --res_passive_queue_type                priority_queues
% 15.91/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.91/2.50  --res_passive_queues_freq               [15;5]
% 15.91/2.50  --res_forward_subs                      full
% 15.91/2.50  --res_backward_subs                     full
% 15.91/2.50  --res_forward_subs_resolution           true
% 15.91/2.50  --res_backward_subs_resolution          true
% 15.91/2.50  --res_orphan_elimination                true
% 15.91/2.50  --res_time_limit                        2.
% 15.91/2.50  --res_out_proof                         true
% 15.91/2.50  
% 15.91/2.50  ------ Superposition Options
% 15.91/2.50  
% 15.91/2.50  --superposition_flag                    true
% 15.91/2.50  --sup_passive_queue_type                priority_queues
% 15.91/2.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.91/2.50  --sup_passive_queues_freq               [8;1;4]
% 15.91/2.50  --demod_completeness_check              fast
% 15.91/2.50  --demod_use_ground                      true
% 15.91/2.50  --sup_to_prop_solver                    passive
% 15.91/2.50  --sup_prop_simpl_new                    true
% 15.91/2.50  --sup_prop_simpl_given                  true
% 15.91/2.50  --sup_fun_splitting                     true
% 15.91/2.50  --sup_smt_interval                      50000
% 15.91/2.50  
% 15.91/2.50  ------ Superposition Simplification Setup
% 15.91/2.50  
% 15.91/2.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.91/2.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.91/2.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.91/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.91/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 15.91/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.91/2.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.91/2.50  --sup_immed_triv                        [TrivRules]
% 15.91/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.91/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.91/2.50  --sup_immed_bw_main                     []
% 15.91/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.91/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 15.91/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.91/2.50  --sup_input_bw                          []
% 15.91/2.50  
% 15.91/2.50  ------ Combination Options
% 15.91/2.50  
% 15.91/2.50  --comb_res_mult                         3
% 15.91/2.50  --comb_sup_mult                         2
% 15.91/2.50  --comb_inst_mult                        10
% 15.91/2.50  
% 15.91/2.50  ------ Debug Options
% 15.91/2.50  
% 15.91/2.50  --dbg_backtrace                         false
% 15.91/2.50  --dbg_dump_prop_clauses                 false
% 15.91/2.50  --dbg_dump_prop_clauses_file            -
% 15.91/2.50  --dbg_out_stat                          false
% 15.91/2.50  
% 15.91/2.50  
% 15.91/2.50  
% 15.91/2.50  
% 15.91/2.50  ------ Proving...
% 15.91/2.50  
% 15.91/2.50  
% 15.91/2.50  % SZS status Theorem for theBenchmark.p
% 15.91/2.50  
% 15.91/2.50  % SZS output start CNFRefutation for theBenchmark.p
% 15.91/2.50  
% 15.91/2.50  fof(f1,axiom,(
% 15.91/2.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 15.91/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.91/2.50  
% 15.91/2.50  fof(f43,plain,(
% 15.91/2.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 15.91/2.50    inference(cnf_transformation,[],[f1])).
% 15.91/2.50  
% 15.91/2.50  fof(f18,conjecture,(
% 15.91/2.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 15.91/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.91/2.50  
% 15.91/2.50  fof(f19,negated_conjecture,(
% 15.91/2.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 15.91/2.50    inference(negated_conjecture,[],[f18])).
% 15.91/2.50  
% 15.91/2.50  fof(f36,plain,(
% 15.91/2.50    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 15.91/2.50    inference(ennf_transformation,[],[f19])).
% 15.91/2.50  
% 15.91/2.50  fof(f37,plain,(
% 15.91/2.50    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 15.91/2.50    inference(flattening,[],[f36])).
% 15.91/2.50  
% 15.91/2.50  fof(f38,plain,(
% 15.91/2.50    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 15.91/2.50    inference(nnf_transformation,[],[f37])).
% 15.91/2.50  
% 15.91/2.50  fof(f39,plain,(
% 15.91/2.50    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 15.91/2.50    inference(flattening,[],[f38])).
% 15.91/2.50  
% 15.91/2.50  fof(f41,plain,(
% 15.91/2.50    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 15.91/2.50    introduced(choice_axiom,[])).
% 15.91/2.50  
% 15.91/2.50  fof(f40,plain,(
% 15.91/2.50    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 15.91/2.50    introduced(choice_axiom,[])).
% 15.91/2.50  
% 15.91/2.50  fof(f42,plain,(
% 15.91/2.50    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 15.91/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f41,f40])).
% 15.91/2.50  
% 15.91/2.50  fof(f64,plain,(
% 15.91/2.50    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 15.91/2.50    inference(cnf_transformation,[],[f42])).
% 15.91/2.50  
% 15.91/2.50  fof(f13,axiom,(
% 15.91/2.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 15.91/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.91/2.50  
% 15.91/2.50  fof(f28,plain,(
% 15.91/2.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.91/2.50    inference(ennf_transformation,[],[f13])).
% 15.91/2.50  
% 15.91/2.50  fof(f29,plain,(
% 15.91/2.50    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.91/2.50    inference(flattening,[],[f28])).
% 15.91/2.50  
% 15.91/2.50  fof(f55,plain,(
% 15.91/2.50    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.91/2.50    inference(cnf_transformation,[],[f29])).
% 15.91/2.50  
% 15.91/2.50  fof(f62,plain,(
% 15.91/2.50    l1_pre_topc(sK0)),
% 15.91/2.50    inference(cnf_transformation,[],[f42])).
% 15.91/2.50  
% 15.91/2.50  fof(f63,plain,(
% 15.91/2.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 15.91/2.50    inference(cnf_transformation,[],[f42])).
% 15.91/2.50  
% 15.91/2.50  fof(f10,axiom,(
% 15.91/2.50    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 15.91/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.91/2.50  
% 15.91/2.50  fof(f25,plain,(
% 15.91/2.50    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.91/2.50    inference(ennf_transformation,[],[f10])).
% 15.91/2.50  
% 15.91/2.50  fof(f52,plain,(
% 15.91/2.50    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.91/2.50    inference(cnf_transformation,[],[f25])).
% 15.91/2.50  
% 15.91/2.50  fof(f2,axiom,(
% 15.91/2.50    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 15.91/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.91/2.50  
% 15.91/2.50  fof(f44,plain,(
% 15.91/2.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 15.91/2.50    inference(cnf_transformation,[],[f2])).
% 15.91/2.50  
% 15.91/2.50  fof(f70,plain,(
% 15.91/2.50    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.91/2.50    inference(definition_unfolding,[],[f52,f44])).
% 15.91/2.50  
% 15.91/2.50  fof(f3,axiom,(
% 15.91/2.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 15.91/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.91/2.50  
% 15.91/2.50  fof(f45,plain,(
% 15.91/2.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 15.91/2.50    inference(cnf_transformation,[],[f3])).
% 15.91/2.50  
% 15.91/2.50  fof(f67,plain,(
% 15.91/2.50    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 15.91/2.50    inference(definition_unfolding,[],[f45,f44])).
% 15.91/2.50  
% 15.91/2.50  fof(f12,axiom,(
% 15.91/2.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.91/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.91/2.50  
% 15.91/2.50  fof(f20,plain,(
% 15.91/2.50    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 15.91/2.50    inference(unused_predicate_definition_removal,[],[f12])).
% 15.91/2.50  
% 15.91/2.50  fof(f27,plain,(
% 15.91/2.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 15.91/2.50    inference(ennf_transformation,[],[f20])).
% 15.91/2.50  
% 15.91/2.50  fof(f54,plain,(
% 15.91/2.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 15.91/2.50    inference(cnf_transformation,[],[f27])).
% 15.91/2.50  
% 15.91/2.50  fof(f4,axiom,(
% 15.91/2.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 15.91/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.91/2.50  
% 15.91/2.50  fof(f46,plain,(
% 15.91/2.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 15.91/2.50    inference(cnf_transformation,[],[f4])).
% 15.91/2.50  
% 15.91/2.50  fof(f68,plain,(
% 15.91/2.50    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 15.91/2.50    inference(definition_unfolding,[],[f46,f44])).
% 15.91/2.50  
% 15.91/2.50  fof(f5,axiom,(
% 15.91/2.50    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 15.91/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.91/2.50  
% 15.91/2.50  fof(f47,plain,(
% 15.91/2.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 15.91/2.50    inference(cnf_transformation,[],[f5])).
% 15.91/2.50  
% 15.91/2.50  fof(f66,plain,(
% 15.91/2.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 15.91/2.50    inference(definition_unfolding,[],[f47,f44,f44])).
% 15.91/2.50  
% 15.91/2.50  fof(f7,axiom,(
% 15.91/2.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 15.91/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.91/2.50  
% 15.91/2.50  fof(f21,plain,(
% 15.91/2.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.91/2.50    inference(ennf_transformation,[],[f7])).
% 15.91/2.50  
% 15.91/2.50  fof(f49,plain,(
% 15.91/2.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.91/2.50    inference(cnf_transformation,[],[f21])).
% 15.91/2.50  
% 15.91/2.50  fof(f69,plain,(
% 15.91/2.50    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.91/2.50    inference(definition_unfolding,[],[f49,f44])).
% 15.91/2.50  
% 15.91/2.50  fof(f9,axiom,(
% 15.91/2.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 15.91/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.91/2.50  
% 15.91/2.50  fof(f23,plain,(
% 15.91/2.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 15.91/2.50    inference(ennf_transformation,[],[f9])).
% 15.91/2.50  
% 15.91/2.50  fof(f24,plain,(
% 15.91/2.50    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.91/2.50    inference(flattening,[],[f23])).
% 15.91/2.50  
% 15.91/2.50  fof(f51,plain,(
% 15.91/2.50    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.91/2.50    inference(cnf_transformation,[],[f24])).
% 15.91/2.50  
% 15.91/2.50  fof(f11,axiom,(
% 15.91/2.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 15.91/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.91/2.50  
% 15.91/2.50  fof(f26,plain,(
% 15.91/2.50    ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 15.91/2.50    inference(ennf_transformation,[],[f11])).
% 15.91/2.50  
% 15.91/2.50  fof(f53,plain,(
% 15.91/2.50    ( ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 15.91/2.50    inference(cnf_transformation,[],[f26])).
% 15.91/2.50  
% 15.91/2.50  fof(f6,axiom,(
% 15.91/2.50    ! [X0] : k2_subset_1(X0) = X0),
% 15.91/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.91/2.50  
% 15.91/2.50  fof(f48,plain,(
% 15.91/2.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 15.91/2.50    inference(cnf_transformation,[],[f6])).
% 15.91/2.50  
% 15.91/2.50  fof(f14,axiom,(
% 15.91/2.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 15.91/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.91/2.50  
% 15.91/2.50  fof(f30,plain,(
% 15.91/2.50    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 15.91/2.50    inference(ennf_transformation,[],[f14])).
% 15.91/2.50  
% 15.91/2.50  fof(f31,plain,(
% 15.91/2.50    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 15.91/2.50    inference(flattening,[],[f30])).
% 15.91/2.50  
% 15.91/2.50  fof(f57,plain,(
% 15.91/2.50    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.91/2.50    inference(cnf_transformation,[],[f31])).
% 15.91/2.50  
% 15.91/2.50  fof(f17,axiom,(
% 15.91/2.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 15.91/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.91/2.50  
% 15.91/2.50  fof(f35,plain,(
% 15.91/2.50    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.91/2.50    inference(ennf_transformation,[],[f17])).
% 15.91/2.50  
% 15.91/2.50  fof(f60,plain,(
% 15.91/2.50    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.91/2.50    inference(cnf_transformation,[],[f35])).
% 15.91/2.50  
% 15.91/2.50  fof(f16,axiom,(
% 15.91/2.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 15.91/2.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.91/2.50  
% 15.91/2.50  fof(f34,plain,(
% 15.91/2.50    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 15.91/2.50    inference(ennf_transformation,[],[f16])).
% 15.91/2.50  
% 15.91/2.50  fof(f59,plain,(
% 15.91/2.50    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.91/2.50    inference(cnf_transformation,[],[f34])).
% 15.91/2.50  
% 15.91/2.50  fof(f65,plain,(
% 15.91/2.50    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 15.91/2.50    inference(cnf_transformation,[],[f42])).
% 15.91/2.50  
% 15.91/2.50  fof(f56,plain,(
% 15.91/2.50    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 15.91/2.50    inference(cnf_transformation,[],[f29])).
% 15.91/2.50  
% 15.91/2.50  fof(f61,plain,(
% 15.91/2.50    v2_pre_topc(sK0)),
% 15.91/2.50    inference(cnf_transformation,[],[f42])).
% 15.91/2.50  
% 15.91/2.50  cnf(c_1,plain,
% 15.91/2.50      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 15.91/2.50      inference(cnf_transformation,[],[f43]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_18,negated_conjecture,
% 15.91/2.50      ( v4_pre_topc(sK1,sK0)
% 15.91/2.50      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 15.91/2.50      inference(cnf_transformation,[],[f64]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_151,plain,
% 15.91/2.50      ( v4_pre_topc(sK1,sK0)
% 15.91/2.50      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 15.91/2.50      inference(prop_impl,[status(thm)],[c_18]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_12,plain,
% 15.91/2.50      ( ~ v4_pre_topc(X0,X1)
% 15.91/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.91/2.50      | ~ l1_pre_topc(X1)
% 15.91/2.50      | k2_pre_topc(X1,X0) = X0 ),
% 15.91/2.50      inference(cnf_transformation,[],[f55]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_20,negated_conjecture,
% 15.91/2.50      ( l1_pre_topc(sK0) ),
% 15.91/2.50      inference(cnf_transformation,[],[f62]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_354,plain,
% 15.91/2.50      ( ~ v4_pre_topc(X0,X1)
% 15.91/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.91/2.50      | k2_pre_topc(X1,X0) = X0
% 15.91/2.50      | sK0 != X1 ),
% 15.91/2.50      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_355,plain,
% 15.91/2.50      ( ~ v4_pre_topc(X0,sK0)
% 15.91/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.91/2.50      | k2_pre_topc(sK0,X0) = X0 ),
% 15.91/2.50      inference(unflattening,[status(thm)],[c_354]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_401,plain,
% 15.91/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.91/2.50      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 15.91/2.50      | k2_pre_topc(sK0,X0) = X0
% 15.91/2.50      | sK1 != X0
% 15.91/2.50      | sK0 != sK0 ),
% 15.91/2.50      inference(resolution_lifted,[status(thm)],[c_151,c_355]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_402,plain,
% 15.91/2.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.91/2.50      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 15.91/2.50      | k2_pre_topc(sK0,sK1) = sK1 ),
% 15.91/2.50      inference(unflattening,[status(thm)],[c_401]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_19,negated_conjecture,
% 15.91/2.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.91/2.50      inference(cnf_transformation,[],[f63]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_404,plain,
% 15.91/2.50      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 15.91/2.50      | k2_pre_topc(sK0,sK1) = sK1 ),
% 15.91/2.50      inference(global_propositional_subsumption,
% 15.91/2.50                [status(thm)],
% 15.91/2.50                [c_402,c_19]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_499,plain,
% 15.91/2.50      ( k2_pre_topc(sK0,sK1) = sK1
% 15.91/2.50      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 15.91/2.50      inference(prop_impl,[status(thm)],[c_404]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_500,plain,
% 15.91/2.50      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 15.91/2.50      | k2_pre_topc(sK0,sK1) = sK1 ),
% 15.91/2.50      inference(renaming,[status(thm)],[c_499]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_901,plain,
% 15.91/2.50      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.91/2.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_8,plain,
% 15.91/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.91/2.50      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 15.91/2.50      inference(cnf_transformation,[],[f70]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_903,plain,
% 15.91/2.50      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
% 15.91/2.50      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 15.91/2.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_4646,plain,
% 15.91/2.50      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
% 15.91/2.50      inference(superposition,[status(thm)],[c_901,c_903]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_4853,plain,
% 15.91/2.50      ( k2_pre_topc(sK0,sK1) = sK1
% 15.91/2.50      | k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
% 15.91/2.50      inference(superposition,[status(thm)],[c_500,c_4646]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_2,plain,
% 15.91/2.50      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 15.91/2.50      inference(cnf_transformation,[],[f67]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_10,plain,
% 15.91/2.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.91/2.50      inference(cnf_transformation,[],[f54]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_261,plain,
% 15.91/2.50      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.91/2.50      | X1 != X2
% 15.91/2.50      | k5_xboole_0(X2,k3_xboole_0(X2,X3)) != X0 ),
% 15.91/2.50      inference(resolution_lifted,[status(thm)],[c_2,c_10]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_262,plain,
% 15.91/2.50      ( m1_subset_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k1_zfmisc_1(X0)) ),
% 15.91/2.50      inference(unflattening,[status(thm)],[c_261]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_900,plain,
% 15.91/2.50      ( m1_subset_1(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k1_zfmisc_1(X0)) = iProver_top ),
% 15.91/2.50      inference(predicate_to_equality,[status(thm)],[c_262]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_4647,plain,
% 15.91/2.50      ( k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)) = k7_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) ),
% 15.91/2.50      inference(superposition,[status(thm)],[c_900,c_903]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_3,plain,
% 15.91/2.50      ( k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
% 15.91/2.50      inference(cnf_transformation,[],[f68]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_22572,plain,
% 15.91/2.50      ( k2_xboole_0(X0,k7_subset_1(X1,k5_xboole_0(X1,k3_xboole_0(X1,X2)),X0)) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) ),
% 15.91/2.50      inference(superposition,[status(thm)],[c_4647,c_3]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_22705,plain,
% 15.91/2.50      ( k2_pre_topc(sK0,sK1) = sK1
% 15.91/2.50      | k2_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1)))) = k2_xboole_0(X0,k7_subset_1(sK1,k2_tops_1(sK0,sK1),X0)) ),
% 15.91/2.50      inference(superposition,[status(thm)],[c_4853,c_22572]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_43613,plain,
% 15.91/2.50      ( k2_pre_topc(sK0,sK1) = sK1
% 15.91/2.50      | k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))),X0) = k2_xboole_0(X0,k7_subset_1(sK1,k2_tops_1(sK0,sK1),X0)) ),
% 15.91/2.50      inference(superposition,[status(thm)],[c_22705,c_1]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_43623,plain,
% 15.91/2.50      ( k2_pre_topc(sK0,sK1) = sK1
% 15.91/2.50      | k2_xboole_0(X0,k7_subset_1(sK1,k2_tops_1(sK0,sK1),X0)) = k2_xboole_0(k2_tops_1(sK0,sK1),X0) ),
% 15.91/2.50      inference(superposition,[status(thm)],[c_4853,c_43613]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_44875,plain,
% 15.91/2.50      ( k2_pre_topc(sK0,sK1) = sK1
% 15.91/2.50      | k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))),X0) = k2_xboole_0(k2_tops_1(sK0,sK1),X0) ),
% 15.91/2.50      inference(superposition,[status(thm)],[c_43623,c_43613]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_0,plain,
% 15.91/2.50      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 15.91/2.50      inference(cnf_transformation,[],[f66]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_5,plain,
% 15.91/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.91/2.50      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 15.91/2.50      inference(cnf_transformation,[],[f69]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_906,plain,
% 15.91/2.50      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 15.91/2.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 15.91/2.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_3659,plain,
% 15.91/2.50      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 15.91/2.50      inference(superposition,[status(thm)],[c_900,c_906]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_3671,plain,
% 15.91/2.50      ( k3_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,X1) ),
% 15.91/2.50      inference(light_normalisation,[status(thm)],[c_3659,c_0]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_3818,plain,
% 15.91/2.50      ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_subset_1(X0,k3_xboole_0(X0,X1)) ),
% 15.91/2.50      inference(superposition,[status(thm)],[c_0,c_3671]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_11215,plain,
% 15.91/2.50      ( k2_pre_topc(sK0,sK1) = sK1
% 15.91/2.50      | k3_subset_1(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 15.91/2.50      inference(superposition,[status(thm)],[c_4853,c_3818]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_3962,plain,
% 15.91/2.50      ( k5_xboole_0(X0,k3_subset_1(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,X1) ),
% 15.91/2.50      inference(demodulation,[status(thm)],[c_3818,c_0]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_16347,plain,
% 15.91/2.50      ( k2_pre_topc(sK0,sK1) = sK1
% 15.91/2.50      | k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k3_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
% 15.91/2.50      inference(superposition,[status(thm)],[c_11215,c_3962]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_22708,plain,
% 15.91/2.50      ( k2_pre_topc(sK0,sK1) = sK1
% 15.91/2.50      | k2_xboole_0(X0,k7_subset_1(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1)),X0)) = k2_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1)))) ),
% 15.91/2.50      inference(superposition,[status(thm)],[c_16347,c_22572]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_3650,plain,
% 15.91/2.50      ( m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0)) = iProver_top ),
% 15.91/2.50      inference(superposition,[status(thm)],[c_0,c_900]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_4651,plain,
% 15.91/2.50      ( k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) = k7_subset_1(X0,k3_xboole_0(X0,X1),X2) ),
% 15.91/2.50      inference(superposition,[status(thm)],[c_3650,c_903]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_9821,plain,
% 15.91/2.50      ( k2_xboole_0(X0,k7_subset_1(X1,k3_xboole_0(X1,X2),X0)) = k2_xboole_0(X0,k3_xboole_0(X1,X2)) ),
% 15.91/2.50      inference(superposition,[status(thm)],[c_4651,c_3]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_22724,plain,
% 15.91/2.50      ( k2_pre_topc(sK0,sK1) = sK1
% 15.91/2.50      | k2_xboole_0(X0,k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1)))) = k2_xboole_0(X0,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) ),
% 15.91/2.50      inference(demodulation,[status(thm)],[c_22708,c_9821]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_46506,plain,
% 15.91/2.50      ( k2_pre_topc(sK0,sK1) = sK1
% 15.91/2.50      | k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))),k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k2_xboole_0(k2_tops_1(sK0,sK1),k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1)))) ),
% 15.91/2.50      inference(superposition,[status(thm)],[c_44875,c_22724]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_7,plain,
% 15.91/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.91/2.50      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 15.91/2.50      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 15.91/2.50      inference(cnf_transformation,[],[f51]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_904,plain,
% 15.91/2.50      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 15.91/2.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 15.91/2.50      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 15.91/2.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_5520,plain,
% 15.91/2.50      ( k4_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X2)
% 15.91/2.50      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 15.91/2.50      inference(superposition,[status(thm)],[c_900,c_904]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_38267,plain,
% 15.91/2.50      ( k4_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X2)) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X2)) ),
% 15.91/2.50      inference(superposition,[status(thm)],[c_3650,c_5520]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_9,plain,
% 15.91/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.91/2.50      | k4_subset_1(X1,X0,k3_subset_1(X1,X0)) = k2_subset_1(X1) ),
% 15.91/2.50      inference(cnf_transformation,[],[f53]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_902,plain,
% 15.91/2.50      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0)
% 15.91/2.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 15.91/2.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_4,plain,
% 15.91/2.50      ( k2_subset_1(X0) = X0 ),
% 15.91/2.50      inference(cnf_transformation,[],[f48]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_907,plain,
% 15.91/2.50      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
% 15.91/2.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 15.91/2.50      inference(light_normalisation,[status(thm)],[c_902,c_4]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_3660,plain,
% 15.91/2.50      ( k4_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
% 15.91/2.50      inference(superposition,[status(thm)],[c_900,c_907]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_3672,plain,
% 15.91/2.50      ( k4_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = X0 ),
% 15.91/2.50      inference(demodulation,[status(thm)],[c_3671,c_3660]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_39265,plain,
% 15.91/2.50      ( k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = X0 ),
% 15.91/2.50      inference(superposition,[status(thm)],[c_38267,c_3672]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_46510,plain,
% 15.91/2.50      ( k2_pre_topc(sK0,sK1) = sK1
% 15.91/2.50      | k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = sK1 ),
% 15.91/2.50      inference(demodulation,[status(thm)],[c_46506,c_3,c_39265]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_46519,plain,
% 15.91/2.50      ( k2_pre_topc(sK0,sK1) = sK1
% 15.91/2.50      | k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
% 15.91/2.50      inference(superposition,[status(thm)],[c_1,c_46510]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_13,plain,
% 15.91/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.91/2.50      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 15.91/2.50      | ~ l1_pre_topc(X1) ),
% 15.91/2.50      inference(cnf_transformation,[],[f57]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_342,plain,
% 15.91/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.91/2.50      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 15.91/2.50      | sK0 != X1 ),
% 15.91/2.50      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_343,plain,
% 15.91/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.91/2.50      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 15.91/2.50      inference(unflattening,[status(thm)],[c_342]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_897,plain,
% 15.91/2.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 15.91/2.50      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 15.91/2.50      inference(predicate_to_equality,[status(thm)],[c_343]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_5519,plain,
% 15.91/2.50      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
% 15.91/2.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 15.91/2.50      inference(superposition,[status(thm)],[c_901,c_904]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_5570,plain,
% 15.91/2.50      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
% 15.91/2.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 15.91/2.50      inference(superposition,[status(thm)],[c_897,c_5519]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_6449,plain,
% 15.91/2.50      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 15.91/2.50      inference(superposition,[status(thm)],[c_901,c_5570]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_16,plain,
% 15.91/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.91/2.50      | ~ l1_pre_topc(X1)
% 15.91/2.50      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 15.91/2.50      inference(cnf_transformation,[],[f60]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_318,plain,
% 15.91/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.91/2.50      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
% 15.91/2.50      | sK0 != X1 ),
% 15.91/2.50      inference(resolution_lifted,[status(thm)],[c_16,c_20]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_319,plain,
% 15.91/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.91/2.50      | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 15.91/2.50      inference(unflattening,[status(thm)],[c_318]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_899,plain,
% 15.91/2.50      ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
% 15.91/2.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 15.91/2.50      inference(predicate_to_equality,[status(thm)],[c_319]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_1057,plain,
% 15.91/2.50      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 15.91/2.50      inference(superposition,[status(thm)],[c_901,c_899]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_6456,plain,
% 15.91/2.50      ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 15.91/2.50      inference(light_normalisation,[status(thm)],[c_6449,c_1057]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_46523,plain,
% 15.91/2.50      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 15.91/2.50      inference(demodulation,[status(thm)],[c_46519,c_6456]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_15,plain,
% 15.91/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.91/2.50      | ~ l1_pre_topc(X1)
% 15.91/2.50      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 15.91/2.50      inference(cnf_transformation,[],[f59]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_330,plain,
% 15.91/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.91/2.50      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 15.91/2.50      | sK0 != X1 ),
% 15.91/2.50      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_331,plain,
% 15.91/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.91/2.50      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 15.91/2.50      inference(unflattening,[status(thm)],[c_330]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_898,plain,
% 15.91/2.50      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 15.91/2.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 15.91/2.50      inference(predicate_to_equality,[status(thm)],[c_331]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_1111,plain,
% 15.91/2.50      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 15.91/2.50      inference(superposition,[status(thm)],[c_901,c_898]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_47496,plain,
% 15.91/2.50      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 15.91/2.50      inference(demodulation,[status(thm)],[c_46523,c_1111]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_17,negated_conjecture,
% 15.91/2.50      ( ~ v4_pre_topc(sK1,sK0)
% 15.91/2.50      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 15.91/2.50      inference(cnf_transformation,[],[f65]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_149,plain,
% 15.91/2.50      ( ~ v4_pre_topc(sK1,sK0)
% 15.91/2.50      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 15.91/2.50      inference(prop_impl,[status(thm)],[c_17]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_11,plain,
% 15.91/2.50      ( v4_pre_topc(X0,X1)
% 15.91/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.91/2.50      | ~ l1_pre_topc(X1)
% 15.91/2.50      | ~ v2_pre_topc(X1)
% 15.91/2.50      | k2_pre_topc(X1,X0) != X0 ),
% 15.91/2.50      inference(cnf_transformation,[],[f56]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_21,negated_conjecture,
% 15.91/2.50      ( v2_pre_topc(sK0) ),
% 15.91/2.50      inference(cnf_transformation,[],[f61]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_290,plain,
% 15.91/2.50      ( v4_pre_topc(X0,X1)
% 15.91/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 15.91/2.50      | ~ l1_pre_topc(X1)
% 15.91/2.50      | k2_pre_topc(X1,X0) != X0
% 15.91/2.50      | sK0 != X1 ),
% 15.91/2.50      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_291,plain,
% 15.91/2.50      ( v4_pre_topc(X0,sK0)
% 15.91/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.91/2.50      | ~ l1_pre_topc(sK0)
% 15.91/2.50      | k2_pre_topc(sK0,X0) != X0 ),
% 15.91/2.50      inference(unflattening,[status(thm)],[c_290]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_295,plain,
% 15.91/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.91/2.50      | v4_pre_topc(X0,sK0)
% 15.91/2.50      | k2_pre_topc(sK0,X0) != X0 ),
% 15.91/2.50      inference(global_propositional_subsumption,
% 15.91/2.50                [status(thm)],
% 15.91/2.50                [c_291,c_20]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_296,plain,
% 15.91/2.50      ( v4_pre_topc(X0,sK0)
% 15.91/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.91/2.50      | k2_pre_topc(sK0,X0) != X0 ),
% 15.91/2.50      inference(renaming,[status(thm)],[c_295]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_412,plain,
% 15.91/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.91/2.50      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 15.91/2.50      | k2_pre_topc(sK0,X0) != X0
% 15.91/2.50      | sK1 != X0
% 15.91/2.50      | sK0 != sK0 ),
% 15.91/2.50      inference(resolution_lifted,[status(thm)],[c_149,c_296]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_413,plain,
% 15.91/2.50      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 15.91/2.50      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 15.91/2.50      | k2_pre_topc(sK0,sK1) != sK1 ),
% 15.91/2.50      inference(unflattening,[status(thm)],[c_412]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(c_415,plain,
% 15.91/2.50      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 15.91/2.50      | k2_pre_topc(sK0,sK1) != sK1 ),
% 15.91/2.50      inference(global_propositional_subsumption,
% 15.91/2.50                [status(thm)],
% 15.91/2.50                [c_413,c_19]) ).
% 15.91/2.50  
% 15.91/2.50  cnf(contradiction,plain,
% 15.91/2.50      ( $false ),
% 15.91/2.50      inference(minisat,[status(thm)],[c_47496,c_46523,c_415]) ).
% 15.91/2.50  
% 15.91/2.50  
% 15.91/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.91/2.50  
% 15.91/2.50  ------                               Statistics
% 15.91/2.50  
% 15.91/2.50  ------ General
% 15.91/2.50  
% 15.91/2.50  abstr_ref_over_cycles:                  0
% 15.91/2.50  abstr_ref_under_cycles:                 0
% 15.91/2.50  gc_basic_clause_elim:                   0
% 15.91/2.50  forced_gc_time:                         0
% 15.91/2.50  parsing_time:                           0.008
% 15.91/2.50  unif_index_cands_time:                  0.
% 15.91/2.50  unif_index_add_time:                    0.
% 15.91/2.50  orderings_time:                         0.
% 15.91/2.50  out_proof_time:                         0.013
% 15.91/2.50  total_time:                             1.858
% 15.91/2.50  num_of_symbols:                         50
% 15.91/2.50  num_of_terms:                           65431
% 15.91/2.50  
% 15.91/2.50  ------ Preprocessing
% 15.91/2.50  
% 15.91/2.50  num_of_splits:                          0
% 15.91/2.50  num_of_split_atoms:                     0
% 15.91/2.50  num_of_reused_defs:                     0
% 15.91/2.50  num_eq_ax_congr_red:                    24
% 15.91/2.50  num_of_sem_filtered_clauses:            1
% 15.91/2.50  num_of_subtypes:                        0
% 15.91/2.50  monotx_restored_types:                  0
% 15.91/2.50  sat_num_of_epr_types:                   0
% 15.91/2.50  sat_num_of_non_cyclic_types:            0
% 15.91/2.50  sat_guarded_non_collapsed_types:        0
% 15.91/2.50  num_pure_diseq_elim:                    0
% 15.91/2.50  simp_replaced_by:                       0
% 15.91/2.50  res_preprocessed:                       103
% 15.91/2.50  prep_upred:                             0
% 15.91/2.50  prep_unflattend:                        11
% 15.91/2.50  smt_new_axioms:                         0
% 15.91/2.50  pred_elim_cands:                        1
% 15.91/2.50  pred_elim:                              4
% 15.91/2.50  pred_elim_cl:                           4
% 15.91/2.50  pred_elim_cycles:                       6
% 15.91/2.50  merged_defs:                            8
% 15.91/2.50  merged_defs_ncl:                        0
% 15.91/2.50  bin_hyper_res:                          9
% 15.91/2.50  prep_cycles:                            4
% 15.91/2.50  pred_elim_time:                         0.004
% 15.91/2.50  splitting_time:                         0.
% 15.91/2.50  sem_filter_time:                        0.
% 15.91/2.50  monotx_time:                            0.
% 15.91/2.50  subtype_inf_time:                       0.
% 15.91/2.50  
% 15.91/2.50  ------ Problem properties
% 15.91/2.50  
% 15.91/2.50  clauses:                                18
% 15.91/2.50  conjectures:                            1
% 15.91/2.50  epr:                                    0
% 15.91/2.50  horn:                                   17
% 15.91/2.50  ground:                                 3
% 15.91/2.50  unary:                                  6
% 15.91/2.50  binary:                                 9
% 15.91/2.50  lits:                                   33
% 15.91/2.50  lits_eq:                                17
% 15.91/2.50  fd_pure:                                0
% 15.91/2.50  fd_pseudo:                              0
% 15.91/2.50  fd_cond:                                0
% 15.91/2.50  fd_pseudo_cond:                         0
% 15.91/2.50  ac_symbols:                             0
% 15.91/2.50  
% 15.91/2.50  ------ Propositional Solver
% 15.91/2.50  
% 15.91/2.50  prop_solver_calls:                      37
% 15.91/2.50  prop_fast_solver_calls:                 1070
% 15.91/2.50  smt_solver_calls:                       0
% 15.91/2.50  smt_fast_solver_calls:                  0
% 15.91/2.50  prop_num_of_clauses:                    18198
% 15.91/2.50  prop_preprocess_simplified:             35692
% 15.91/2.50  prop_fo_subsumed:                       4
% 15.91/2.50  prop_solver_time:                       0.
% 15.91/2.50  smt_solver_time:                        0.
% 15.91/2.50  smt_fast_solver_time:                   0.
% 15.91/2.50  prop_fast_solver_time:                  0.
% 15.91/2.50  prop_unsat_core_time:                   0.002
% 15.91/2.50  
% 15.91/2.50  ------ QBF
% 15.91/2.50  
% 15.91/2.50  qbf_q_res:                              0
% 15.91/2.50  qbf_num_tautologies:                    0
% 15.91/2.50  qbf_prep_cycles:                        0
% 15.91/2.50  
% 15.91/2.50  ------ BMC1
% 15.91/2.50  
% 15.91/2.50  bmc1_current_bound:                     -1
% 15.91/2.50  bmc1_last_solved_bound:                 -1
% 15.91/2.50  bmc1_unsat_core_size:                   -1
% 15.91/2.50  bmc1_unsat_core_parents_size:           -1
% 15.91/2.50  bmc1_merge_next_fun:                    0
% 15.91/2.50  bmc1_unsat_core_clauses_time:           0.
% 15.91/2.50  
% 15.91/2.50  ------ Instantiation
% 15.91/2.50  
% 15.91/2.50  inst_num_of_clauses:                    6023
% 15.91/2.50  inst_num_in_passive:                    3279
% 15.91/2.50  inst_num_in_active:                     1991
% 15.91/2.50  inst_num_in_unprocessed:                753
% 15.91/2.50  inst_num_of_loops:                      2220
% 15.91/2.50  inst_num_of_learning_restarts:          0
% 15.91/2.50  inst_num_moves_active_passive:          225
% 15.91/2.50  inst_lit_activity:                      0
% 15.91/2.50  inst_lit_activity_moves:                4
% 15.91/2.50  inst_num_tautologies:                   0
% 15.91/2.50  inst_num_prop_implied:                  0
% 15.91/2.50  inst_num_existing_simplified:           0
% 15.91/2.50  inst_num_eq_res_simplified:             0
% 15.91/2.50  inst_num_child_elim:                    0
% 15.91/2.50  inst_num_of_dismatching_blockings:      12567
% 15.91/2.50  inst_num_of_non_proper_insts:           6002
% 15.91/2.50  inst_num_of_duplicates:                 0
% 15.91/2.50  inst_inst_num_from_inst_to_res:         0
% 15.91/2.50  inst_dismatching_checking_time:         0.
% 15.91/2.50  
% 15.91/2.50  ------ Resolution
% 15.91/2.50  
% 15.91/2.50  res_num_of_clauses:                     0
% 15.91/2.50  res_num_in_passive:                     0
% 15.91/2.50  res_num_in_active:                      0
% 15.91/2.50  res_num_of_loops:                       107
% 15.91/2.50  res_forward_subset_subsumed:            171
% 15.91/2.50  res_backward_subset_subsumed:           0
% 15.91/2.50  res_forward_subsumed:                   0
% 15.91/2.50  res_backward_subsumed:                  0
% 15.91/2.50  res_forward_subsumption_resolution:     0
% 15.91/2.50  res_backward_subsumption_resolution:    0
% 15.91/2.50  res_clause_to_clause_subsumption:       5861
% 15.91/2.50  res_orphan_elimination:                 0
% 15.91/2.50  res_tautology_del:                      502
% 15.91/2.50  res_num_eq_res_simplified:              1
% 15.91/2.50  res_num_sel_changes:                    0
% 15.91/2.50  res_moves_from_active_to_pass:          0
% 15.91/2.50  
% 15.91/2.50  ------ Superposition
% 15.91/2.50  
% 15.91/2.50  sup_time_total:                         0.
% 15.91/2.50  sup_time_generating:                    0.
% 15.91/2.50  sup_time_sim_full:                      0.
% 15.91/2.50  sup_time_sim_immed:                     0.
% 15.91/2.50  
% 15.91/2.50  sup_num_of_clauses:                     1655
% 15.91/2.50  sup_num_in_active:                      401
% 15.91/2.50  sup_num_in_passive:                     1254
% 15.91/2.50  sup_num_of_loops:                       443
% 15.91/2.50  sup_fw_superposition:                   2588
% 15.91/2.50  sup_bw_superposition:                   1317
% 15.91/2.50  sup_immediate_simplified:               1569
% 15.91/2.50  sup_given_eliminated:                   0
% 15.91/2.50  comparisons_done:                       0
% 15.91/2.50  comparisons_avoided:                    81
% 15.91/2.50  
% 15.91/2.50  ------ Simplifications
% 15.91/2.50  
% 15.91/2.50  
% 15.91/2.50  sim_fw_subset_subsumed:                 1
% 15.91/2.50  sim_bw_subset_subsumed:                 137
% 15.91/2.50  sim_fw_subsumed:                        506
% 15.91/2.50  sim_bw_subsumed:                        20
% 15.91/2.50  sim_fw_subsumption_res:                 0
% 15.91/2.50  sim_bw_subsumption_res:                 0
% 15.91/2.50  sim_tautology_del:                      1
% 15.91/2.50  sim_eq_tautology_del:                   432
% 15.91/2.50  sim_eq_res_simp:                        1
% 15.91/2.50  sim_fw_demodulated:                     636
% 15.91/2.50  sim_bw_demodulated:                     17
% 15.91/2.50  sim_light_normalised:                   813
% 15.91/2.50  sim_joinable_taut:                      0
% 15.91/2.50  sim_joinable_simp:                      0
% 15.91/2.50  sim_ac_normalised:                      0
% 15.91/2.50  sim_smt_subsumption:                    0
% 15.91/2.50  
%------------------------------------------------------------------------------
