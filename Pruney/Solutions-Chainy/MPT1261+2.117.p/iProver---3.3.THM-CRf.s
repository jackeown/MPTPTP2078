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
% DateTime   : Thu Dec  3 12:14:41 EST 2020

% Result     : Theorem 11.92s
% Output     : CNFRefutation 11.92s
% Verified   : 
% Statistics : Number of formulae       :  162 (2158 expanded)
%              Number of clauses        :   96 ( 648 expanded)
%              Number of leaves         :   19 ( 494 expanded)
%              Depth                    :   22
%              Number of atoms          :  374 (7467 expanded)
%              Number of equality atoms :  206 (2810 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f47,f44,f44])).

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

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f46,f44])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

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

fof(f56,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f65,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f61,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_703,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_714,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3373,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
    inference(superposition,[status(thm)],[c_703,c_714])).

cnf(c_18,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_704,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3385,plain,
    ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3373,c_704])).

cnf(c_12,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_710,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4600,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_703,c_710])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_23,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4853,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4600,c_23])).

cnf(c_4854,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4853])).

cnf(c_4859,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_3385,c_4854])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_718,plain,
    ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1217,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_718])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_712,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_717,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1910,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_712,c_717])).

cnf(c_7083,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_subset_1(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_1217,c_1910])).

cnf(c_7082,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(superposition,[status(thm)],[c_718,c_1910])).

cnf(c_7096,plain,
    ( k3_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(light_normalisation,[status(thm)],[c_7082,c_0])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_716,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1472,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_712,c_716])).

cnf(c_1586,plain,
    ( k3_subset_1(X0,k3_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_718,c_1472])).

cnf(c_8104,plain,
    ( k3_subset_1(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(demodulation,[status(thm)],[c_7096,c_1586])).

cnf(c_10390,plain,
    ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(light_normalisation,[status(thm)],[c_7083,c_8104])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_10399,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k2_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_10390,c_3])).

cnf(c_11517,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(k3_xboole_0(sK1,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = k2_xboole_0(k3_xboole_0(sK1,k1_tops_1(sK0,sK1)),sK1) ),
    inference(superposition,[status(thm)],[c_4859,c_10399])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_12660,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k2_xboole_0(k3_xboole_0(sK1,k1_tops_1(sK0,sK1)),sK1) ),
    inference(superposition,[status(thm)],[c_11517,c_1])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_715,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4365,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_712,c_715])).

cnf(c_31144,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_712,c_4365])).

cnf(c_31709,plain,
    ( k4_subset_1(X0,k3_xboole_0(X0,X1),X2) = k2_xboole_0(k3_xboole_0(X0,X1),X2)
    | r1_tarski(X2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1217,c_31144])).

cnf(c_31901,plain,
    ( k4_subset_1(X0,k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X2))) = k2_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
    inference(superposition,[status(thm)],[c_718,c_31709])).

cnf(c_32120,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(k3_xboole_0(sK1,X0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1)))) = k4_subset_1(sK1,k3_xboole_0(sK1,X0),k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_4859,c_31901])).

cnf(c_32259,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))),k3_xboole_0(sK1,X0)) = k4_subset_1(sK1,k3_xboole_0(sK1,X0),k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_32120,c_1])).

cnf(c_33170,plain,
    ( k4_subset_1(sK1,k3_xboole_0(sK1,X0),k2_tops_1(sK0,sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(sK1,X0))
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_4859,c_32259])).

cnf(c_5218,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k3_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_4859,c_0])).

cnf(c_8106,plain,
    ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_subset_1(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[status(thm)],[c_0,c_7096])).

cnf(c_8358,plain,
    ( k5_xboole_0(X0,k3_subset_1(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_8106,c_0])).

cnf(c_9493,plain,
    ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,X1) ),
    inference(demodulation,[status(thm)],[c_8104,c_8358])).

cnf(c_10240,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_5218,c_9493])).

cnf(c_19125,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_10240,c_4859])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X0,k3_subset_1(X1,X0)) = k2_subset_1(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_713,plain,
    ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_4,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_747,plain,
    ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_713,c_4])).

cnf(c_1821,plain,
    ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
    | r1_tarski(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_712,c_747])).

cnf(c_6978,plain,
    ( k4_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
    inference(superposition,[status(thm)],[c_718,c_1821])).

cnf(c_15545,plain,
    ( k4_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = X0 ),
    inference(light_normalisation,[status(thm)],[c_6978,c_7096])).

cnf(c_15551,plain,
    ( k4_subset_1(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1)),k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) = sK1
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_5218,c_15545])).

cnf(c_20736,plain,
    ( k4_subset_1(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = sK1
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_19125,c_15551])).

cnf(c_36600,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = sK1 ),
    inference(superposition,[status(thm)],[c_33170,c_20736])).

cnf(c_36805,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(k3_xboole_0(sK1,k1_tops_1(sK0,sK1)),sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_12660,c_36600])).

cnf(c_1218,plain,
    ( k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_0,c_3])).

cnf(c_1926,plain,
    ( k2_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(superposition,[status(thm)],[c_1218,c_1])).

cnf(c_11511,plain,
    ( k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = k2_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(demodulation,[status(thm)],[c_10399,c_1926])).

cnf(c_13111,plain,
    ( k2_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k2_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[status(thm)],[c_11511,c_1])).

cnf(c_13135,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(k3_xboole_0(sK1,k1_tops_1(sK0,sK1)),sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_4859,c_13111])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_709,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4367,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_703,c_715])).

cnf(c_4740,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_709,c_4367])).

cnf(c_5009,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4740,c_23])).

cnf(c_5010,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5009])).

cnf(c_5019,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_703,c_5010])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_706,plain,
    ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1079,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_703,c_706])).

cnf(c_980,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1332,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1079,c_20,c_19,c_980])).

cnf(c_5021,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_5019,c_1332])).

cnf(c_13156,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(k3_xboole_0(sK1,k1_tops_1(sK0,sK1)),sK1) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_13135,c_5021])).

cnf(c_37877,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(superposition,[status(thm)],[c_36805,c_13156])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_707,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1837,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_703,c_707])).

cnf(c_983,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2460,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1837,c_20,c_19,c_983])).

cnf(c_38181,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_37877,c_2460])).

cnf(c_11,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_977,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_17,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_38181,c_37877,c_977,c_17,c_19,c_20,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:43:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 11.92/1.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.92/1.98  
% 11.92/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.92/1.98  
% 11.92/1.98  ------  iProver source info
% 11.92/1.98  
% 11.92/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.92/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.92/1.98  git: non_committed_changes: false
% 11.92/1.98  git: last_make_outside_of_git: false
% 11.92/1.98  
% 11.92/1.98  ------ 
% 11.92/1.98  ------ Parsing...
% 11.92/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.92/1.98  
% 11.92/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 11.92/1.98  
% 11.92/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.92/1.98  
% 11.92/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.92/1.98  ------ Proving...
% 11.92/1.98  ------ Problem Properties 
% 11.92/1.98  
% 11.92/1.98  
% 11.92/1.98  clauses                                 22
% 11.92/1.98  conjectures                             5
% 11.92/1.98  EPR                                     2
% 11.92/1.98  Horn                                    21
% 11.92/1.98  unary                                   8
% 11.92/1.98  binary                                  7
% 11.92/1.98  lits                                    47
% 11.92/1.98  lits eq                                 15
% 11.92/1.98  fd_pure                                 0
% 11.92/1.98  fd_pseudo                               0
% 11.92/1.98  fd_cond                                 0
% 11.92/1.98  fd_pseudo_cond                          0
% 11.92/1.98  AC symbols                              0
% 11.92/1.98  
% 11.92/1.98  ------ Input Options Time Limit: Unbounded
% 11.92/1.98  
% 11.92/1.98  
% 11.92/1.98  ------ 
% 11.92/1.98  Current options:
% 11.92/1.98  ------ 
% 11.92/1.98  
% 11.92/1.98  
% 11.92/1.98  
% 11.92/1.98  
% 11.92/1.98  ------ Proving...
% 11.92/1.98  
% 11.92/1.98  
% 11.92/1.98  % SZS status Theorem for theBenchmark.p
% 11.92/1.98  
% 11.92/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 11.92/1.98  
% 11.92/1.98  fof(f18,conjecture,(
% 11.92/1.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 11.92/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.98  
% 11.92/1.98  fof(f19,negated_conjecture,(
% 11.92/1.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 11.92/1.98    inference(negated_conjecture,[],[f18])).
% 11.92/1.98  
% 11.92/1.98  fof(f36,plain,(
% 11.92/1.98    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 11.92/1.98    inference(ennf_transformation,[],[f19])).
% 11.92/1.98  
% 11.92/1.98  fof(f37,plain,(
% 11.92/1.98    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.92/1.98    inference(flattening,[],[f36])).
% 11.92/1.98  
% 11.92/1.98  fof(f38,plain,(
% 11.92/1.98    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.92/1.98    inference(nnf_transformation,[],[f37])).
% 11.92/1.98  
% 11.92/1.98  fof(f39,plain,(
% 11.92/1.98    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.92/1.98    inference(flattening,[],[f38])).
% 11.92/1.98  
% 11.92/1.98  fof(f41,plain,(
% 11.92/1.98    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 11.92/1.98    introduced(choice_axiom,[])).
% 11.92/1.98  
% 11.92/1.98  fof(f40,plain,(
% 11.92/1.98    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 11.92/1.98    introduced(choice_axiom,[])).
% 11.92/1.98  
% 11.92/1.98  fof(f42,plain,(
% 11.92/1.98    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 11.92/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f39,f41,f40])).
% 11.92/1.98  
% 11.92/1.98  fof(f63,plain,(
% 11.92/1.98    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.92/1.98    inference(cnf_transformation,[],[f42])).
% 11.92/1.98  
% 11.92/1.98  fof(f10,axiom,(
% 11.92/1.98    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 11.92/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.98  
% 11.92/1.98  fof(f25,plain,(
% 11.92/1.98    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.92/1.98    inference(ennf_transformation,[],[f10])).
% 11.92/1.98  
% 11.92/1.98  fof(f52,plain,(
% 11.92/1.98    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.92/1.98    inference(cnf_transformation,[],[f25])).
% 11.92/1.98  
% 11.92/1.98  fof(f2,axiom,(
% 11.92/1.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 11.92/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.98  
% 11.92/1.98  fof(f44,plain,(
% 11.92/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 11.92/1.98    inference(cnf_transformation,[],[f2])).
% 11.92/1.98  
% 11.92/1.98  fof(f70,plain,(
% 11.92/1.98    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.92/1.98    inference(definition_unfolding,[],[f52,f44])).
% 11.92/1.98  
% 11.92/1.98  fof(f64,plain,(
% 11.92/1.98    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 11.92/1.98    inference(cnf_transformation,[],[f42])).
% 11.92/1.98  
% 11.92/1.98  fof(f13,axiom,(
% 11.92/1.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 11.92/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.98  
% 11.92/1.98  fof(f28,plain,(
% 11.92/1.98    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.92/1.98    inference(ennf_transformation,[],[f13])).
% 11.92/1.98  
% 11.92/1.98  fof(f29,plain,(
% 11.92/1.98    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.92/1.98    inference(flattening,[],[f28])).
% 11.92/1.98  
% 11.92/1.98  fof(f55,plain,(
% 11.92/1.98    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.92/1.98    inference(cnf_transformation,[],[f29])).
% 11.92/1.98  
% 11.92/1.98  fof(f62,plain,(
% 11.92/1.98    l1_pre_topc(sK0)),
% 11.92/1.98    inference(cnf_transformation,[],[f42])).
% 11.92/1.98  
% 11.92/1.98  fof(f5,axiom,(
% 11.92/1.98    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 11.92/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.98  
% 11.92/1.98  fof(f47,plain,(
% 11.92/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 11.92/1.98    inference(cnf_transformation,[],[f5])).
% 11.92/1.98  
% 11.92/1.98  fof(f66,plain,(
% 11.92/1.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 11.92/1.98    inference(definition_unfolding,[],[f47,f44,f44])).
% 11.92/1.98  
% 11.92/1.98  fof(f3,axiom,(
% 11.92/1.98    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 11.92/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.98  
% 11.92/1.98  fof(f45,plain,(
% 11.92/1.98    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 11.92/1.98    inference(cnf_transformation,[],[f3])).
% 11.92/1.98  
% 11.92/1.98  fof(f67,plain,(
% 11.92/1.98    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 11.92/1.98    inference(definition_unfolding,[],[f45,f44])).
% 11.92/1.98  
% 11.92/1.98  fof(f12,axiom,(
% 11.92/1.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.92/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.98  
% 11.92/1.98  fof(f20,plain,(
% 11.92/1.98    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 11.92/1.98    inference(unused_predicate_definition_removal,[],[f12])).
% 11.92/1.98  
% 11.92/1.98  fof(f27,plain,(
% 11.92/1.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 11.92/1.98    inference(ennf_transformation,[],[f20])).
% 11.92/1.98  
% 11.92/1.98  fof(f54,plain,(
% 11.92/1.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.92/1.98    inference(cnf_transformation,[],[f27])).
% 11.92/1.98  
% 11.92/1.98  fof(f7,axiom,(
% 11.92/1.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 11.92/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.98  
% 11.92/1.98  fof(f21,plain,(
% 11.92/1.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.92/1.98    inference(ennf_transformation,[],[f7])).
% 11.92/1.98  
% 11.92/1.98  fof(f49,plain,(
% 11.92/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.92/1.98    inference(cnf_transformation,[],[f21])).
% 11.92/1.98  
% 11.92/1.98  fof(f69,plain,(
% 11.92/1.98    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.92/1.98    inference(definition_unfolding,[],[f49,f44])).
% 11.92/1.98  
% 11.92/1.98  fof(f8,axiom,(
% 11.92/1.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 11.92/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.98  
% 11.92/1.98  fof(f22,plain,(
% 11.92/1.98    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.92/1.98    inference(ennf_transformation,[],[f8])).
% 11.92/1.98  
% 11.92/1.98  fof(f50,plain,(
% 11.92/1.98    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.92/1.98    inference(cnf_transformation,[],[f22])).
% 11.92/1.98  
% 11.92/1.98  fof(f4,axiom,(
% 11.92/1.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 11.92/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.98  
% 11.92/1.98  fof(f46,plain,(
% 11.92/1.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 11.92/1.98    inference(cnf_transformation,[],[f4])).
% 11.92/1.98  
% 11.92/1.98  fof(f68,plain,(
% 11.92/1.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 11.92/1.98    inference(definition_unfolding,[],[f46,f44])).
% 11.92/1.98  
% 11.92/1.98  fof(f1,axiom,(
% 11.92/1.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 11.92/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.98  
% 11.92/1.98  fof(f43,plain,(
% 11.92/1.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 11.92/1.98    inference(cnf_transformation,[],[f1])).
% 11.92/1.98  
% 11.92/1.98  fof(f9,axiom,(
% 11.92/1.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 11.92/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.98  
% 11.92/1.98  fof(f23,plain,(
% 11.92/1.98    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 11.92/1.98    inference(ennf_transformation,[],[f9])).
% 11.92/1.98  
% 11.92/1.98  fof(f24,plain,(
% 11.92/1.98    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.92/1.98    inference(flattening,[],[f23])).
% 11.92/1.98  
% 11.92/1.98  fof(f51,plain,(
% 11.92/1.98    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.92/1.98    inference(cnf_transformation,[],[f24])).
% 11.92/1.98  
% 11.92/1.98  fof(f11,axiom,(
% 11.92/1.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 11.92/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.98  
% 11.92/1.98  fof(f26,plain,(
% 11.92/1.98    ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.92/1.98    inference(ennf_transformation,[],[f11])).
% 11.92/1.98  
% 11.92/1.98  fof(f53,plain,(
% 11.92/1.98    ( ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.92/1.98    inference(cnf_transformation,[],[f26])).
% 11.92/1.98  
% 11.92/1.98  fof(f6,axiom,(
% 11.92/1.98    ! [X0] : k2_subset_1(X0) = X0),
% 11.92/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.98  
% 11.92/1.98  fof(f48,plain,(
% 11.92/1.98    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 11.92/1.98    inference(cnf_transformation,[],[f6])).
% 11.92/1.98  
% 11.92/1.98  fof(f14,axiom,(
% 11.92/1.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.92/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.98  
% 11.92/1.98  fof(f30,plain,(
% 11.92/1.98    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.92/1.98    inference(ennf_transformation,[],[f14])).
% 11.92/1.98  
% 11.92/1.98  fof(f31,plain,(
% 11.92/1.98    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.92/1.98    inference(flattening,[],[f30])).
% 11.92/1.98  
% 11.92/1.98  fof(f57,plain,(
% 11.92/1.98    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.92/1.98    inference(cnf_transformation,[],[f31])).
% 11.92/1.98  
% 11.92/1.98  fof(f17,axiom,(
% 11.92/1.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 11.92/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.98  
% 11.92/1.98  fof(f35,plain,(
% 11.92/1.98    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.92/1.98    inference(ennf_transformation,[],[f17])).
% 11.92/1.98  
% 11.92/1.98  fof(f60,plain,(
% 11.92/1.98    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.92/1.98    inference(cnf_transformation,[],[f35])).
% 11.92/1.98  
% 11.92/1.98  fof(f16,axiom,(
% 11.92/1.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 11.92/1.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 11.92/1.98  
% 11.92/1.98  fof(f34,plain,(
% 11.92/1.98    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.92/1.98    inference(ennf_transformation,[],[f16])).
% 11.92/1.98  
% 11.92/1.98  fof(f59,plain,(
% 11.92/1.98    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.92/1.98    inference(cnf_transformation,[],[f34])).
% 11.92/1.98  
% 11.92/1.98  fof(f56,plain,(
% 11.92/1.98    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.92/1.98    inference(cnf_transformation,[],[f29])).
% 11.92/1.98  
% 11.92/1.98  fof(f65,plain,(
% 11.92/1.98    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 11.92/1.98    inference(cnf_transformation,[],[f42])).
% 11.92/1.98  
% 11.92/1.98  fof(f61,plain,(
% 11.92/1.98    v2_pre_topc(sK0)),
% 11.92/1.98    inference(cnf_transformation,[],[f42])).
% 11.92/1.98  
% 11.92/1.98  cnf(c_19,negated_conjecture,
% 11.92/1.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 11.92/1.98      inference(cnf_transformation,[],[f63]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_703,plain,
% 11.92/1.98      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 11.92/1.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_8,plain,
% 11.92/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.92/1.98      | k5_xboole_0(X0,k3_xboole_0(X0,X2)) = k7_subset_1(X1,X0,X2) ),
% 11.92/1.98      inference(cnf_transformation,[],[f70]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_714,plain,
% 11.92/1.98      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k7_subset_1(X2,X0,X1)
% 11.92/1.98      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top ),
% 11.92/1.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_3373,plain,
% 11.92/1.98      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_703,c_714]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_18,negated_conjecture,
% 11.92/1.98      ( v4_pre_topc(sK1,sK0)
% 11.92/1.98      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.92/1.98      inference(cnf_transformation,[],[f64]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_704,plain,
% 11.92/1.98      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 11.92/1.98      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 11.92/1.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_3385,plain,
% 11.92/1.98      ( k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1)
% 11.92/1.98      | v4_pre_topc(sK1,sK0) = iProver_top ),
% 11.92/1.98      inference(demodulation,[status(thm)],[c_3373,c_704]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_12,plain,
% 11.92/1.98      ( ~ v4_pre_topc(X0,X1)
% 11.92/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.92/1.98      | ~ l1_pre_topc(X1)
% 11.92/1.98      | k2_pre_topc(X1,X0) = X0 ),
% 11.92/1.98      inference(cnf_transformation,[],[f55]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_710,plain,
% 11.92/1.98      ( k2_pre_topc(X0,X1) = X1
% 11.92/1.98      | v4_pre_topc(X1,X0) != iProver_top
% 11.92/1.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.92/1.98      | l1_pre_topc(X0) != iProver_top ),
% 11.92/1.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_4600,plain,
% 11.92/1.98      ( k2_pre_topc(sK0,sK1) = sK1
% 11.92/1.98      | v4_pre_topc(sK1,sK0) != iProver_top
% 11.92/1.98      | l1_pre_topc(sK0) != iProver_top ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_703,c_710]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_20,negated_conjecture,
% 11.92/1.98      ( l1_pre_topc(sK0) ),
% 11.92/1.98      inference(cnf_transformation,[],[f62]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_23,plain,
% 11.92/1.98      ( l1_pre_topc(sK0) = iProver_top ),
% 11.92/1.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_4853,plain,
% 11.92/1.98      ( v4_pre_topc(sK1,sK0) != iProver_top
% 11.92/1.98      | k2_pre_topc(sK0,sK1) = sK1 ),
% 11.92/1.98      inference(global_propositional_subsumption,
% 11.92/1.98                [status(thm)],
% 11.92/1.98                [c_4600,c_23]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_4854,plain,
% 11.92/1.98      ( k2_pre_topc(sK0,sK1) = sK1
% 11.92/1.98      | v4_pre_topc(sK1,sK0) != iProver_top ),
% 11.92/1.98      inference(renaming,[status(thm)],[c_4853]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_4859,plain,
% 11.92/1.98      ( k2_pre_topc(sK0,sK1) = sK1
% 11.92/1.98      | k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k2_tops_1(sK0,sK1) ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_3385,c_4854]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_0,plain,
% 11.92/1.98      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_xboole_0(X0,X1) ),
% 11.92/1.98      inference(cnf_transformation,[],[f66]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_2,plain,
% 11.92/1.98      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 11.92/1.98      inference(cnf_transformation,[],[f67]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_718,plain,
% 11.92/1.98      ( r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = iProver_top ),
% 11.92/1.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_1217,plain,
% 11.92/1.98      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_0,c_718]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_10,plain,
% 11.92/1.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.92/1.98      inference(cnf_transformation,[],[f54]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_712,plain,
% 11.92/1.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 11.92/1.98      | r1_tarski(X0,X1) != iProver_top ),
% 11.92/1.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_5,plain,
% 11.92/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.92/1.98      | k5_xboole_0(X1,k3_xboole_0(X1,X0)) = k3_subset_1(X1,X0) ),
% 11.92/1.98      inference(cnf_transformation,[],[f69]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_717,plain,
% 11.92/1.98      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 11.92/1.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 11.92/1.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_1910,plain,
% 11.92/1.98      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
% 11.92/1.98      | r1_tarski(X1,X0) != iProver_top ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_712,c_717]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_7083,plain,
% 11.92/1.98      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_subset_1(X0,k3_xboole_0(X0,X1)) ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_1217,c_1910]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_7082,plain,
% 11.92/1.98      ( k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k3_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_718,c_1910]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_7096,plain,
% 11.92/1.98      ( k3_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,X1) ),
% 11.92/1.98      inference(light_normalisation,[status(thm)],[c_7082,c_0]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_6,plain,
% 11.92/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.92/1.98      | k3_subset_1(X1,k3_subset_1(X1,X0)) = X0 ),
% 11.92/1.98      inference(cnf_transformation,[],[f50]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_716,plain,
% 11.92/1.98      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 11.92/1.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 11.92/1.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_1472,plain,
% 11.92/1.98      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
% 11.92/1.98      | r1_tarski(X1,X0) != iProver_top ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_712,c_716]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_1586,plain,
% 11.92/1.98      ( k3_subset_1(X0,k3_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_718,c_1472]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_8104,plain,
% 11.92/1.98      ( k3_subset_1(X0,k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 11.92/1.98      inference(demodulation,[status(thm)],[c_7096,c_1586]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_10390,plain,
% 11.92/1.98      ( k5_xboole_0(X0,k3_xboole_0(X0,k3_xboole_0(X0,X1))) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
% 11.92/1.98      inference(light_normalisation,[status(thm)],[c_7083,c_8104]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_3,plain,
% 11.92/1.98      ( k2_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k2_xboole_0(X0,X1) ),
% 11.92/1.98      inference(cnf_transformation,[],[f68]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_10399,plain,
% 11.92/1.98      ( k2_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k2_xboole_0(k3_xboole_0(X0,X1),X0) ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_10390,c_3]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_11517,plain,
% 11.92/1.98      ( k2_pre_topc(sK0,sK1) = sK1
% 11.92/1.98      | k2_xboole_0(k3_xboole_0(sK1,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = k2_xboole_0(k3_xboole_0(sK1,k1_tops_1(sK0,sK1)),sK1) ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_4859,c_10399]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_1,plain,
% 11.92/1.98      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 11.92/1.98      inference(cnf_transformation,[],[f43]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_12660,plain,
% 11.92/1.98      ( k2_pre_topc(sK0,sK1) = sK1
% 11.92/1.98      | k2_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k2_xboole_0(k3_xboole_0(sK1,k1_tops_1(sK0,sK1)),sK1) ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_11517,c_1]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_7,plain,
% 11.92/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.92/1.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 11.92/1.98      | k4_subset_1(X1,X0,X2) = k2_xboole_0(X0,X2) ),
% 11.92/1.98      inference(cnf_transformation,[],[f51]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_715,plain,
% 11.92/1.98      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 11.92/1.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 11.92/1.98      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 11.92/1.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_4365,plain,
% 11.92/1.98      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 11.92/1.98      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 11.92/1.98      | r1_tarski(X1,X0) != iProver_top ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_712,c_715]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_31144,plain,
% 11.92/1.98      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 11.92/1.98      | r1_tarski(X2,X0) != iProver_top
% 11.92/1.98      | r1_tarski(X1,X0) != iProver_top ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_712,c_4365]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_31709,plain,
% 11.92/1.98      ( k4_subset_1(X0,k3_xboole_0(X0,X1),X2) = k2_xboole_0(k3_xboole_0(X0,X1),X2)
% 11.92/1.98      | r1_tarski(X2,X0) != iProver_top ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_1217,c_31144]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_31901,plain,
% 11.92/1.98      ( k4_subset_1(X0,k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X2))) = k2_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X2))) ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_718,c_31709]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_32120,plain,
% 11.92/1.98      ( k2_pre_topc(sK0,sK1) = sK1
% 11.92/1.98      | k2_xboole_0(k3_xboole_0(sK1,X0),k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1)))) = k4_subset_1(sK1,k3_xboole_0(sK1,X0),k2_tops_1(sK0,sK1)) ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_4859,c_31901]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_32259,plain,
% 11.92/1.98      ( k2_pre_topc(sK0,sK1) = sK1
% 11.92/1.98      | k2_xboole_0(k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))),k3_xboole_0(sK1,X0)) = k4_subset_1(sK1,k3_xboole_0(sK1,X0),k2_tops_1(sK0,sK1)) ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_32120,c_1]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_33170,plain,
% 11.92/1.98      ( k4_subset_1(sK1,k3_xboole_0(sK1,X0),k2_tops_1(sK0,sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(sK1,X0))
% 11.92/1.98      | k2_pre_topc(sK0,sK1) = sK1 ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_4859,c_32259]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_5218,plain,
% 11.92/1.98      ( k2_pre_topc(sK0,sK1) = sK1
% 11.92/1.98      | k5_xboole_0(sK1,k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) = k3_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_4859,c_0]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_8106,plain,
% 11.92/1.98      ( k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_subset_1(X0,k3_xboole_0(X0,X1)) ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_0,c_7096]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_8358,plain,
% 11.92/1.98      ( k5_xboole_0(X0,k3_subset_1(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,X1) ),
% 11.92/1.98      inference(demodulation,[status(thm)],[c_8106,c_0]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_9493,plain,
% 11.92/1.98      ( k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k3_xboole_0(X0,X1) ),
% 11.92/1.98      inference(demodulation,[status(thm)],[c_8104,c_8358]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_10240,plain,
% 11.92/1.98      ( k2_pre_topc(sK0,sK1) = sK1
% 11.92/1.98      | k5_xboole_0(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_5218,c_9493]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_19125,plain,
% 11.92/1.98      ( k2_pre_topc(sK0,sK1) = sK1
% 11.92/1.98      | k3_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_10240,c_4859]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_9,plain,
% 11.92/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.92/1.98      | k4_subset_1(X1,X0,k3_subset_1(X1,X0)) = k2_subset_1(X1) ),
% 11.92/1.98      inference(cnf_transformation,[],[f53]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_713,plain,
% 11.92/1.98      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0)
% 11.92/1.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 11.92/1.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_4,plain,
% 11.92/1.98      ( k2_subset_1(X0) = X0 ),
% 11.92/1.98      inference(cnf_transformation,[],[f48]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_747,plain,
% 11.92/1.98      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
% 11.92/1.98      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 11.92/1.98      inference(light_normalisation,[status(thm)],[c_713,c_4]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_1821,plain,
% 11.92/1.98      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
% 11.92/1.98      | r1_tarski(X1,X0) != iProver_top ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_712,c_747]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_6978,plain,
% 11.92/1.98      ( k4_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) = X0 ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_718,c_1821]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_15545,plain,
% 11.92/1.98      ( k4_subset_1(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = X0 ),
% 11.92/1.98      inference(light_normalisation,[status(thm)],[c_6978,c_7096]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_15551,plain,
% 11.92/1.98      ( k4_subset_1(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1)),k3_xboole_0(sK1,k2_tops_1(sK0,sK1))) = sK1
% 11.92/1.98      | k2_pre_topc(sK0,sK1) = sK1 ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_5218,c_15545]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_20736,plain,
% 11.92/1.98      ( k4_subset_1(sK1,k3_xboole_0(sK1,k1_tops_1(sK0,sK1)),k2_tops_1(sK0,sK1)) = sK1
% 11.92/1.98      | k2_pre_topc(sK0,sK1) = sK1 ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_19125,c_15551]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_36600,plain,
% 11.92/1.98      ( k2_pre_topc(sK0,sK1) = sK1
% 11.92/1.98      | k2_xboole_0(k2_tops_1(sK0,sK1),k3_xboole_0(sK1,k1_tops_1(sK0,sK1))) = sK1 ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_33170,c_20736]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_36805,plain,
% 11.92/1.98      ( k2_pre_topc(sK0,sK1) = sK1
% 11.92/1.98      | k2_xboole_0(k3_xboole_0(sK1,k1_tops_1(sK0,sK1)),sK1) = sK1 ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_12660,c_36600]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_1218,plain,
% 11.92/1.98      ( k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_0,c_3]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_1926,plain,
% 11.92/1.98      ( k2_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_1218,c_1]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_11511,plain,
% 11.92/1.98      ( k2_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) = k2_xboole_0(k3_xboole_0(X0,X1),X0) ),
% 11.92/1.98      inference(demodulation,[status(thm)],[c_10399,c_1926]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_13111,plain,
% 11.92/1.98      ( k2_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))) = k2_xboole_0(k3_xboole_0(X0,X1),X0) ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_11511,c_1]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_13135,plain,
% 11.92/1.98      ( k2_pre_topc(sK0,sK1) = sK1
% 11.92/1.98      | k2_xboole_0(k3_xboole_0(sK1,k1_tops_1(sK0,sK1)),sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_4859,c_13111]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_13,plain,
% 11.92/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.92/1.98      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 11.92/1.98      | ~ l1_pre_topc(X1) ),
% 11.92/1.98      inference(cnf_transformation,[],[f57]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_709,plain,
% 11.92/1.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 11.92/1.98      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 11.92/1.98      | l1_pre_topc(X1) != iProver_top ),
% 11.92/1.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_4367,plain,
% 11.92/1.98      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
% 11.92/1.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_703,c_715]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_4740,plain,
% 11.92/1.98      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
% 11.92/1.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.92/1.98      | l1_pre_topc(sK0) != iProver_top ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_709,c_4367]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_5009,plain,
% 11.92/1.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 11.92/1.98      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0)) ),
% 11.92/1.98      inference(global_propositional_subsumption,
% 11.92/1.98                [status(thm)],
% 11.92/1.98                [c_4740,c_23]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_5010,plain,
% 11.92/1.98      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
% 11.92/1.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 11.92/1.98      inference(renaming,[status(thm)],[c_5009]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_5019,plain,
% 11.92/1.98      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_703,c_5010]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_16,plain,
% 11.92/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.92/1.98      | ~ l1_pre_topc(X1)
% 11.92/1.98      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 11.92/1.98      inference(cnf_transformation,[],[f60]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_706,plain,
% 11.92/1.98      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
% 11.92/1.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.92/1.98      | l1_pre_topc(X0) != iProver_top ),
% 11.92/1.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_1079,plain,
% 11.92/1.98      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
% 11.92/1.98      | l1_pre_topc(sK0) != iProver_top ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_703,c_706]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_980,plain,
% 11.92/1.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.92/1.98      | ~ l1_pre_topc(sK0)
% 11.92/1.98      | k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 11.92/1.98      inference(instantiation,[status(thm)],[c_16]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_1332,plain,
% 11.92/1.98      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 11.92/1.98      inference(global_propositional_subsumption,
% 11.92/1.98                [status(thm)],
% 11.92/1.98                [c_1079,c_20,c_19,c_980]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_5021,plain,
% 11.92/1.98      ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 11.92/1.98      inference(light_normalisation,[status(thm)],[c_5019,c_1332]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_13156,plain,
% 11.92/1.98      ( k2_pre_topc(sK0,sK1) = sK1
% 11.92/1.98      | k2_xboole_0(k3_xboole_0(sK1,k1_tops_1(sK0,sK1)),sK1) = k2_pre_topc(sK0,sK1) ),
% 11.92/1.98      inference(light_normalisation,[status(thm)],[c_13135,c_5021]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_37877,plain,
% 11.92/1.98      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_36805,c_13156]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_15,plain,
% 11.92/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.92/1.98      | ~ l1_pre_topc(X1)
% 11.92/1.98      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 11.92/1.98      inference(cnf_transformation,[],[f59]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_707,plain,
% 11.92/1.98      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
% 11.92/1.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 11.92/1.98      | l1_pre_topc(X0) != iProver_top ),
% 11.92/1.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_1837,plain,
% 11.92/1.98      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 11.92/1.98      | l1_pre_topc(sK0) != iProver_top ),
% 11.92/1.98      inference(superposition,[status(thm)],[c_703,c_707]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_983,plain,
% 11.92/1.98      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.92/1.98      | ~ l1_pre_topc(sK0)
% 11.92/1.98      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.92/1.98      inference(instantiation,[status(thm)],[c_15]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_2460,plain,
% 11.92/1.98      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.92/1.98      inference(global_propositional_subsumption,
% 11.92/1.98                [status(thm)],
% 11.92/1.98                [c_1837,c_20,c_19,c_983]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_38181,plain,
% 11.92/1.98      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 11.92/1.98      inference(demodulation,[status(thm)],[c_37877,c_2460]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_11,plain,
% 11.92/1.98      ( v4_pre_topc(X0,X1)
% 11.92/1.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 11.92/1.98      | ~ l1_pre_topc(X1)
% 11.92/1.98      | ~ v2_pre_topc(X1)
% 11.92/1.98      | k2_pre_topc(X1,X0) != X0 ),
% 11.92/1.98      inference(cnf_transformation,[],[f56]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_977,plain,
% 11.92/1.98      ( v4_pre_topc(sK1,sK0)
% 11.92/1.98      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 11.92/1.98      | ~ l1_pre_topc(sK0)
% 11.92/1.98      | ~ v2_pre_topc(sK0)
% 11.92/1.98      | k2_pre_topc(sK0,sK1) != sK1 ),
% 11.92/1.98      inference(instantiation,[status(thm)],[c_11]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_17,negated_conjecture,
% 11.92/1.98      ( ~ v4_pre_topc(sK1,sK0)
% 11.92/1.98      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 11.92/1.98      inference(cnf_transformation,[],[f65]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(c_21,negated_conjecture,
% 11.92/1.98      ( v2_pre_topc(sK0) ),
% 11.92/1.98      inference(cnf_transformation,[],[f61]) ).
% 11.92/1.98  
% 11.92/1.98  cnf(contradiction,plain,
% 11.92/1.98      ( $false ),
% 11.92/1.98      inference(minisat,
% 11.92/1.98                [status(thm)],
% 11.92/1.98                [c_38181,c_37877,c_977,c_17,c_19,c_20,c_21]) ).
% 11.92/1.98  
% 11.92/1.98  
% 11.92/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 11.92/1.98  
% 11.92/1.98  ------                               Statistics
% 11.92/1.98  
% 11.92/1.98  ------ Selected
% 11.92/1.98  
% 11.92/1.98  total_time:                             1.3
% 11.92/1.98  
%------------------------------------------------------------------------------
