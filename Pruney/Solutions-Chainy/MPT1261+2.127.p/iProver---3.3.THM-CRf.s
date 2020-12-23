%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:14:43 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 428 expanded)
%              Number of clauses        :   58 ( 123 expanded)
%              Number of leaves         :   13 (  94 expanded)
%              Depth                    :   20
%              Number of atoms          :  288 (2007 expanded)
%              Number of equality atoms :  128 ( 642 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1)
            | ~ v4_pre_topc(X1,X0) )
          & ( k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f27,plain,(
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

fof(f26,plain,
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

fof(f28,plain,
    ( ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f27,f26])).

fof(f43,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
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

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f32,f31])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f44,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f40,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_11,negated_conjecture,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_97,plain,
    ( v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_6,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_13,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_237,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_13])).

cnf(c_238,plain,
    ( ~ v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_237])).

cnf(c_267,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,X0) = X0
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_97,c_238])).

cnf(c_268,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(unflattening,[status(thm)],[c_267])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_270,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_268,c_12])).

cnf(c_317,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_270])).

cnf(c_318,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(renaming,[status(thm)],[c_317])).

cnf(c_583,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_584,plain,
    ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1567,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
    inference(superposition,[status(thm)],[c_583,c_584])).

cnf(c_1706,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_318,c_1567])).

cnf(c_0,plain,
    ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_1,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_2,plain,
    ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_946,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_2])).

cnf(c_1007,plain,
    ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(superposition,[status(thm)],[c_1,c_946])).

cnf(c_1499,plain,
    ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[status(thm)],[c_0,c_1007])).

cnf(c_2421,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_1706,c_1499])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_225,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_13])).

cnf(c_226,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unflattening,[status(thm)],[c_225])).

cnf(c_580,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_226])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_585,plain,
    ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2202,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_583,c_585])).

cnf(c_2588,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_580,c_2202])).

cnf(c_2692,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    inference(superposition,[status(thm)],[c_583,c_2588])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_201,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_13])).

cnf(c_202,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_201])).

cnf(c_582,plain,
    ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_202])).

cnf(c_666,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_583,c_582])).

cnf(c_2699,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    inference(light_normalisation,[status(thm)],[c_2692,c_666])).

cnf(c_3466,plain,
    ( k2_pre_topc(sK0,sK1) = sK1 ),
    inference(demodulation,[status(thm)],[c_2421,c_2699])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_213,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_13])).

cnf(c_214,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
    inference(unflattening,[status(thm)],[c_213])).

cnf(c_581,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_214])).

cnf(c_731,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(superposition,[status(thm)],[c_583,c_581])).

cnf(c_3470,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
    inference(demodulation,[status(thm)],[c_3466,c_731])).

cnf(c_10,negated_conjecture,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_95,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_5,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_14,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_176,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_14])).

cnf(c_177,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_176])).

cnf(c_181,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(X0,sK0)
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_177,c_13])).

cnf(c_182,plain,
    ( v4_pre_topc(X0,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,X0) != X0 ),
    inference(renaming,[status(thm)],[c_181])).

cnf(c_278,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,X0) != X0
    | sK1 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_95,c_182])).

cnf(c_279,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(unflattening,[status(thm)],[c_278])).

cnf(c_281,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
    | k2_pre_topc(sK0,sK1) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_279,c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3470,c_3466,c_281])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:41:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.18/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.01  
% 2.18/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.18/1.01  
% 2.18/1.01  ------  iProver source info
% 2.18/1.01  
% 2.18/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.18/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.18/1.01  git: non_committed_changes: false
% 2.18/1.01  git: last_make_outside_of_git: false
% 2.18/1.01  
% 2.18/1.01  ------ 
% 2.18/1.01  
% 2.18/1.01  ------ Input Options
% 2.18/1.01  
% 2.18/1.01  --out_options                           all
% 2.18/1.01  --tptp_safe_out                         true
% 2.18/1.01  --problem_path                          ""
% 2.18/1.01  --include_path                          ""
% 2.18/1.01  --clausifier                            res/vclausify_rel
% 2.18/1.01  --clausifier_options                    --mode clausify
% 2.18/1.01  --stdin                                 false
% 2.18/1.01  --stats_out                             all
% 2.18/1.01  
% 2.18/1.01  ------ General Options
% 2.18/1.01  
% 2.18/1.01  --fof                                   false
% 2.18/1.01  --time_out_real                         305.
% 2.18/1.01  --time_out_virtual                      -1.
% 2.18/1.01  --symbol_type_check                     false
% 2.18/1.01  --clausify_out                          false
% 2.18/1.01  --sig_cnt_out                           false
% 2.18/1.01  --trig_cnt_out                          false
% 2.18/1.01  --trig_cnt_out_tolerance                1.
% 2.18/1.01  --trig_cnt_out_sk_spl                   false
% 2.18/1.01  --abstr_cl_out                          false
% 2.18/1.01  
% 2.18/1.01  ------ Global Options
% 2.18/1.01  
% 2.18/1.01  --schedule                              default
% 2.18/1.01  --add_important_lit                     false
% 2.18/1.01  --prop_solver_per_cl                    1000
% 2.18/1.01  --min_unsat_core                        false
% 2.18/1.01  --soft_assumptions                      false
% 2.18/1.01  --soft_lemma_size                       3
% 2.18/1.01  --prop_impl_unit_size                   0
% 2.18/1.01  --prop_impl_unit                        []
% 2.18/1.01  --share_sel_clauses                     true
% 2.18/1.01  --reset_solvers                         false
% 2.18/1.01  --bc_imp_inh                            [conj_cone]
% 2.18/1.01  --conj_cone_tolerance                   3.
% 2.18/1.01  --extra_neg_conj                        none
% 2.18/1.01  --large_theory_mode                     true
% 2.18/1.01  --prolific_symb_bound                   200
% 2.18/1.01  --lt_threshold                          2000
% 2.18/1.01  --clause_weak_htbl                      true
% 2.18/1.01  --gc_record_bc_elim                     false
% 2.18/1.01  
% 2.18/1.01  ------ Preprocessing Options
% 2.18/1.01  
% 2.18/1.01  --preprocessing_flag                    true
% 2.18/1.01  --time_out_prep_mult                    0.1
% 2.18/1.01  --splitting_mode                        input
% 2.18/1.01  --splitting_grd                         true
% 2.18/1.01  --splitting_cvd                         false
% 2.18/1.01  --splitting_cvd_svl                     false
% 2.18/1.01  --splitting_nvd                         32
% 2.18/1.01  --sub_typing                            true
% 2.18/1.01  --prep_gs_sim                           true
% 2.18/1.01  --prep_unflatten                        true
% 2.18/1.01  --prep_res_sim                          true
% 2.18/1.01  --prep_upred                            true
% 2.18/1.01  --prep_sem_filter                       exhaustive
% 2.18/1.01  --prep_sem_filter_out                   false
% 2.18/1.01  --pred_elim                             true
% 2.18/1.01  --res_sim_input                         true
% 2.18/1.01  --eq_ax_congr_red                       true
% 2.18/1.01  --pure_diseq_elim                       true
% 2.18/1.01  --brand_transform                       false
% 2.18/1.01  --non_eq_to_eq                          false
% 2.18/1.01  --prep_def_merge                        true
% 2.18/1.01  --prep_def_merge_prop_impl              false
% 2.18/1.01  --prep_def_merge_mbd                    true
% 2.18/1.01  --prep_def_merge_tr_red                 false
% 2.18/1.01  --prep_def_merge_tr_cl                  false
% 2.18/1.01  --smt_preprocessing                     true
% 2.18/1.01  --smt_ac_axioms                         fast
% 2.18/1.01  --preprocessed_out                      false
% 2.18/1.01  --preprocessed_stats                    false
% 2.18/1.01  
% 2.18/1.01  ------ Abstraction refinement Options
% 2.18/1.01  
% 2.18/1.01  --abstr_ref                             []
% 2.18/1.01  --abstr_ref_prep                        false
% 2.18/1.01  --abstr_ref_until_sat                   false
% 2.18/1.01  --abstr_ref_sig_restrict                funpre
% 2.18/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.18/1.01  --abstr_ref_under                       []
% 2.18/1.01  
% 2.18/1.01  ------ SAT Options
% 2.18/1.01  
% 2.18/1.01  --sat_mode                              false
% 2.18/1.01  --sat_fm_restart_options                ""
% 2.18/1.01  --sat_gr_def                            false
% 2.18/1.01  --sat_epr_types                         true
% 2.18/1.01  --sat_non_cyclic_types                  false
% 2.18/1.01  --sat_finite_models                     false
% 2.18/1.01  --sat_fm_lemmas                         false
% 2.18/1.01  --sat_fm_prep                           false
% 2.18/1.01  --sat_fm_uc_incr                        true
% 2.18/1.01  --sat_out_model                         small
% 2.18/1.01  --sat_out_clauses                       false
% 2.18/1.01  
% 2.18/1.01  ------ QBF Options
% 2.18/1.01  
% 2.18/1.01  --qbf_mode                              false
% 2.18/1.01  --qbf_elim_univ                         false
% 2.18/1.01  --qbf_dom_inst                          none
% 2.18/1.01  --qbf_dom_pre_inst                      false
% 2.18/1.01  --qbf_sk_in                             false
% 2.18/1.01  --qbf_pred_elim                         true
% 2.18/1.01  --qbf_split                             512
% 2.18/1.01  
% 2.18/1.01  ------ BMC1 Options
% 2.18/1.01  
% 2.18/1.01  --bmc1_incremental                      false
% 2.18/1.01  --bmc1_axioms                           reachable_all
% 2.18/1.01  --bmc1_min_bound                        0
% 2.18/1.01  --bmc1_max_bound                        -1
% 2.18/1.01  --bmc1_max_bound_default                -1
% 2.18/1.01  --bmc1_symbol_reachability              true
% 2.18/1.01  --bmc1_property_lemmas                  false
% 2.18/1.01  --bmc1_k_induction                      false
% 2.18/1.01  --bmc1_non_equiv_states                 false
% 2.18/1.01  --bmc1_deadlock                         false
% 2.18/1.01  --bmc1_ucm                              false
% 2.18/1.01  --bmc1_add_unsat_core                   none
% 2.18/1.01  --bmc1_unsat_core_children              false
% 2.18/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.18/1.01  --bmc1_out_stat                         full
% 2.18/1.01  --bmc1_ground_init                      false
% 2.18/1.01  --bmc1_pre_inst_next_state              false
% 2.18/1.01  --bmc1_pre_inst_state                   false
% 2.18/1.01  --bmc1_pre_inst_reach_state             false
% 2.18/1.01  --bmc1_out_unsat_core                   false
% 2.18/1.01  --bmc1_aig_witness_out                  false
% 2.18/1.01  --bmc1_verbose                          false
% 2.18/1.01  --bmc1_dump_clauses_tptp                false
% 2.18/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.18/1.01  --bmc1_dump_file                        -
% 2.18/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.18/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.18/1.01  --bmc1_ucm_extend_mode                  1
% 2.18/1.01  --bmc1_ucm_init_mode                    2
% 2.18/1.01  --bmc1_ucm_cone_mode                    none
% 2.18/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.18/1.01  --bmc1_ucm_relax_model                  4
% 2.18/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.18/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.18/1.01  --bmc1_ucm_layered_model                none
% 2.18/1.01  --bmc1_ucm_max_lemma_size               10
% 2.18/1.01  
% 2.18/1.01  ------ AIG Options
% 2.18/1.01  
% 2.18/1.01  --aig_mode                              false
% 2.18/1.01  
% 2.18/1.01  ------ Instantiation Options
% 2.18/1.01  
% 2.18/1.01  --instantiation_flag                    true
% 2.18/1.01  --inst_sos_flag                         false
% 2.18/1.01  --inst_sos_phase                        true
% 2.18/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.18/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.18/1.01  --inst_lit_sel_side                     num_symb
% 2.18/1.01  --inst_solver_per_active                1400
% 2.18/1.01  --inst_solver_calls_frac                1.
% 2.18/1.01  --inst_passive_queue_type               priority_queues
% 2.18/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.18/1.01  --inst_passive_queues_freq              [25;2]
% 2.18/1.01  --inst_dismatching                      true
% 2.18/1.01  --inst_eager_unprocessed_to_passive     true
% 2.18/1.01  --inst_prop_sim_given                   true
% 2.18/1.01  --inst_prop_sim_new                     false
% 2.18/1.01  --inst_subs_new                         false
% 2.18/1.01  --inst_eq_res_simp                      false
% 2.18/1.01  --inst_subs_given                       false
% 2.18/1.01  --inst_orphan_elimination               true
% 2.18/1.01  --inst_learning_loop_flag               true
% 2.18/1.01  --inst_learning_start                   3000
% 2.18/1.01  --inst_learning_factor                  2
% 2.18/1.01  --inst_start_prop_sim_after_learn       3
% 2.18/1.01  --inst_sel_renew                        solver
% 2.18/1.01  --inst_lit_activity_flag                true
% 2.18/1.01  --inst_restr_to_given                   false
% 2.18/1.01  --inst_activity_threshold               500
% 2.18/1.01  --inst_out_proof                        true
% 2.18/1.01  
% 2.18/1.01  ------ Resolution Options
% 2.18/1.01  
% 2.18/1.01  --resolution_flag                       true
% 2.18/1.01  --res_lit_sel                           adaptive
% 2.18/1.01  --res_lit_sel_side                      none
% 2.18/1.01  --res_ordering                          kbo
% 2.18/1.01  --res_to_prop_solver                    active
% 2.18/1.01  --res_prop_simpl_new                    false
% 2.18/1.01  --res_prop_simpl_given                  true
% 2.18/1.01  --res_passive_queue_type                priority_queues
% 2.18/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.18/1.01  --res_passive_queues_freq               [15;5]
% 2.18/1.01  --res_forward_subs                      full
% 2.18/1.01  --res_backward_subs                     full
% 2.18/1.01  --res_forward_subs_resolution           true
% 2.18/1.01  --res_backward_subs_resolution          true
% 2.18/1.01  --res_orphan_elimination                true
% 2.18/1.01  --res_time_limit                        2.
% 2.18/1.01  --res_out_proof                         true
% 2.18/1.01  
% 2.18/1.01  ------ Superposition Options
% 2.18/1.01  
% 2.18/1.01  --superposition_flag                    true
% 2.18/1.01  --sup_passive_queue_type                priority_queues
% 2.18/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.18/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.18/1.01  --demod_completeness_check              fast
% 2.18/1.01  --demod_use_ground                      true
% 2.18/1.01  --sup_to_prop_solver                    passive
% 2.18/1.01  --sup_prop_simpl_new                    true
% 2.18/1.01  --sup_prop_simpl_given                  true
% 2.18/1.01  --sup_fun_splitting                     false
% 2.18/1.01  --sup_smt_interval                      50000
% 2.18/1.02  
% 2.18/1.02  ------ Superposition Simplification Setup
% 2.18/1.02  
% 2.18/1.02  --sup_indices_passive                   []
% 2.18/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.18/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.02  --sup_full_bw                           [BwDemod]
% 2.18/1.02  --sup_immed_triv                        [TrivRules]
% 2.18/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.18/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.02  --sup_immed_bw_main                     []
% 2.18/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.18/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/1.02  
% 2.18/1.02  ------ Combination Options
% 2.18/1.02  
% 2.18/1.02  --comb_res_mult                         3
% 2.18/1.02  --comb_sup_mult                         2
% 2.18/1.02  --comb_inst_mult                        10
% 2.18/1.02  
% 2.18/1.02  ------ Debug Options
% 2.18/1.02  
% 2.18/1.02  --dbg_backtrace                         false
% 2.18/1.02  --dbg_dump_prop_clauses                 false
% 2.18/1.02  --dbg_dump_prop_clauses_file            -
% 2.18/1.02  --dbg_out_stat                          false
% 2.18/1.02  ------ Parsing...
% 2.18/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.18/1.02  
% 2.18/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.18/1.02  
% 2.18/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.18/1.02  
% 2.18/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.18/1.02  ------ Proving...
% 2.18/1.02  ------ Problem Properties 
% 2.18/1.02  
% 2.18/1.02  
% 2.18/1.02  clauses                                 11
% 2.18/1.02  conjectures                             1
% 2.18/1.02  EPR                                     0
% 2.18/1.02  Horn                                    10
% 2.18/1.02  unary                                   4
% 2.18/1.02  binary                                  6
% 2.18/1.02  lits                                    19
% 2.18/1.02  lits eq                                 11
% 2.18/1.02  fd_pure                                 0
% 2.18/1.02  fd_pseudo                               0
% 2.18/1.02  fd_cond                                 0
% 2.18/1.02  fd_pseudo_cond                          0
% 2.18/1.02  AC symbols                              0
% 2.18/1.02  
% 2.18/1.02  ------ Schedule dynamic 5 is on 
% 2.18/1.02  
% 2.18/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.18/1.02  
% 2.18/1.02  
% 2.18/1.02  ------ 
% 2.18/1.02  Current options:
% 2.18/1.02  ------ 
% 2.18/1.02  
% 2.18/1.02  ------ Input Options
% 2.18/1.02  
% 2.18/1.02  --out_options                           all
% 2.18/1.02  --tptp_safe_out                         true
% 2.18/1.02  --problem_path                          ""
% 2.18/1.02  --include_path                          ""
% 2.18/1.02  --clausifier                            res/vclausify_rel
% 2.18/1.02  --clausifier_options                    --mode clausify
% 2.18/1.02  --stdin                                 false
% 2.18/1.02  --stats_out                             all
% 2.18/1.02  
% 2.18/1.02  ------ General Options
% 2.18/1.02  
% 2.18/1.02  --fof                                   false
% 2.18/1.02  --time_out_real                         305.
% 2.18/1.02  --time_out_virtual                      -1.
% 2.18/1.02  --symbol_type_check                     false
% 2.18/1.02  --clausify_out                          false
% 2.18/1.02  --sig_cnt_out                           false
% 2.18/1.02  --trig_cnt_out                          false
% 2.18/1.02  --trig_cnt_out_tolerance                1.
% 2.18/1.02  --trig_cnt_out_sk_spl                   false
% 2.18/1.02  --abstr_cl_out                          false
% 2.18/1.02  
% 2.18/1.02  ------ Global Options
% 2.18/1.02  
% 2.18/1.02  --schedule                              default
% 2.18/1.02  --add_important_lit                     false
% 2.18/1.02  --prop_solver_per_cl                    1000
% 2.18/1.02  --min_unsat_core                        false
% 2.18/1.02  --soft_assumptions                      false
% 2.18/1.02  --soft_lemma_size                       3
% 2.18/1.02  --prop_impl_unit_size                   0
% 2.18/1.02  --prop_impl_unit                        []
% 2.18/1.02  --share_sel_clauses                     true
% 2.18/1.02  --reset_solvers                         false
% 2.18/1.02  --bc_imp_inh                            [conj_cone]
% 2.18/1.02  --conj_cone_tolerance                   3.
% 2.18/1.02  --extra_neg_conj                        none
% 2.18/1.02  --large_theory_mode                     true
% 2.18/1.02  --prolific_symb_bound                   200
% 2.18/1.02  --lt_threshold                          2000
% 2.18/1.02  --clause_weak_htbl                      true
% 2.18/1.02  --gc_record_bc_elim                     false
% 2.18/1.02  
% 2.18/1.02  ------ Preprocessing Options
% 2.18/1.02  
% 2.18/1.02  --preprocessing_flag                    true
% 2.18/1.02  --time_out_prep_mult                    0.1
% 2.18/1.02  --splitting_mode                        input
% 2.18/1.02  --splitting_grd                         true
% 2.18/1.02  --splitting_cvd                         false
% 2.18/1.02  --splitting_cvd_svl                     false
% 2.18/1.02  --splitting_nvd                         32
% 2.18/1.02  --sub_typing                            true
% 2.18/1.02  --prep_gs_sim                           true
% 2.18/1.02  --prep_unflatten                        true
% 2.18/1.02  --prep_res_sim                          true
% 2.18/1.02  --prep_upred                            true
% 2.18/1.02  --prep_sem_filter                       exhaustive
% 2.18/1.02  --prep_sem_filter_out                   false
% 2.18/1.02  --pred_elim                             true
% 2.18/1.02  --res_sim_input                         true
% 2.18/1.02  --eq_ax_congr_red                       true
% 2.18/1.02  --pure_diseq_elim                       true
% 2.18/1.02  --brand_transform                       false
% 2.18/1.02  --non_eq_to_eq                          false
% 2.18/1.02  --prep_def_merge                        true
% 2.18/1.02  --prep_def_merge_prop_impl              false
% 2.18/1.02  --prep_def_merge_mbd                    true
% 2.18/1.02  --prep_def_merge_tr_red                 false
% 2.18/1.02  --prep_def_merge_tr_cl                  false
% 2.18/1.02  --smt_preprocessing                     true
% 2.18/1.02  --smt_ac_axioms                         fast
% 2.18/1.02  --preprocessed_out                      false
% 2.18/1.02  --preprocessed_stats                    false
% 2.18/1.02  
% 2.18/1.02  ------ Abstraction refinement Options
% 2.18/1.02  
% 2.18/1.02  --abstr_ref                             []
% 2.18/1.02  --abstr_ref_prep                        false
% 2.18/1.02  --abstr_ref_until_sat                   false
% 2.18/1.02  --abstr_ref_sig_restrict                funpre
% 2.18/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.18/1.02  --abstr_ref_under                       []
% 2.18/1.02  
% 2.18/1.02  ------ SAT Options
% 2.18/1.02  
% 2.18/1.02  --sat_mode                              false
% 2.18/1.02  --sat_fm_restart_options                ""
% 2.18/1.02  --sat_gr_def                            false
% 2.18/1.02  --sat_epr_types                         true
% 2.18/1.02  --sat_non_cyclic_types                  false
% 2.18/1.02  --sat_finite_models                     false
% 2.18/1.02  --sat_fm_lemmas                         false
% 2.18/1.02  --sat_fm_prep                           false
% 2.18/1.02  --sat_fm_uc_incr                        true
% 2.18/1.02  --sat_out_model                         small
% 2.18/1.02  --sat_out_clauses                       false
% 2.18/1.02  
% 2.18/1.02  ------ QBF Options
% 2.18/1.02  
% 2.18/1.02  --qbf_mode                              false
% 2.18/1.02  --qbf_elim_univ                         false
% 2.18/1.02  --qbf_dom_inst                          none
% 2.18/1.02  --qbf_dom_pre_inst                      false
% 2.18/1.02  --qbf_sk_in                             false
% 2.18/1.02  --qbf_pred_elim                         true
% 2.18/1.02  --qbf_split                             512
% 2.18/1.02  
% 2.18/1.02  ------ BMC1 Options
% 2.18/1.02  
% 2.18/1.02  --bmc1_incremental                      false
% 2.18/1.02  --bmc1_axioms                           reachable_all
% 2.18/1.02  --bmc1_min_bound                        0
% 2.18/1.02  --bmc1_max_bound                        -1
% 2.18/1.02  --bmc1_max_bound_default                -1
% 2.18/1.02  --bmc1_symbol_reachability              true
% 2.18/1.02  --bmc1_property_lemmas                  false
% 2.18/1.02  --bmc1_k_induction                      false
% 2.18/1.02  --bmc1_non_equiv_states                 false
% 2.18/1.02  --bmc1_deadlock                         false
% 2.18/1.02  --bmc1_ucm                              false
% 2.18/1.02  --bmc1_add_unsat_core                   none
% 2.18/1.02  --bmc1_unsat_core_children              false
% 2.18/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.18/1.02  --bmc1_out_stat                         full
% 2.18/1.02  --bmc1_ground_init                      false
% 2.18/1.02  --bmc1_pre_inst_next_state              false
% 2.18/1.02  --bmc1_pre_inst_state                   false
% 2.18/1.02  --bmc1_pre_inst_reach_state             false
% 2.18/1.02  --bmc1_out_unsat_core                   false
% 2.18/1.02  --bmc1_aig_witness_out                  false
% 2.18/1.02  --bmc1_verbose                          false
% 2.18/1.02  --bmc1_dump_clauses_tptp                false
% 2.18/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.18/1.02  --bmc1_dump_file                        -
% 2.18/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.18/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.18/1.02  --bmc1_ucm_extend_mode                  1
% 2.18/1.02  --bmc1_ucm_init_mode                    2
% 2.18/1.02  --bmc1_ucm_cone_mode                    none
% 2.18/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.18/1.02  --bmc1_ucm_relax_model                  4
% 2.18/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.18/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.18/1.02  --bmc1_ucm_layered_model                none
% 2.18/1.02  --bmc1_ucm_max_lemma_size               10
% 2.18/1.02  
% 2.18/1.02  ------ AIG Options
% 2.18/1.02  
% 2.18/1.02  --aig_mode                              false
% 2.18/1.02  
% 2.18/1.02  ------ Instantiation Options
% 2.18/1.02  
% 2.18/1.02  --instantiation_flag                    true
% 2.18/1.02  --inst_sos_flag                         false
% 2.18/1.02  --inst_sos_phase                        true
% 2.18/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.18/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.18/1.02  --inst_lit_sel_side                     none
% 2.18/1.02  --inst_solver_per_active                1400
% 2.18/1.02  --inst_solver_calls_frac                1.
% 2.18/1.02  --inst_passive_queue_type               priority_queues
% 2.18/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.18/1.02  --inst_passive_queues_freq              [25;2]
% 2.18/1.02  --inst_dismatching                      true
% 2.18/1.02  --inst_eager_unprocessed_to_passive     true
% 2.18/1.02  --inst_prop_sim_given                   true
% 2.18/1.02  --inst_prop_sim_new                     false
% 2.18/1.02  --inst_subs_new                         false
% 2.18/1.02  --inst_eq_res_simp                      false
% 2.18/1.02  --inst_subs_given                       false
% 2.18/1.02  --inst_orphan_elimination               true
% 2.18/1.02  --inst_learning_loop_flag               true
% 2.18/1.02  --inst_learning_start                   3000
% 2.18/1.02  --inst_learning_factor                  2
% 2.18/1.02  --inst_start_prop_sim_after_learn       3
% 2.18/1.02  --inst_sel_renew                        solver
% 2.18/1.02  --inst_lit_activity_flag                true
% 2.18/1.02  --inst_restr_to_given                   false
% 2.18/1.02  --inst_activity_threshold               500
% 2.18/1.02  --inst_out_proof                        true
% 2.18/1.02  
% 2.18/1.02  ------ Resolution Options
% 2.18/1.02  
% 2.18/1.02  --resolution_flag                       false
% 2.18/1.02  --res_lit_sel                           adaptive
% 2.18/1.02  --res_lit_sel_side                      none
% 2.18/1.02  --res_ordering                          kbo
% 2.18/1.02  --res_to_prop_solver                    active
% 2.18/1.02  --res_prop_simpl_new                    false
% 2.18/1.02  --res_prop_simpl_given                  true
% 2.18/1.02  --res_passive_queue_type                priority_queues
% 2.18/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.18/1.02  --res_passive_queues_freq               [15;5]
% 2.18/1.02  --res_forward_subs                      full
% 2.18/1.02  --res_backward_subs                     full
% 2.18/1.02  --res_forward_subs_resolution           true
% 2.18/1.02  --res_backward_subs_resolution          true
% 2.18/1.02  --res_orphan_elimination                true
% 2.18/1.02  --res_time_limit                        2.
% 2.18/1.02  --res_out_proof                         true
% 2.18/1.02  
% 2.18/1.02  ------ Superposition Options
% 2.18/1.02  
% 2.18/1.02  --superposition_flag                    true
% 2.18/1.02  --sup_passive_queue_type                priority_queues
% 2.18/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.18/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.18/1.02  --demod_completeness_check              fast
% 2.18/1.02  --demod_use_ground                      true
% 2.18/1.02  --sup_to_prop_solver                    passive
% 2.18/1.02  --sup_prop_simpl_new                    true
% 2.18/1.02  --sup_prop_simpl_given                  true
% 2.18/1.02  --sup_fun_splitting                     false
% 2.18/1.02  --sup_smt_interval                      50000
% 2.18/1.02  
% 2.18/1.02  ------ Superposition Simplification Setup
% 2.18/1.02  
% 2.18/1.02  --sup_indices_passive                   []
% 2.18/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.18/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.02  --sup_full_bw                           [BwDemod]
% 2.18/1.02  --sup_immed_triv                        [TrivRules]
% 2.18/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.18/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.02  --sup_immed_bw_main                     []
% 2.18/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.18/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/1.02  
% 2.18/1.02  ------ Combination Options
% 2.18/1.02  
% 2.18/1.02  --comb_res_mult                         3
% 2.18/1.02  --comb_sup_mult                         2
% 2.18/1.02  --comb_inst_mult                        10
% 2.18/1.02  
% 2.18/1.02  ------ Debug Options
% 2.18/1.02  
% 2.18/1.02  --dbg_backtrace                         false
% 2.18/1.02  --dbg_dump_prop_clauses                 false
% 2.18/1.02  --dbg_dump_prop_clauses_file            -
% 2.18/1.02  --dbg_out_stat                          false
% 2.18/1.02  
% 2.18/1.02  
% 2.18/1.02  
% 2.18/1.02  
% 2.18/1.02  ------ Proving...
% 2.18/1.02  
% 2.18/1.02  
% 2.18/1.02  % SZS status Theorem for theBenchmark.p
% 2.18/1.02  
% 2.18/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.18/1.02  
% 2.18/1.02  fof(f11,conjecture,(
% 2.18/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 2.18/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.02  
% 2.18/1.02  fof(f12,negated_conjecture,(
% 2.18/1.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1))))),
% 2.18/1.02    inference(negated_conjecture,[],[f11])).
% 2.18/1.02  
% 2.18/1.02  fof(f22,plain,(
% 2.18/1.02    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.18/1.02    inference(ennf_transformation,[],[f12])).
% 2.18/1.02  
% 2.18/1.02  fof(f23,plain,(
% 2.18/1.02    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.18/1.02    inference(flattening,[],[f22])).
% 2.18/1.02  
% 2.18/1.02  fof(f24,plain,(
% 2.18/1.02    ? [X0] : (? [X1] : (((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.18/1.02    inference(nnf_transformation,[],[f23])).
% 2.18/1.02  
% 2.18/1.02  fof(f25,plain,(
% 2.18/1.02    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.18/1.02    inference(flattening,[],[f24])).
% 2.18/1.02  
% 2.18/1.02  fof(f27,plain,(
% 2.18/1.02    ( ! [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) != k2_tops_1(X0,sK1) | ~v4_pre_topc(sK1,X0)) & (k7_subset_1(u1_struct_0(X0),sK1,k1_tops_1(X0,sK1)) = k2_tops_1(X0,sK1) | v4_pre_topc(sK1,X0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.18/1.02    introduced(choice_axiom,[])).
% 2.18/1.02  
% 2.18/1.02  fof(f26,plain,(
% 2.18/1.02    ? [X0] : (? [X1] : ((k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) != k2_tops_1(X0,X1) | ~v4_pre_topc(X1,X0)) & (k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) != k2_tops_1(sK0,X1) | ~v4_pre_topc(X1,sK0)) & (k7_subset_1(u1_struct_0(sK0),X1,k1_tops_1(sK0,X1)) = k2_tops_1(sK0,X1) | v4_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.18/1.02    introduced(choice_axiom,[])).
% 2.18/1.02  
% 2.18/1.02  fof(f28,plain,(
% 2.18/1.02    ((k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)) & (k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.18/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f27,f26])).
% 2.18/1.02  
% 2.18/1.02  fof(f43,plain,(
% 2.18/1.02    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) | v4_pre_topc(sK1,sK0)),
% 2.18/1.02    inference(cnf_transformation,[],[f28])).
% 2.18/1.02  
% 2.18/1.02  fof(f7,axiom,(
% 2.18/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.18/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.02  
% 2.18/1.02  fof(f16,plain,(
% 2.18/1.02    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.18/1.02    inference(ennf_transformation,[],[f7])).
% 2.18/1.02  
% 2.18/1.02  fof(f17,plain,(
% 2.18/1.02    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.18/1.02    inference(flattening,[],[f16])).
% 2.18/1.02  
% 2.18/1.02  fof(f35,plain,(
% 2.18/1.02    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.18/1.02    inference(cnf_transformation,[],[f17])).
% 2.18/1.02  
% 2.18/1.02  fof(f41,plain,(
% 2.18/1.02    l1_pre_topc(sK0)),
% 2.18/1.02    inference(cnf_transformation,[],[f28])).
% 2.18/1.02  
% 2.18/1.02  fof(f42,plain,(
% 2.18/1.02    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.18/1.02    inference(cnf_transformation,[],[f28])).
% 2.18/1.02  
% 2.18/1.02  fof(f6,axiom,(
% 2.18/1.02    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 2.18/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.02  
% 2.18/1.02  fof(f15,plain,(
% 2.18/1.02    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.18/1.02    inference(ennf_transformation,[],[f6])).
% 2.18/1.02  
% 2.18/1.02  fof(f34,plain,(
% 2.18/1.02    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.18/1.02    inference(cnf_transformation,[],[f15])).
% 2.18/1.02  
% 2.18/1.02  fof(f1,axiom,(
% 2.18/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.18/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.02  
% 2.18/1.02  fof(f29,plain,(
% 2.18/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.18/1.02    inference(cnf_transformation,[],[f1])).
% 2.18/1.02  
% 2.18/1.02  fof(f2,axiom,(
% 2.18/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.18/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.02  
% 2.18/1.02  fof(f30,plain,(
% 2.18/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.18/1.02    inference(cnf_transformation,[],[f2])).
% 2.18/1.02  
% 2.18/1.02  fof(f4,axiom,(
% 2.18/1.02    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 2.18/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.02  
% 2.18/1.02  fof(f32,plain,(
% 2.18/1.02    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 2.18/1.02    inference(cnf_transformation,[],[f4])).
% 2.18/1.02  
% 2.18/1.02  fof(f3,axiom,(
% 2.18/1.02    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.18/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.02  
% 2.18/1.02  fof(f31,plain,(
% 2.18/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.18/1.02    inference(cnf_transformation,[],[f3])).
% 2.18/1.02  
% 2.18/1.02  fof(f45,plain,(
% 2.18/1.02    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 2.18/1.02    inference(definition_unfolding,[],[f32,f31])).
% 2.18/1.02  
% 2.18/1.02  fof(f8,axiom,(
% 2.18/1.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.18/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.02  
% 2.18/1.02  fof(f18,plain,(
% 2.18/1.02    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.18/1.02    inference(ennf_transformation,[],[f8])).
% 2.18/1.02  
% 2.18/1.02  fof(f19,plain,(
% 2.18/1.02    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.18/1.02    inference(flattening,[],[f18])).
% 2.18/1.02  
% 2.18/1.02  fof(f37,plain,(
% 2.18/1.02    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.18/1.02    inference(cnf_transformation,[],[f19])).
% 2.18/1.02  
% 2.18/1.02  fof(f5,axiom,(
% 2.18/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 2.18/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.02  
% 2.18/1.02  fof(f13,plain,(
% 2.18/1.02    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.18/1.02    inference(ennf_transformation,[],[f5])).
% 2.18/1.02  
% 2.18/1.02  fof(f14,plain,(
% 2.18/1.02    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.18/1.02    inference(flattening,[],[f13])).
% 2.18/1.02  
% 2.18/1.02  fof(f33,plain,(
% 2.18/1.02    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.18/1.02    inference(cnf_transformation,[],[f14])).
% 2.18/1.02  
% 2.18/1.02  fof(f10,axiom,(
% 2.18/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1)))),
% 2.18/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.02  
% 2.18/1.02  fof(f21,plain,(
% 2.18/1.02    ! [X0] : (! [X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.18/1.02    inference(ennf_transformation,[],[f10])).
% 2.18/1.02  
% 2.18/1.02  fof(f39,plain,(
% 2.18/1.02    ( ! [X0,X1] : (k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) = k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.18/1.02    inference(cnf_transformation,[],[f21])).
% 2.18/1.02  
% 2.18/1.02  fof(f9,axiom,(
% 2.18/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1)))),
% 2.18/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.02  
% 2.18/1.02  fof(f20,plain,(
% 2.18/1.02    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.18/1.02    inference(ennf_transformation,[],[f9])).
% 2.18/1.02  
% 2.18/1.02  fof(f38,plain,(
% 2.18/1.02    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) = k2_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.18/1.02    inference(cnf_transformation,[],[f20])).
% 2.18/1.02  
% 2.18/1.02  fof(f44,plain,(
% 2.18/1.02    k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) | ~v4_pre_topc(sK1,sK0)),
% 2.18/1.02    inference(cnf_transformation,[],[f28])).
% 2.18/1.02  
% 2.18/1.02  fof(f36,plain,(
% 2.18/1.02    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.18/1.02    inference(cnf_transformation,[],[f17])).
% 2.18/1.02  
% 2.18/1.02  fof(f40,plain,(
% 2.18/1.02    v2_pre_topc(sK0)),
% 2.18/1.02    inference(cnf_transformation,[],[f28])).
% 2.18/1.02  
% 2.18/1.02  cnf(c_11,negated_conjecture,
% 2.18/1.02      ( v4_pre_topc(sK1,sK0)
% 2.18/1.02      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 2.18/1.02      inference(cnf_transformation,[],[f43]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_97,plain,
% 2.18/1.02      ( v4_pre_topc(sK1,sK0)
% 2.18/1.02      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 2.18/1.02      inference(prop_impl,[status(thm)],[c_11]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_6,plain,
% 2.18/1.02      ( ~ v4_pre_topc(X0,X1)
% 2.18/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/1.02      | ~ l1_pre_topc(X1)
% 2.18/1.02      | k2_pre_topc(X1,X0) = X0 ),
% 2.18/1.02      inference(cnf_transformation,[],[f35]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_13,negated_conjecture,
% 2.18/1.02      ( l1_pre_topc(sK0) ),
% 2.18/1.02      inference(cnf_transformation,[],[f41]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_237,plain,
% 2.18/1.02      ( ~ v4_pre_topc(X0,X1)
% 2.18/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/1.02      | k2_pre_topc(X1,X0) = X0
% 2.18/1.02      | sK0 != X1 ),
% 2.18/1.02      inference(resolution_lifted,[status(thm)],[c_6,c_13]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_238,plain,
% 2.18/1.02      ( ~ v4_pre_topc(X0,sK0)
% 2.18/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.18/1.02      | k2_pre_topc(sK0,X0) = X0 ),
% 2.18/1.02      inference(unflattening,[status(thm)],[c_237]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_267,plain,
% 2.18/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.18/1.02      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 2.18/1.02      | k2_pre_topc(sK0,X0) = X0
% 2.18/1.02      | sK1 != X0
% 2.18/1.02      | sK0 != sK0 ),
% 2.18/1.02      inference(resolution_lifted,[status(thm)],[c_97,c_238]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_268,plain,
% 2.18/1.02      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.18/1.02      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 2.18/1.02      | k2_pre_topc(sK0,sK1) = sK1 ),
% 2.18/1.02      inference(unflattening,[status(thm)],[c_267]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_12,negated_conjecture,
% 2.18/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.18/1.02      inference(cnf_transformation,[],[f42]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_270,plain,
% 2.18/1.02      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 2.18/1.02      | k2_pre_topc(sK0,sK1) = sK1 ),
% 2.18/1.02      inference(global_propositional_subsumption,
% 2.18/1.02                [status(thm)],
% 2.18/1.02                [c_268,c_12]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_317,plain,
% 2.18/1.02      ( k2_pre_topc(sK0,sK1) = sK1
% 2.18/1.02      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 2.18/1.02      inference(prop_impl,[status(thm)],[c_270]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_318,plain,
% 2.18/1.02      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1)
% 2.18/1.02      | k2_pre_topc(sK0,sK1) = sK1 ),
% 2.18/1.02      inference(renaming,[status(thm)],[c_317]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_583,plain,
% 2.18/1.02      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_4,plain,
% 2.18/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.18/1.02      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 2.18/1.02      inference(cnf_transformation,[],[f34]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_584,plain,
% 2.18/1.02      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
% 2.18/1.02      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1567,plain,
% 2.18/1.02      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) ),
% 2.18/1.02      inference(superposition,[status(thm)],[c_583,c_584]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1706,plain,
% 2.18/1.02      ( k2_pre_topc(sK0,sK1) = sK1
% 2.18/1.02      | k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 2.18/1.02      inference(superposition,[status(thm)],[c_318,c_1567]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_0,plain,
% 2.18/1.02      ( k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
% 2.18/1.02      inference(cnf_transformation,[],[f29]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1,plain,
% 2.18/1.02      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
% 2.18/1.02      inference(cnf_transformation,[],[f30]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_2,plain,
% 2.18/1.02      ( k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
% 2.18/1.02      inference(cnf_transformation,[],[f45]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_946,plain,
% 2.18/1.02      ( k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
% 2.18/1.02      inference(superposition,[status(thm)],[c_0,c_2]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1007,plain,
% 2.18/1.02      ( k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
% 2.18/1.02      inference(superposition,[status(thm)],[c_1,c_946]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_1499,plain,
% 2.18/1.02      ( k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 2.18/1.02      inference(superposition,[status(thm)],[c_0,c_1007]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_2421,plain,
% 2.18/1.02      ( k2_pre_topc(sK0,sK1) = sK1
% 2.18/1.02      | k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = sK1 ),
% 2.18/1.02      inference(superposition,[status(thm)],[c_1706,c_1499]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_7,plain,
% 2.18/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/1.02      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/1.02      | ~ l1_pre_topc(X1) ),
% 2.18/1.02      inference(cnf_transformation,[],[f37]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_225,plain,
% 2.18/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/1.02      | m1_subset_1(k2_tops_1(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/1.02      | sK0 != X1 ),
% 2.18/1.02      inference(resolution_lifted,[status(thm)],[c_7,c_13]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_226,plain,
% 2.18/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.18/1.02      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
% 2.18/1.02      inference(unflattening,[status(thm)],[c_225]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_580,plain,
% 2.18/1.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 2.18/1.02      | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_226]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_3,plain,
% 2.18/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.18/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.18/1.02      | k4_subset_1(X1,X2,X0) = k2_xboole_0(X2,X0) ),
% 2.18/1.02      inference(cnf_transformation,[],[f33]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_585,plain,
% 2.18/1.02      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
% 2.18/1.02      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 2.18/1.02      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_2202,plain,
% 2.18/1.02      ( k4_subset_1(u1_struct_0(sK0),sK1,X0) = k2_xboole_0(sK1,X0)
% 2.18/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.18/1.02      inference(superposition,[status(thm)],[c_583,c_585]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_2588,plain,
% 2.18/1.02      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,X0)) = k2_xboole_0(sK1,k2_tops_1(sK0,X0))
% 2.18/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.18/1.02      inference(superposition,[status(thm)],[c_580,c_2202]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_2692,plain,
% 2.18/1.02      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
% 2.18/1.02      inference(superposition,[status(thm)],[c_583,c_2588]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_9,plain,
% 2.18/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/1.02      | ~ l1_pre_topc(X1)
% 2.18/1.02      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0) ),
% 2.18/1.02      inference(cnf_transformation,[],[f39]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_201,plain,
% 2.18/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/1.02      | k4_subset_1(u1_struct_0(X1),X0,k2_tops_1(X1,X0)) = k2_pre_topc(X1,X0)
% 2.18/1.02      | sK0 != X1 ),
% 2.18/1.02      inference(resolution_lifted,[status(thm)],[c_9,c_13]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_202,plain,
% 2.18/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.18/1.02      | k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0) ),
% 2.18/1.02      inference(unflattening,[status(thm)],[c_201]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_582,plain,
% 2.18/1.02      ( k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) = k2_pre_topc(sK0,X0)
% 2.18/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_202]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_666,plain,
% 2.18/1.02      ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 2.18/1.02      inference(superposition,[status(thm)],[c_583,c_582]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_2699,plain,
% 2.18/1.02      ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
% 2.18/1.02      inference(light_normalisation,[status(thm)],[c_2692,c_666]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_3466,plain,
% 2.18/1.02      ( k2_pre_topc(sK0,sK1) = sK1 ),
% 2.18/1.02      inference(demodulation,[status(thm)],[c_2421,c_2699]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_8,plain,
% 2.18/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/1.02      | ~ l1_pre_topc(X1)
% 2.18/1.02      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0) ),
% 2.18/1.02      inference(cnf_transformation,[],[f38]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_213,plain,
% 2.18/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/1.02      | k7_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0),k1_tops_1(X1,X0)) = k2_tops_1(X1,X0)
% 2.18/1.02      | sK0 != X1 ),
% 2.18/1.02      inference(resolution_lifted,[status(thm)],[c_8,c_13]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_214,plain,
% 2.18/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.18/1.02      | k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0) ),
% 2.18/1.02      inference(unflattening,[status(thm)],[c_213]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_581,plain,
% 2.18/1.02      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k1_tops_1(sK0,X0)) = k2_tops_1(sK0,X0)
% 2.18/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 2.18/1.02      inference(predicate_to_equality,[status(thm)],[c_214]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_731,plain,
% 2.18/1.02      ( k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 2.18/1.02      inference(superposition,[status(thm)],[c_583,c_581]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_3470,plain,
% 2.18/1.02      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) = k2_tops_1(sK0,sK1) ),
% 2.18/1.02      inference(demodulation,[status(thm)],[c_3466,c_731]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_10,negated_conjecture,
% 2.18/1.02      ( ~ v4_pre_topc(sK1,sK0)
% 2.18/1.02      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 2.18/1.02      inference(cnf_transformation,[],[f44]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_95,plain,
% 2.18/1.02      ( ~ v4_pre_topc(sK1,sK0)
% 2.18/1.02      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1) ),
% 2.18/1.02      inference(prop_impl,[status(thm)],[c_10]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_5,plain,
% 2.18/1.02      ( v4_pre_topc(X0,X1)
% 2.18/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/1.02      | ~ l1_pre_topc(X1)
% 2.18/1.02      | ~ v2_pre_topc(X1)
% 2.18/1.02      | k2_pre_topc(X1,X0) != X0 ),
% 2.18/1.02      inference(cnf_transformation,[],[f36]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_14,negated_conjecture,
% 2.18/1.02      ( v2_pre_topc(sK0) ),
% 2.18/1.02      inference(cnf_transformation,[],[f40]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_176,plain,
% 2.18/1.02      ( v4_pre_topc(X0,X1)
% 2.18/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/1.02      | ~ l1_pre_topc(X1)
% 2.18/1.02      | k2_pre_topc(X1,X0) != X0
% 2.18/1.02      | sK0 != X1 ),
% 2.18/1.02      inference(resolution_lifted,[status(thm)],[c_5,c_14]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_177,plain,
% 2.18/1.02      ( v4_pre_topc(X0,sK0)
% 2.18/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.18/1.02      | ~ l1_pre_topc(sK0)
% 2.18/1.02      | k2_pre_topc(sK0,X0) != X0 ),
% 2.18/1.02      inference(unflattening,[status(thm)],[c_176]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_181,plain,
% 2.18/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.18/1.02      | v4_pre_topc(X0,sK0)
% 2.18/1.02      | k2_pre_topc(sK0,X0) != X0 ),
% 2.18/1.02      inference(global_propositional_subsumption,
% 2.18/1.02                [status(thm)],
% 2.18/1.02                [c_177,c_13]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_182,plain,
% 2.18/1.02      ( v4_pre_topc(X0,sK0)
% 2.18/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.18/1.02      | k2_pre_topc(sK0,X0) != X0 ),
% 2.18/1.02      inference(renaming,[status(thm)],[c_181]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_278,plain,
% 2.18/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.18/1.02      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 2.18/1.02      | k2_pre_topc(sK0,X0) != X0
% 2.18/1.02      | sK1 != X0
% 2.18/1.02      | sK0 != sK0 ),
% 2.18/1.02      inference(resolution_lifted,[status(thm)],[c_95,c_182]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_279,plain,
% 2.18/1.02      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.18/1.02      | k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 2.18/1.02      | k2_pre_topc(sK0,sK1) != sK1 ),
% 2.18/1.02      inference(unflattening,[status(thm)],[c_278]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(c_281,plain,
% 2.18/1.02      ( k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) != k2_tops_1(sK0,sK1)
% 2.18/1.02      | k2_pre_topc(sK0,sK1) != sK1 ),
% 2.18/1.02      inference(global_propositional_subsumption,
% 2.18/1.02                [status(thm)],
% 2.18/1.02                [c_279,c_12]) ).
% 2.18/1.02  
% 2.18/1.02  cnf(contradiction,plain,
% 2.18/1.02      ( $false ),
% 2.18/1.02      inference(minisat,[status(thm)],[c_3470,c_3466,c_281]) ).
% 2.18/1.02  
% 2.18/1.02  
% 2.18/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.18/1.02  
% 2.18/1.02  ------                               Statistics
% 2.18/1.02  
% 2.18/1.02  ------ General
% 2.18/1.02  
% 2.18/1.02  abstr_ref_over_cycles:                  0
% 2.18/1.02  abstr_ref_under_cycles:                 0
% 2.18/1.02  gc_basic_clause_elim:                   0
% 2.18/1.02  forced_gc_time:                         0
% 2.18/1.02  parsing_time:                           0.006
% 2.18/1.02  unif_index_cands_time:                  0.
% 2.18/1.02  unif_index_add_time:                    0.
% 2.18/1.02  orderings_time:                         0.
% 2.18/1.02  out_proof_time:                         0.008
% 2.18/1.02  total_time:                             0.113
% 2.18/1.02  num_of_symbols:                         46
% 2.18/1.02  num_of_terms:                           3590
% 2.18/1.02  
% 2.18/1.02  ------ Preprocessing
% 2.18/1.02  
% 2.18/1.02  num_of_splits:                          0
% 2.18/1.02  num_of_split_atoms:                     0
% 2.18/1.02  num_of_reused_defs:                     0
% 2.18/1.02  num_eq_ax_congr_red:                    8
% 2.18/1.02  num_of_sem_filtered_clauses:            1
% 2.18/1.02  num_of_subtypes:                        0
% 2.18/1.02  monotx_restored_types:                  0
% 2.18/1.02  sat_num_of_epr_types:                   0
% 2.18/1.02  sat_num_of_non_cyclic_types:            0
% 2.18/1.02  sat_guarded_non_collapsed_types:        0
% 2.18/1.02  num_pure_diseq_elim:                    0
% 2.18/1.02  simp_replaced_by:                       0
% 2.18/1.02  res_preprocessed:                       73
% 2.18/1.02  prep_upred:                             0
% 2.18/1.02  prep_unflattend:                        7
% 2.18/1.02  smt_new_axioms:                         0
% 2.18/1.02  pred_elim_cands:                        1
% 2.18/1.02  pred_elim:                              3
% 2.18/1.02  pred_elim_cl:                           4
% 2.18/1.02  pred_elim_cycles:                       5
% 2.18/1.02  merged_defs:                            8
% 2.18/1.02  merged_defs_ncl:                        0
% 2.18/1.02  bin_hyper_res:                          8
% 2.18/1.02  prep_cycles:                            4
% 2.18/1.02  pred_elim_time:                         0.001
% 2.18/1.02  splitting_time:                         0.
% 2.18/1.02  sem_filter_time:                        0.
% 2.18/1.02  monotx_time:                            0.
% 2.18/1.02  subtype_inf_time:                       0.
% 2.18/1.02  
% 2.18/1.02  ------ Problem properties
% 2.18/1.02  
% 2.18/1.02  clauses:                                11
% 2.18/1.02  conjectures:                            1
% 2.18/1.02  epr:                                    0
% 2.18/1.02  horn:                                   10
% 2.18/1.02  ground:                                 3
% 2.18/1.02  unary:                                  4
% 2.18/1.02  binary:                                 6
% 2.18/1.02  lits:                                   19
% 2.18/1.02  lits_eq:                                11
% 2.18/1.02  fd_pure:                                0
% 2.18/1.02  fd_pseudo:                              0
% 2.18/1.02  fd_cond:                                0
% 2.18/1.02  fd_pseudo_cond:                         0
% 2.18/1.02  ac_symbols:                             0
% 2.18/1.02  
% 2.18/1.02  ------ Propositional Solver
% 2.18/1.02  
% 2.18/1.02  prop_solver_calls:                      27
% 2.18/1.02  prop_fast_solver_calls:                 421
% 2.18/1.02  smt_solver_calls:                       0
% 2.18/1.02  smt_fast_solver_calls:                  0
% 2.18/1.02  prop_num_of_clauses:                    1678
% 2.18/1.02  prop_preprocess_simplified:             4186
% 2.18/1.02  prop_fo_subsumed:                       3
% 2.18/1.02  prop_solver_time:                       0.
% 2.18/1.02  smt_solver_time:                        0.
% 2.18/1.02  smt_fast_solver_time:                   0.
% 2.18/1.02  prop_fast_solver_time:                  0.
% 2.18/1.02  prop_unsat_core_time:                   0.
% 2.18/1.02  
% 2.18/1.02  ------ QBF
% 2.18/1.02  
% 2.18/1.02  qbf_q_res:                              0
% 2.18/1.02  qbf_num_tautologies:                    0
% 2.18/1.02  qbf_prep_cycles:                        0
% 2.18/1.02  
% 2.18/1.02  ------ BMC1
% 2.18/1.02  
% 2.18/1.02  bmc1_current_bound:                     -1
% 2.18/1.02  bmc1_last_solved_bound:                 -1
% 2.18/1.02  bmc1_unsat_core_size:                   -1
% 2.18/1.02  bmc1_unsat_core_parents_size:           -1
% 2.18/1.02  bmc1_merge_next_fun:                    0
% 2.18/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.18/1.02  
% 2.18/1.02  ------ Instantiation
% 2.18/1.02  
% 2.18/1.02  inst_num_of_clauses:                    519
% 2.18/1.02  inst_num_in_passive:                    193
% 2.18/1.02  inst_num_in_active:                     245
% 2.18/1.02  inst_num_in_unprocessed:                81
% 2.18/1.02  inst_num_of_loops:                      260
% 2.18/1.02  inst_num_of_learning_restarts:          0
% 2.18/1.02  inst_num_moves_active_passive:          11
% 2.18/1.02  inst_lit_activity:                      0
% 2.18/1.02  inst_lit_activity_moves:                0
% 2.18/1.02  inst_num_tautologies:                   0
% 2.18/1.02  inst_num_prop_implied:                  0
% 2.18/1.02  inst_num_existing_simplified:           0
% 2.18/1.02  inst_num_eq_res_simplified:             0
% 2.18/1.02  inst_num_child_elim:                    0
% 2.18/1.02  inst_num_of_dismatching_blockings:      34
% 2.18/1.02  inst_num_of_non_proper_insts:           337
% 2.18/1.02  inst_num_of_duplicates:                 0
% 2.18/1.02  inst_inst_num_from_inst_to_res:         0
% 2.18/1.02  inst_dismatching_checking_time:         0.
% 2.18/1.02  
% 2.18/1.02  ------ Resolution
% 2.18/1.02  
% 2.18/1.02  res_num_of_clauses:                     0
% 2.18/1.02  res_num_in_passive:                     0
% 2.18/1.02  res_num_in_active:                      0
% 2.18/1.02  res_num_of_loops:                       77
% 2.18/1.02  res_forward_subset_subsumed:            19
% 2.18/1.02  res_backward_subset_subsumed:           0
% 2.18/1.02  res_forward_subsumed:                   0
% 2.18/1.02  res_backward_subsumed:                  0
% 2.18/1.02  res_forward_subsumption_resolution:     0
% 2.18/1.02  res_backward_subsumption_resolution:    0
% 2.18/1.02  res_clause_to_clause_subsumption:       213
% 2.18/1.02  res_orphan_elimination:                 0
% 2.18/1.02  res_tautology_del:                      42
% 2.18/1.02  res_num_eq_res_simplified:              0
% 2.18/1.02  res_num_sel_changes:                    0
% 2.18/1.02  res_moves_from_active_to_pass:          0
% 2.18/1.02  
% 2.18/1.02  ------ Superposition
% 2.18/1.02  
% 2.18/1.02  sup_time_total:                         0.
% 2.18/1.02  sup_time_generating:                    0.
% 2.18/1.02  sup_time_sim_full:                      0.
% 2.18/1.02  sup_time_sim_immed:                     0.
% 2.18/1.02  
% 2.18/1.02  sup_num_of_clauses:                     50
% 2.18/1.02  sup_num_in_active:                      39
% 2.18/1.02  sup_num_in_passive:                     11
% 2.18/1.02  sup_num_of_loops:                       50
% 2.18/1.02  sup_fw_superposition:                   49
% 2.18/1.02  sup_bw_superposition:                   22
% 2.18/1.02  sup_immediate_simplified:               3
% 2.18/1.02  sup_given_eliminated:                   0
% 2.18/1.02  comparisons_done:                       0
% 2.18/1.02  comparisons_avoided:                    12
% 2.18/1.02  
% 2.18/1.02  ------ Simplifications
% 2.18/1.02  
% 2.18/1.02  
% 2.18/1.02  sim_fw_subset_subsumed:                 0
% 2.18/1.02  sim_bw_subset_subsumed:                 6
% 2.18/1.02  sim_fw_subsumed:                        0
% 2.18/1.02  sim_bw_subsumed:                        0
% 2.18/1.02  sim_fw_subsumption_res:                 0
% 2.18/1.02  sim_bw_subsumption_res:                 0
% 2.18/1.02  sim_tautology_del:                      1
% 2.18/1.02  sim_eq_tautology_del:                   0
% 2.18/1.02  sim_eq_res_simp:                        1
% 2.18/1.02  sim_fw_demodulated:                     3
% 2.18/1.02  sim_bw_demodulated:                     5
% 2.18/1.02  sim_light_normalised:                   1
% 2.18/1.02  sim_joinable_taut:                      0
% 2.18/1.02  sim_joinable_simp:                      0
% 2.18/1.02  sim_ac_normalised:                      0
% 2.18/1.02  sim_smt_subsumption:                    0
% 2.18/1.02  
%------------------------------------------------------------------------------
