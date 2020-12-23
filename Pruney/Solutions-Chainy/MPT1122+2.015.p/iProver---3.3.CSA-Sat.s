%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:38 EST 2020

% Result     : CounterSatisfiable 4.05s
% Output     : Saturation 4.05s
% Verified   : 
% Statistics : Number of formulae       :  187 (1816 expanded)
%              Number of clauses        :  139 ( 682 expanded)
%              Number of leaves         :   17 ( 411 expanded)
%              Depth                    :   14
%              Number of atoms          :  574 (6308 expanded)
%              Number of equality atoms :  406 (2443 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f28,f34])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f30,f49])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f12,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
                & v2_pre_topc(X0) )
             => v3_pre_topc(X1,X0) )
            & ( v3_pre_topc(X1,X0)
             => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
                  & v2_pre_topc(X0) )
               => v3_pre_topc(X1,X0) )
              & ( v3_pre_topc(X1,X0)
               => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ~ v3_pre_topc(X1,X0)
              & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              & v2_pre_topc(X0) )
            | ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              & v3_pre_topc(X1,X0) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ~ v3_pre_topc(X1,X0)
              & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              & v2_pre_topc(X0) )
            | ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              & v3_pre_topc(X1,X0) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ( ~ v3_pre_topc(X1,X0)
              & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              & v2_pre_topc(X0) )
            | ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              & v3_pre_topc(X1,X0) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ( ~ v3_pre_topc(sK1,X0)
            & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1))
            & v2_pre_topc(X0) )
          | ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1))
            & v3_pre_topc(sK1,X0) ) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ( ~ v3_pre_topc(X1,X0)
                & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
                & v2_pre_topc(X0) )
              | ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
                & v3_pre_topc(X1,X0) ) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ( ~ v3_pre_topc(X1,sK0)
              & k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1))
              & v2_pre_topc(sK0) )
            | ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1))
              & v3_pre_topc(X1,sK0) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ( ( ~ v3_pre_topc(sK1,sK0)
        & k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))
        & v2_pre_topc(sK0) )
      | ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))
        & v3_pre_topc(sK1,sK0) ) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f26,f25])).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f33,f49])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f43,plain,
    ( v2_pre_topc(sK0)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_181,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_9612,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ iProver_ARSWP_78
    | arAF0_k5_xboole_0_0 = arAF0_k3_subset_1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_1])).

cnf(c_2,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_2818,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

cnf(c_2823,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2818,c_0])).

cnf(c_2858,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2823])).

cnf(c_2860,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_2858])).

cnf(c_9634,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ iProver_ARSWP_78
    | arAF0_k5_xboole_0_0 = arAF0_k3_subset_1_0 ),
    inference(instantiation,[status(thm)],[c_9612])).

cnf(c_9788,plain,
    ( ~ iProver_ARSWP_78
    | arAF0_k5_xboole_0_0 = arAF0_k3_subset_1_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9612,c_2860,c_9634])).

cnf(c_9873,plain,
    ( arAF0_k5_xboole_0_0 = arAF0_k3_subset_1_0
    | iProver_ARSWP_78 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9788])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_9883,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_9613,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(X1))
    | ~ iProver_ARSWP_79 ),
    inference(arg_filter_abstr,[status(unp)],[c_3])).

cnf(c_9877,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(X1)) = iProver_top
    | iProver_ARSWP_79 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9613])).

cnf(c_10419,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | iProver_ARSWP_79 != iProver_top ),
    inference(superposition,[status(thm)],[c_9883,c_9877])).

cnf(c_10719,plain,
    ( m1_subset_1(arAF0_k5_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | iProver_ARSWP_79 != iProver_top
    | iProver_ARSWP_78 != iProver_top ),
    inference(superposition,[status(thm)],[c_9873,c_10419])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1)
    | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_9889,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_10865,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0)) = arAF0_k5_xboole_0_0
    | l1_struct_0(sK0) != iProver_top
    | iProver_ARSWP_79 != iProver_top
    | iProver_ARSWP_78 != iProver_top ),
    inference(superposition,[status(thm)],[c_10719,c_9889])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_19,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_35,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_37,plain,
    ( l1_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_12236,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0)) = arAF0_k5_xboole_0_0
    | iProver_ARSWP_79 != iProver_top
    | iProver_ARSWP_78 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10865,c_19,c_37])).

cnf(c_6,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
    | ~ v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_9891,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) = iProver_top
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_12245,plain,
    ( v3_pre_topc(arAF0_k5_xboole_0_0,sK0) = iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),sK0) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | iProver_ARSWP_79 != iProver_top
    | iProver_ARSWP_78 != iProver_top ),
    inference(superposition,[status(thm)],[c_12236,c_9891])).

cnf(c_13863,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),sK0) != iProver_top
    | v3_pre_topc(arAF0_k5_xboole_0_0,sK0) = iProver_top
    | iProver_ARSWP_79 != iProver_top
    | iProver_ARSWP_78 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12245,c_19])).

cnf(c_13864,plain,
    ( v3_pre_topc(arAF0_k5_xboole_0_0,sK0) = iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),sK0) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | iProver_ARSWP_79 != iProver_top
    | iProver_ARSWP_78 != iProver_top ),
    inference(renaming,[status(thm)],[c_13863])).

cnf(c_5,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
    | v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_9892,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) != iProver_top
    | v4_pre_topc(X1,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_12244,plain,
    ( v3_pre_topc(arAF0_k5_xboole_0_0,sK0) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),sK0) = iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | iProver_ARSWP_79 != iProver_top
    | iProver_ARSWP_78 != iProver_top ),
    inference(superposition,[status(thm)],[c_12236,c_9892])).

cnf(c_13853,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),sK0) = iProver_top
    | v3_pre_topc(arAF0_k5_xboole_0_0,sK0) != iProver_top
    | iProver_ARSWP_79 != iProver_top
    | iProver_ARSWP_78 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12244,c_19])).

cnf(c_13854,plain,
    ( v3_pre_topc(arAF0_k5_xboole_0_0,sK0) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),sK0) = iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | iProver_ARSWP_79 != iProver_top
    | iProver_ARSWP_78 != iProver_top ),
    inference(renaming,[status(thm)],[c_13853])).

cnf(c_9893,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_9900,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9893,c_0])).

cnf(c_10420,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(X0)) = iProver_top
    | iProver_ARSWP_79 != iProver_top ),
    inference(superposition,[status(thm)],[c_9900,c_9877])).

cnf(c_11422,plain,
    ( m1_subset_1(arAF0_k5_xboole_0_0,k1_zfmisc_1(X0)) = iProver_top
    | iProver_ARSWP_79 != iProver_top
    | iProver_ARSWP_78 != iProver_top ),
    inference(superposition,[status(thm)],[c_9873,c_10420])).

cnf(c_10,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_9887,plain,
    ( k2_pre_topc(X0,X1) = X1
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_13517,plain,
    ( k2_pre_topc(X0,arAF0_k5_xboole_0_0) = arAF0_k5_xboole_0_0
    | v4_pre_topc(arAF0_k5_xboole_0_0,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | iProver_ARSWP_79 != iProver_top
    | iProver_ARSWP_78 != iProver_top ),
    inference(superposition,[status(thm)],[c_11422,c_9887])).

cnf(c_13516,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),arAF0_k5_xboole_0_0)) = arAF0_k5_xboole_0_0
    | l1_struct_0(X0) != iProver_top
    | iProver_ARSWP_79 != iProver_top
    | iProver_ARSWP_78 != iProver_top ),
    inference(superposition,[status(thm)],[c_11422,c_9889])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_9614,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ iProver_ARSWP_80
    | arAF0_k5_xboole_0_0 = k7_subset_1(X1,X0,X2) ),
    inference(arg_filter_abstr,[status(unp)],[c_4])).

cnf(c_9876,plain,
    ( arAF0_k5_xboole_0_0 = k7_subset_1(X0,X1,X2)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | iProver_ARSWP_80 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9614])).

cnf(c_13515,plain,
    ( k7_subset_1(X0,arAF0_k5_xboole_0_0,X1) = arAF0_k5_xboole_0_0
    | iProver_ARSWP_80 != iProver_top
    | iProver_ARSWP_79 != iProver_top
    | iProver_ARSWP_78 != iProver_top ),
    inference(superposition,[status(thm)],[c_11422,c_9876])).

cnf(c_10720,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0)) = arAF0_k3_subset_1_0
    | l1_struct_0(sK0) != iProver_top
    | iProver_ARSWP_79 != iProver_top ),
    inference(superposition,[status(thm)],[c_10419,c_9889])).

cnf(c_11024,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0)) = arAF0_k3_subset_1_0
    | iProver_ARSWP_79 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10720,c_19,c_37])).

cnf(c_11030,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0)) = arAF0_k3_subset_1_0
    | iProver_ARSWP_79 != iProver_top
    | iProver_ARSWP_78 != iProver_top ),
    inference(superposition,[status(thm)],[c_9873,c_11024])).

cnf(c_12060,plain,
    ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) = iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),sK0) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | iProver_ARSWP_79 != iProver_top
    | iProver_ARSWP_78 != iProver_top ),
    inference(superposition,[status(thm)],[c_11030,c_9891])).

cnf(c_13502,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),sK0) != iProver_top
    | v3_pre_topc(arAF0_k3_subset_1_0,sK0) = iProver_top
    | iProver_ARSWP_79 != iProver_top
    | iProver_ARSWP_78 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12060,c_19])).

cnf(c_13503,plain,
    ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) = iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),sK0) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | iProver_ARSWP_79 != iProver_top
    | iProver_ARSWP_78 != iProver_top ),
    inference(renaming,[status(thm)],[c_13502])).

cnf(c_12059,plain,
    ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),sK0) = iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | iProver_ARSWP_79 != iProver_top
    | iProver_ARSWP_78 != iProver_top ),
    inference(superposition,[status(thm)],[c_11030,c_9892])).

cnf(c_13309,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),sK0) = iProver_top
    | v3_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
    | iProver_ARSWP_79 != iProver_top
    | iProver_ARSWP_78 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12059,c_19])).

cnf(c_13310,plain,
    ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),sK0) = iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | iProver_ARSWP_79 != iProver_top
    | iProver_ARSWP_78 != iProver_top ),
    inference(renaming,[status(thm)],[c_13309])).

cnf(c_9882,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9890,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_10435,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9882,c_9890])).

cnf(c_10548,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0))) = u1_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9900,c_9889])).

cnf(c_12409,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_10435,c_10548])).

cnf(c_12755,plain,
    ( v3_pre_topc(u1_struct_0(sK0),sK0) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),sK0) = iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12409,c_9892])).

cnf(c_12940,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),sK0) = iProver_top
    | v3_pre_topc(u1_struct_0(sK0),sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12755,c_19])).

cnf(c_12941,plain,
    ( v3_pre_topc(u1_struct_0(sK0),sK0) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),sK0) = iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_12940])).

cnf(c_11398,plain,
    ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),sK0) = iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | iProver_ARSWP_79 != iProver_top ),
    inference(superposition,[status(thm)],[c_11024,c_9892])).

cnf(c_12744,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),sK0) = iProver_top
    | v3_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
    | iProver_ARSWP_79 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11398,c_19])).

cnf(c_12745,plain,
    ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),sK0) = iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | iProver_ARSWP_79 != iProver_top ),
    inference(renaming,[status(thm)],[c_12744])).

cnf(c_12752,plain,
    ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),sK0) = iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | iProver_ARSWP_79 != iProver_top
    | iProver_ARSWP_78 != iProver_top ),
    inference(superposition,[status(thm)],[c_9873,c_12745])).

cnf(c_12246,plain,
    ( arAF0_k3_subset_1_0 = arAF0_k5_xboole_0_0
    | iProver_ARSWP_79 != iProver_top
    | iProver_ARSWP_78 != iProver_top ),
    inference(superposition,[status(thm)],[c_12236,c_11030])).

cnf(c_313,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_312,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_10465,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_313,c_312])).

cnf(c_12625,plain,
    ( ~ iProver_ARSWP_78
    | arAF0_k3_subset_1_0 = arAF0_k5_xboole_0_0 ),
    inference(resolution,[status(thm)],[c_10465,c_9788])).

cnf(c_12626,plain,
    ( arAF0_k3_subset_1_0 = arAF0_k5_xboole_0_0
    | iProver_ARSWP_78 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12625])).

cnf(c_13117,plain,
    ( arAF0_k3_subset_1_0 = arAF0_k5_xboole_0_0
    | iProver_ARSWP_78 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12246,c_12626])).

cnf(c_11424,plain,
    ( k2_pre_topc(X0,arAF0_k3_subset_1_0) = arAF0_k3_subset_1_0
    | v4_pre_topc(arAF0_k3_subset_1_0,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | iProver_ARSWP_79 != iProver_top ),
    inference(superposition,[status(thm)],[c_10420,c_9887])).

cnf(c_12603,plain,
    ( k2_pre_topc(X0,arAF0_k3_subset_1_0) = arAF0_k3_subset_1_0
    | v4_pre_topc(arAF0_k5_xboole_0_0,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | iProver_ARSWP_79 != iProver_top
    | iProver_ARSWP_78 != iProver_top ),
    inference(superposition,[status(thm)],[c_9873,c_11424])).

cnf(c_11031,plain,
    ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) = iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),sK0) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | iProver_ARSWP_79 != iProver_top ),
    inference(superposition,[status(thm)],[c_11024,c_9891])).

cnf(c_12281,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),sK0) != iProver_top
    | v3_pre_topc(arAF0_k3_subset_1_0,sK0) = iProver_top
    | iProver_ARSWP_79 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11031,c_19])).

cnf(c_12282,plain,
    ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) = iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),sK0) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | iProver_ARSWP_79 != iProver_top ),
    inference(renaming,[status(thm)],[c_12281])).

cnf(c_12289,plain,
    ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) = iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),sK0) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | iProver_ARSWP_79 != iProver_top
    | iProver_ARSWP_78 != iProver_top ),
    inference(superposition,[status(thm)],[c_9873,c_12282])).

cnf(c_10866,plain,
    ( k2_pre_topc(sK0,arAF0_k5_xboole_0_0) = arAF0_k5_xboole_0_0
    | v4_pre_topc(arAF0_k5_xboole_0_0,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | iProver_ARSWP_79 != iProver_top
    | iProver_ARSWP_78 != iProver_top ),
    inference(superposition,[status(thm)],[c_10719,c_9887])).

cnf(c_12088,plain,
    ( v4_pre_topc(arAF0_k5_xboole_0_0,sK0) != iProver_top
    | k2_pre_topc(sK0,arAF0_k5_xboole_0_0) = arAF0_k5_xboole_0_0
    | iProver_ARSWP_79 != iProver_top
    | iProver_ARSWP_78 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10866,c_19])).

cnf(c_12089,plain,
    ( k2_pre_topc(sK0,arAF0_k5_xboole_0_0) = arAF0_k5_xboole_0_0
    | v4_pre_topc(arAF0_k5_xboole_0_0,sK0) != iProver_top
    | iProver_ARSWP_79 != iProver_top
    | iProver_ARSWP_78 != iProver_top ),
    inference(renaming,[status(thm)],[c_12088])).

cnf(c_10547,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) = sK1
    | l1_struct_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9883,c_9889])).

cnf(c_36,plain,
    ( l1_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_8134,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_10856,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10547,c_18,c_17,c_36,c_8134])).

cnf(c_11397,plain,
    ( v3_pre_topc(sK1,sK0) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10856,c_9892])).

cnf(c_11789,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) = iProver_top
    | v3_pre_topc(sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11397,c_19])).

cnf(c_11790,plain,
    ( v3_pre_topc(sK1,sK0) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_11789])).

cnf(c_11597,plain,
    ( k7_subset_1(u1_struct_0(sK0),arAF0_k5_xboole_0_0,X0) = arAF0_k5_xboole_0_0
    | iProver_ARSWP_80 != iProver_top
    | iProver_ARSWP_79 != iProver_top
    | iProver_ARSWP_78 != iProver_top ),
    inference(superposition,[status(thm)],[c_10719,c_9876])).

cnf(c_11596,plain,
    ( k7_subset_1(X0,arAF0_k3_subset_1_0,X1) = arAF0_k5_xboole_0_0
    | iProver_ARSWP_80 != iProver_top
    | iProver_ARSWP_79 != iProver_top ),
    inference(superposition,[status(thm)],[c_10420,c_9876])).

cnf(c_11594,plain,
    ( k7_subset_1(X0,X0,X1) = arAF0_k5_xboole_0_0
    | iProver_ARSWP_80 != iProver_top ),
    inference(superposition,[status(thm)],[c_9900,c_9876])).

cnf(c_11593,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = arAF0_k5_xboole_0_0
    | iProver_ARSWP_80 != iProver_top ),
    inference(superposition,[status(thm)],[c_9883,c_9876])).

cnf(c_11423,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),arAF0_k3_subset_1_0)) = arAF0_k3_subset_1_0
    | l1_struct_0(X0) != iProver_top
    | iProver_ARSWP_79 != iProver_top ),
    inference(superposition,[status(thm)],[c_10420,c_9889])).

cnf(c_10721,plain,
    ( k2_pre_topc(sK0,arAF0_k3_subset_1_0) = arAF0_k3_subset_1_0
    | v4_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | iProver_ARSWP_79 != iProver_top ),
    inference(superposition,[status(thm)],[c_10419,c_9887])).

cnf(c_11014,plain,
    ( v4_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
    | k2_pre_topc(sK0,arAF0_k3_subset_1_0) = arAF0_k3_subset_1_0
    | iProver_ARSWP_79 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10721,c_19])).

cnf(c_11015,plain,
    ( k2_pre_topc(sK0,arAF0_k3_subset_1_0) = arAF0_k3_subset_1_0
    | v4_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
    | iProver_ARSWP_79 != iProver_top ),
    inference(renaming,[status(thm)],[c_11014])).

cnf(c_11021,plain,
    ( k2_pre_topc(sK0,arAF0_k3_subset_1_0) = arAF0_k3_subset_1_0
    | v4_pre_topc(arAF0_k5_xboole_0_0,sK0) != iProver_top
    | iProver_ARSWP_79 != iProver_top
    | iProver_ARSWP_78 != iProver_top ),
    inference(superposition,[status(thm)],[c_9873,c_11015])).

cnf(c_10525,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9883,c_9887])).

cnf(c_10746,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10525,c_19])).

cnf(c_10747,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10746])).

cnf(c_10526,plain,
    ( k2_pre_topc(X0,u1_struct_0(X0)) = u1_struct_0(X0)
    | v4_pre_topc(u1_struct_0(X0),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_9900,c_9887])).

cnf(c_12756,plain,
    ( v3_pre_topc(u1_struct_0(sK0),sK0) = iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),sK0) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12409,c_9891])).

cnf(c_8010,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_8016,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8298,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8010,c_8016])).

cnf(c_8018,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_8025,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8018,c_0])).

cnf(c_8015,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_8383,plain,
    ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0))) = u1_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8025,c_8015])).

cnf(c_8601,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) = u1_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_8298,c_8383])).

cnf(c_8017,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) = iProver_top
    | v4_pre_topc(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8603,plain,
    ( v3_pre_topc(u1_struct_0(sK0),sK0) = iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),sK0) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8601,c_8017])).

cnf(c_8709,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),sK0) != iProver_top
    | v3_pre_topc(u1_struct_0(sK0),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8603,c_19])).

cnf(c_8710,plain,
    ( v3_pre_topc(u1_struct_0(sK0),sK0) = iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),sK0) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8709])).

cnf(c_12948,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),sK0) != iProver_top
    | v3_pre_topc(u1_struct_0(sK0),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12756,c_19,c_8603])).

cnf(c_12949,plain,
    ( v3_pre_topc(u1_struct_0(sK0),sK0) = iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),sK0) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_12948])).

cnf(c_10859,plain,
    ( v3_pre_topc(sK1,sK0) = iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10856,c_9891])).

cnf(c_8011,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_8382,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) = sK1
    | l1_struct_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8011,c_8015])).

cnf(c_8484,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8382,c_18,c_17,c_36,c_8134])).

cnf(c_8487,plain,
    ( v3_pre_topc(sK1,sK0) = iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8484,c_8017])).

cnf(c_8701,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) != iProver_top
    | v3_pre_topc(sK1,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8487,c_19])).

cnf(c_8702,plain,
    ( v3_pre_topc(sK1,sK0) = iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_8701])).

cnf(c_11154,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) != iProver_top
    | v3_pre_topc(sK1,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10859,c_19,c_8487])).

cnf(c_11155,plain,
    ( v3_pre_topc(sK1,sK0) = iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_11154])).

cnf(c_9,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_9888,plain,
    ( k2_pre_topc(X0,X1) != X1
    | v4_pre_topc(X1,X0) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_pre_topc(X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_11,negated_conjecture,
    ( ~ v3_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_9886,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))
    | v3_pre_topc(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_14,negated_conjecture,
    ( v3_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_9885,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))
    | v3_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_16,negated_conjecture,
    ( v3_pre_topc(sK1,sK0)
    | v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_9884,plain,
    ( v3_pre_topc(sK1,sK0) = iProver_top
    | v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:59:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 4.05/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.05/1.00  
% 4.05/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.05/1.00  
% 4.05/1.00  ------  iProver source info
% 4.05/1.00  
% 4.05/1.00  git: date: 2020-06-30 10:37:57 +0100
% 4.05/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.05/1.00  git: non_committed_changes: false
% 4.05/1.00  git: last_make_outside_of_git: false
% 4.05/1.00  
% 4.05/1.00  ------ 
% 4.05/1.00  ------ Parsing...
% 4.05/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.05/1.00  
% 4.05/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 4.05/1.00  
% 4.05/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.05/1.00  
% 4.05/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.05/1.00  ------ Proving...
% 4.05/1.00  ------ Problem Properties 
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  clauses                                 16
% 4.05/1.00  conjectures                             5
% 4.05/1.00  EPR                                     3
% 4.05/1.00  Horn                                    14
% 4.05/1.00  unary                                   4
% 4.05/1.00  binary                                  7
% 4.05/1.00  lits                                    38
% 4.05/1.00  lits eq                                 8
% 4.05/1.00  fd_pure                                 0
% 4.05/1.00  fd_pseudo                               0
% 4.05/1.00  fd_cond                                 0
% 4.05/1.00  fd_pseudo_cond                          0
% 4.05/1.00  AC symbols                              0
% 4.05/1.00  
% 4.05/1.00  ------ Input Options Time Limit: Unbounded
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 4.05/1.00  Current options:
% 4.05/1.00  ------ 
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  ------ Proving...
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.05/1.00  
% 4.05/1.00  ------ Proving...
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  ------ Preprocessing... sf_s  rm: 9 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.05/1.00  
% 4.05/1.00  ------ Proving...
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.05/1.00  
% 4.05/1.00  ------ Proving...
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.05/1.00  
% 4.05/1.00  ------ Proving...
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.05/1.00  
% 4.05/1.00  ------ Proving...
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.05/1.00  
% 4.05/1.00  ------ Proving...
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.05/1.00  
% 4.05/1.00  ------ Proving...
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.05/1.00  
% 4.05/1.00  ------ Proving...
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 4.05/1.00  
% 4.05/1.00  ------ Proving...
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  % SZS status CounterSatisfiable for theBenchmark.p
% 4.05/1.00  
% 4.05/1.00  % SZS output start Saturation for theBenchmark.p
% 4.05/1.00  
% 4.05/1.00  fof(f3,axiom,(
% 4.05/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 4.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f14,plain,(
% 4.05/1.00    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.05/1.00    inference(ennf_transformation,[],[f3])).
% 4.05/1.00  
% 4.05/1.00  fof(f30,plain,(
% 4.05/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.05/1.00    inference(cnf_transformation,[],[f14])).
% 4.05/1.00  
% 4.05/1.00  fof(f1,axiom,(
% 4.05/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f28,plain,(
% 4.05/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.05/1.00    inference(cnf_transformation,[],[f1])).
% 4.05/1.00  
% 4.05/1.00  fof(f7,axiom,(
% 4.05/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 4.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f34,plain,(
% 4.05/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 4.05/1.00    inference(cnf_transformation,[],[f7])).
% 4.05/1.00  
% 4.05/1.00  fof(f49,plain,(
% 4.05/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 4.05/1.00    inference(definition_unfolding,[],[f28,f34])).
% 4.05/1.00  
% 4.05/1.00  fof(f50,plain,(
% 4.05/1.00    ( ! [X0,X1] : (k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.05/1.00    inference(definition_unfolding,[],[f30,f49])).
% 4.05/1.00  
% 4.05/1.00  fof(f4,axiom,(
% 4.05/1.00    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 4.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f31,plain,(
% 4.05/1.00    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 4.05/1.00    inference(cnf_transformation,[],[f4])).
% 4.05/1.00  
% 4.05/1.00  fof(f2,axiom,(
% 4.05/1.00    ! [X0] : k2_subset_1(X0) = X0),
% 4.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f29,plain,(
% 4.05/1.00    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 4.05/1.00    inference(cnf_transformation,[],[f2])).
% 4.05/1.00  
% 4.05/1.00  fof(f12,conjecture,(
% 4.05/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v2_pre_topc(X0)) => v3_pre_topc(X1,X0)) & (v3_pre_topc(X1,X0) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))))))),
% 4.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f13,negated_conjecture,(
% 4.05/1.00    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v2_pre_topc(X0)) => v3_pre_topc(X1,X0)) & (v3_pre_topc(X1,X0) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))))))),
% 4.05/1.00    inference(negated_conjecture,[],[f12])).
% 4.05/1.00  
% 4.05/1.00  fof(f22,plain,(
% 4.05/1.00    ? [X0] : (? [X1] : (((~v3_pre_topc(X1,X0) & (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v2_pre_topc(X0))) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 4.05/1.00    inference(ennf_transformation,[],[f13])).
% 4.05/1.00  
% 4.05/1.00  fof(f23,plain,(
% 4.05/1.00    ? [X0] : (? [X1] : (((~v3_pre_topc(X1,X0) & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v2_pre_topc(X0)) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 4.05/1.00    inference(flattening,[],[f22])).
% 4.05/1.00  
% 4.05/1.00  fof(f26,plain,(
% 4.05/1.00    ( ! [X0] : (? [X1] : (((~v3_pre_topc(X1,X0) & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v2_pre_topc(X0)) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (((~v3_pre_topc(sK1,X0) & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1)) & v2_pre_topc(X0)) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1)) & v3_pre_topc(sK1,X0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 4.05/1.00    introduced(choice_axiom,[])).
% 4.05/1.00  
% 4.05/1.00  fof(f25,plain,(
% 4.05/1.00    ? [X0] : (? [X1] : (((~v3_pre_topc(X1,X0) & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v2_pre_topc(X0)) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (((~v3_pre_topc(X1,sK0) & k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1)) & v2_pre_topc(sK0)) | (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1)) & v3_pre_topc(X1,sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 4.05/1.00    introduced(choice_axiom,[])).
% 4.05/1.00  
% 4.05/1.00  fof(f27,plain,(
% 4.05/1.00    (((~v3_pre_topc(sK1,sK0) & k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) & v2_pre_topc(sK0)) | (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) & v3_pre_topc(sK1,sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 4.05/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f26,f25])).
% 4.05/1.00  
% 4.05/1.00  fof(f42,plain,(
% 4.05/1.00    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 4.05/1.00    inference(cnf_transformation,[],[f27])).
% 4.05/1.00  
% 4.05/1.00  fof(f5,axiom,(
% 4.05/1.00    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 4.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f15,plain,(
% 4.05/1.00    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.05/1.00    inference(ennf_transformation,[],[f5])).
% 4.05/1.00  
% 4.05/1.00  fof(f32,plain,(
% 4.05/1.00    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.05/1.00    inference(cnf_transformation,[],[f15])).
% 4.05/1.00  
% 4.05/1.00  fof(f10,axiom,(
% 4.05/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1))),
% 4.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f19,plain,(
% 4.05/1.00    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 4.05/1.00    inference(ennf_transformation,[],[f10])).
% 4.05/1.00  
% 4.05/1.00  fof(f38,plain,(
% 4.05/1.00    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f19])).
% 4.05/1.00  
% 4.05/1.00  fof(f41,plain,(
% 4.05/1.00    l1_pre_topc(sK0)),
% 4.05/1.00    inference(cnf_transformation,[],[f27])).
% 4.05/1.00  
% 4.05/1.00  fof(f9,axiom,(
% 4.05/1.00    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 4.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f18,plain,(
% 4.05/1.00    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 4.05/1.00    inference(ennf_transformation,[],[f9])).
% 4.05/1.00  
% 4.05/1.00  fof(f37,plain,(
% 4.05/1.00    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f18])).
% 4.05/1.00  
% 4.05/1.00  fof(f8,axiom,(
% 4.05/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0))))),
% 4.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f17,plain,(
% 4.05/1.00    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.05/1.00    inference(ennf_transformation,[],[f8])).
% 4.05/1.00  
% 4.05/1.00  fof(f24,plain,(
% 4.05/1.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) & (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.05/1.00    inference(nnf_transformation,[],[f17])).
% 4.05/1.00  
% 4.05/1.00  fof(f35,plain,(
% 4.05/1.00    ( ! [X0,X1] : (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f24])).
% 4.05/1.00  
% 4.05/1.00  fof(f36,plain,(
% 4.05/1.00    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f24])).
% 4.05/1.00  
% 4.05/1.00  fof(f11,axiom,(
% 4.05/1.00    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 4.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f20,plain,(
% 4.05/1.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.05/1.00    inference(ennf_transformation,[],[f11])).
% 4.05/1.00  
% 4.05/1.00  fof(f21,plain,(
% 4.05/1.00    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.05/1.00    inference(flattening,[],[f20])).
% 4.05/1.00  
% 4.05/1.00  fof(f39,plain,(
% 4.05/1.00    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f21])).
% 4.05/1.00  
% 4.05/1.00  fof(f6,axiom,(
% 4.05/1.00    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 4.05/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.05/1.00  
% 4.05/1.00  fof(f16,plain,(
% 4.05/1.00    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 4.05/1.00    inference(ennf_transformation,[],[f6])).
% 4.05/1.00  
% 4.05/1.00  fof(f33,plain,(
% 4.05/1.00    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.05/1.00    inference(cnf_transformation,[],[f16])).
% 4.05/1.00  
% 4.05/1.00  fof(f51,plain,(
% 4.05/1.00    ( ! [X2,X0,X1] : (k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 4.05/1.00    inference(definition_unfolding,[],[f33,f49])).
% 4.05/1.00  
% 4.05/1.00  fof(f40,plain,(
% 4.05/1.00    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 4.05/1.00    inference(cnf_transformation,[],[f21])).
% 4.05/1.00  
% 4.05/1.00  fof(f48,plain,(
% 4.05/1.00    ~v3_pre_topc(sK1,sK0) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))),
% 4.05/1.00    inference(cnf_transformation,[],[f27])).
% 4.05/1.00  
% 4.05/1.00  fof(f45,plain,(
% 4.05/1.00    k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) | v3_pre_topc(sK1,sK0)),
% 4.05/1.00    inference(cnf_transformation,[],[f27])).
% 4.05/1.00  
% 4.05/1.00  fof(f43,plain,(
% 4.05/1.00    v2_pre_topc(sK0) | v3_pre_topc(sK1,sK0)),
% 4.05/1.00    inference(cnf_transformation,[],[f27])).
% 4.05/1.00  
% 4.05/1.00  cnf(c_181,plain,( X0_2 = X0_2 ),theory(equality) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_1,plain,
% 4.05/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.05/1.00      | k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X0))) = k3_subset_1(X1,X0) ),
% 4.05/1.00      inference(cnf_transformation,[],[f50]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_9612,plain,
% 4.05/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.05/1.00      | ~ iProver_ARSWP_78
% 4.05/1.00      | arAF0_k5_xboole_0_0 = arAF0_k3_subset_1_0 ),
% 4.05/1.00      inference(arg_filter_abstr,[status(unp)],[c_1]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_2,plain,
% 4.05/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 4.05/1.00      inference(cnf_transformation,[],[f31]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_2818,plain,
% 4.05/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_0,plain,
% 4.05/1.00      ( k2_subset_1(X0) = X0 ),
% 4.05/1.00      inference(cnf_transformation,[],[f29]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_2823,plain,
% 4.05/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 4.05/1.00      inference(light_normalisation,[status(thm)],[c_2818,c_0]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_2858,plain,
% 4.05/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) ),
% 4.05/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2823]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_2860,plain,
% 4.05/1.00      ( m1_subset_1(sK0,k1_zfmisc_1(sK0)) ),
% 4.05/1.00      inference(instantiation,[status(thm)],[c_2858]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_9634,plain,
% 4.05/1.00      ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
% 4.05/1.00      | ~ iProver_ARSWP_78
% 4.05/1.00      | arAF0_k5_xboole_0_0 = arAF0_k3_subset_1_0 ),
% 4.05/1.00      inference(instantiation,[status(thm)],[c_9612]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_9788,plain,
% 4.05/1.00      ( ~ iProver_ARSWP_78 | arAF0_k5_xboole_0_0 = arAF0_k3_subset_1_0 ),
% 4.05/1.00      inference(global_propositional_subsumption,
% 4.05/1.00                [status(thm)],
% 4.05/1.00                [c_9612,c_2860,c_9634]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_9873,plain,
% 4.05/1.00      ( arAF0_k5_xboole_0_0 = arAF0_k3_subset_1_0
% 4.05/1.00      | iProver_ARSWP_78 != iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_9788]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_17,negated_conjecture,
% 4.05/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 4.05/1.00      inference(cnf_transformation,[],[f42]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_9883,plain,
% 4.05/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_3,plain,
% 4.05/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.05/1.00      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 4.05/1.00      inference(cnf_transformation,[],[f32]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_9613,plain,
% 4.05/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.05/1.00      | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(X1))
% 4.05/1.00      | ~ iProver_ARSWP_79 ),
% 4.05/1.00      inference(arg_filter_abstr,[status(unp)],[c_3]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_9877,plain,
% 4.05/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.05/1.00      | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(X1)) = iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_9613]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_10419,plain,
% 4.05/1.00      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_9883,c_9877]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_10719,plain,
% 4.05/1.00      ( m1_subset_1(arAF0_k5_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top
% 4.05/1.00      | iProver_ARSWP_78 != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_9873,c_10419]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_8,plain,
% 4.05/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.05/1.00      | ~ l1_struct_0(X1)
% 4.05/1.00      | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0 ),
% 4.05/1.00      inference(cnf_transformation,[],[f38]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_9889,plain,
% 4.05/1.00      ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
% 4.05/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.05/1.00      | l1_struct_0(X0) != iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_10865,plain,
% 4.05/1.00      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0)) = arAF0_k5_xboole_0_0
% 4.05/1.00      | l1_struct_0(sK0) != iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top
% 4.05/1.00      | iProver_ARSWP_78 != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_10719,c_9889]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_18,negated_conjecture,
% 4.05/1.00      ( l1_pre_topc(sK0) ),
% 4.05/1.00      inference(cnf_transformation,[],[f41]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_19,plain,
% 4.05/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_7,plain,
% 4.05/1.00      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 4.05/1.00      inference(cnf_transformation,[],[f37]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_35,plain,
% 4.05/1.00      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_37,plain,
% 4.05/1.00      ( l1_struct_0(sK0) = iProver_top | l1_pre_topc(sK0) != iProver_top ),
% 4.05/1.00      inference(instantiation,[status(thm)],[c_35]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_12236,plain,
% 4.05/1.00      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0)) = arAF0_k5_xboole_0_0
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top
% 4.05/1.00      | iProver_ARSWP_78 != iProver_top ),
% 4.05/1.00      inference(global_propositional_subsumption,
% 4.05/1.00                [status(thm)],
% 4.05/1.00                [c_10865,c_19,c_37]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_6,plain,
% 4.05/1.00      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
% 4.05/1.00      | ~ v4_pre_topc(X1,X0)
% 4.05/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 4.05/1.00      | ~ l1_pre_topc(X0) ),
% 4.05/1.00      inference(cnf_transformation,[],[f35]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_9891,plain,
% 4.05/1.00      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) = iProver_top
% 4.05/1.00      | v4_pre_topc(X1,X0) != iProver_top
% 4.05/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.05/1.00      | l1_pre_topc(X0) != iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_12245,plain,
% 4.05/1.00      ( v3_pre_topc(arAF0_k5_xboole_0_0,sK0) = iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),sK0) != iProver_top
% 4.05/1.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.05/1.00      | l1_pre_topc(sK0) != iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top
% 4.05/1.00      | iProver_ARSWP_78 != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_12236,c_9891]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_13863,plain,
% 4.05/1.00      ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),sK0) != iProver_top
% 4.05/1.00      | v3_pre_topc(arAF0_k5_xboole_0_0,sK0) = iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top
% 4.05/1.00      | iProver_ARSWP_78 != iProver_top ),
% 4.05/1.00      inference(global_propositional_subsumption,[status(thm)],[c_12245,c_19]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_13864,plain,
% 4.05/1.00      ( v3_pre_topc(arAF0_k5_xboole_0_0,sK0) = iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),sK0) != iProver_top
% 4.05/1.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top
% 4.05/1.00      | iProver_ARSWP_78 != iProver_top ),
% 4.05/1.00      inference(renaming,[status(thm)],[c_13863]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_5,plain,
% 4.05/1.00      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
% 4.05/1.00      | v4_pre_topc(X1,X0)
% 4.05/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 4.05/1.00      | ~ l1_pre_topc(X0) ),
% 4.05/1.00      inference(cnf_transformation,[],[f36]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_9892,plain,
% 4.05/1.00      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) != iProver_top
% 4.05/1.00      | v4_pre_topc(X1,X0) = iProver_top
% 4.05/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.05/1.00      | l1_pre_topc(X0) != iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_12244,plain,
% 4.05/1.00      ( v3_pre_topc(arAF0_k5_xboole_0_0,sK0) != iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),sK0) = iProver_top
% 4.05/1.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.05/1.00      | l1_pre_topc(sK0) != iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top
% 4.05/1.00      | iProver_ARSWP_78 != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_12236,c_9892]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_13853,plain,
% 4.05/1.00      ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),sK0) = iProver_top
% 4.05/1.00      | v3_pre_topc(arAF0_k5_xboole_0_0,sK0) != iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top
% 4.05/1.00      | iProver_ARSWP_78 != iProver_top ),
% 4.05/1.00      inference(global_propositional_subsumption,[status(thm)],[c_12244,c_19]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_13854,plain,
% 4.05/1.00      ( v3_pre_topc(arAF0_k5_xboole_0_0,sK0) != iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),sK0) = iProver_top
% 4.05/1.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top
% 4.05/1.00      | iProver_ARSWP_78 != iProver_top ),
% 4.05/1.00      inference(renaming,[status(thm)],[c_13853]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_9893,plain,
% 4.05/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_9900,plain,
% 4.05/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 4.05/1.00      inference(light_normalisation,[status(thm)],[c_9893,c_0]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_10420,plain,
% 4.05/1.00      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(X0)) = iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_9900,c_9877]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_11422,plain,
% 4.05/1.00      ( m1_subset_1(arAF0_k5_xboole_0_0,k1_zfmisc_1(X0)) = iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top
% 4.05/1.00      | iProver_ARSWP_78 != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_9873,c_10420]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_10,plain,
% 4.05/1.00      ( ~ v4_pre_topc(X0,X1)
% 4.05/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.05/1.00      | ~ l1_pre_topc(X1)
% 4.05/1.00      | k2_pre_topc(X1,X0) = X0 ),
% 4.05/1.00      inference(cnf_transformation,[],[f39]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_9887,plain,
% 4.05/1.00      ( k2_pre_topc(X0,X1) = X1
% 4.05/1.00      | v4_pre_topc(X1,X0) != iProver_top
% 4.05/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.05/1.00      | l1_pre_topc(X0) != iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_13517,plain,
% 4.05/1.00      ( k2_pre_topc(X0,arAF0_k5_xboole_0_0) = arAF0_k5_xboole_0_0
% 4.05/1.00      | v4_pre_topc(arAF0_k5_xboole_0_0,X0) != iProver_top
% 4.05/1.00      | l1_pre_topc(X0) != iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top
% 4.05/1.00      | iProver_ARSWP_78 != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_11422,c_9887]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_13516,plain,
% 4.05/1.00      ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),arAF0_k5_xboole_0_0)) = arAF0_k5_xboole_0_0
% 4.05/1.00      | l1_struct_0(X0) != iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top
% 4.05/1.00      | iProver_ARSWP_78 != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_11422,c_9889]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_4,plain,
% 4.05/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.05/1.00      | k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))) = k7_subset_1(X1,X0,X2) ),
% 4.05/1.00      inference(cnf_transformation,[],[f51]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_9614,plain,
% 4.05/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 4.05/1.00      | ~ iProver_ARSWP_80
% 4.05/1.00      | arAF0_k5_xboole_0_0 = k7_subset_1(X1,X0,X2) ),
% 4.05/1.00      inference(arg_filter_abstr,[status(unp)],[c_4]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_9876,plain,
% 4.05/1.00      ( arAF0_k5_xboole_0_0 = k7_subset_1(X0,X1,X2)
% 4.05/1.00      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 4.05/1.00      | iProver_ARSWP_80 != iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_9614]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_13515,plain,
% 4.05/1.00      ( k7_subset_1(X0,arAF0_k5_xboole_0_0,X1) = arAF0_k5_xboole_0_0
% 4.05/1.00      | iProver_ARSWP_80 != iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top
% 4.05/1.00      | iProver_ARSWP_78 != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_11422,c_9876]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_10720,plain,
% 4.05/1.00      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0)) = arAF0_k3_subset_1_0
% 4.05/1.00      | l1_struct_0(sK0) != iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_10419,c_9889]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_11024,plain,
% 4.05/1.00      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0)) = arAF0_k3_subset_1_0
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top ),
% 4.05/1.00      inference(global_propositional_subsumption,
% 4.05/1.00                [status(thm)],
% 4.05/1.00                [c_10720,c_19,c_37]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_11030,plain,
% 4.05/1.00      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0)) = arAF0_k3_subset_1_0
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top
% 4.05/1.00      | iProver_ARSWP_78 != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_9873,c_11024]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_12060,plain,
% 4.05/1.00      ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) = iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),sK0) != iProver_top
% 4.05/1.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.05/1.00      | l1_pre_topc(sK0) != iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top
% 4.05/1.00      | iProver_ARSWP_78 != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_11030,c_9891]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_13502,plain,
% 4.05/1.00      ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),sK0) != iProver_top
% 4.05/1.00      | v3_pre_topc(arAF0_k3_subset_1_0,sK0) = iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top
% 4.05/1.00      | iProver_ARSWP_78 != iProver_top ),
% 4.05/1.00      inference(global_propositional_subsumption,[status(thm)],[c_12060,c_19]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_13503,plain,
% 4.05/1.00      ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) = iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),sK0) != iProver_top
% 4.05/1.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top
% 4.05/1.00      | iProver_ARSWP_78 != iProver_top ),
% 4.05/1.00      inference(renaming,[status(thm)],[c_13502]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_12059,plain,
% 4.05/1.00      ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),sK0) = iProver_top
% 4.05/1.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.05/1.00      | l1_pre_topc(sK0) != iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top
% 4.05/1.00      | iProver_ARSWP_78 != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_11030,c_9892]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_13309,plain,
% 4.05/1.00      ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),sK0) = iProver_top
% 4.05/1.00      | v3_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top
% 4.05/1.00      | iProver_ARSWP_78 != iProver_top ),
% 4.05/1.00      inference(global_propositional_subsumption,[status(thm)],[c_12059,c_19]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_13310,plain,
% 4.05/1.00      ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),sK0) = iProver_top
% 4.05/1.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top
% 4.05/1.00      | iProver_ARSWP_78 != iProver_top ),
% 4.05/1.00      inference(renaming,[status(thm)],[c_13309]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_9882,plain,
% 4.05/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_9890,plain,
% 4.05/1.00      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_10435,plain,
% 4.05/1.00      ( l1_struct_0(sK0) = iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_9882,c_9890]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_10548,plain,
% 4.05/1.00      ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0))) = u1_struct_0(X0)
% 4.05/1.00      | l1_struct_0(X0) != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_9900,c_9889]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_12409,plain,
% 4.05/1.00      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) = u1_struct_0(sK0) ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_10435,c_10548]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_12755,plain,
% 4.05/1.00      ( v3_pre_topc(u1_struct_0(sK0),sK0) != iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),sK0) = iProver_top
% 4.05/1.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.05/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_12409,c_9892]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_12940,plain,
% 4.05/1.00      ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),sK0) = iProver_top
% 4.05/1.00      | v3_pre_topc(u1_struct_0(sK0),sK0) != iProver_top ),
% 4.05/1.00      inference(global_propositional_subsumption,[status(thm)],[c_12755,c_19]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_12941,plain,
% 4.05/1.00      ( v3_pre_topc(u1_struct_0(sK0),sK0) != iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),sK0) = iProver_top
% 4.05/1.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.05/1.00      inference(renaming,[status(thm)],[c_12940]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_11398,plain,
% 4.05/1.00      ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),sK0) = iProver_top
% 4.05/1.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.05/1.00      | l1_pre_topc(sK0) != iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_11024,c_9892]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_12744,plain,
% 4.05/1.00      ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),sK0) = iProver_top
% 4.05/1.00      | v3_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top ),
% 4.05/1.00      inference(global_propositional_subsumption,[status(thm)],[c_11398,c_19]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_12745,plain,
% 4.05/1.00      ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),sK0) = iProver_top
% 4.05/1.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top ),
% 4.05/1.00      inference(renaming,[status(thm)],[c_12744]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_12752,plain,
% 4.05/1.00      ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),sK0) = iProver_top
% 4.05/1.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top
% 4.05/1.00      | iProver_ARSWP_78 != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_9873,c_12745]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_12246,plain,
% 4.05/1.00      ( arAF0_k3_subset_1_0 = arAF0_k5_xboole_0_0
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top
% 4.05/1.00      | iProver_ARSWP_78 != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_12236,c_11030]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_313,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_312,plain,( X0 = X0 ),theory(equality) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_10465,plain,
% 4.05/1.00      ( X0 != X1 | X1 = X0 ),
% 4.05/1.00      inference(resolution,[status(thm)],[c_313,c_312]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_12625,plain,
% 4.05/1.00      ( ~ iProver_ARSWP_78 | arAF0_k3_subset_1_0 = arAF0_k5_xboole_0_0 ),
% 4.05/1.00      inference(resolution,[status(thm)],[c_10465,c_9788]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_12626,plain,
% 4.05/1.00      ( arAF0_k3_subset_1_0 = arAF0_k5_xboole_0_0
% 4.05/1.00      | iProver_ARSWP_78 != iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_12625]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_13117,plain,
% 4.05/1.00      ( arAF0_k3_subset_1_0 = arAF0_k5_xboole_0_0
% 4.05/1.00      | iProver_ARSWP_78 != iProver_top ),
% 4.05/1.00      inference(global_propositional_subsumption,
% 4.05/1.00                [status(thm)],
% 4.05/1.00                [c_12246,c_12626]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_11424,plain,
% 4.05/1.00      ( k2_pre_topc(X0,arAF0_k3_subset_1_0) = arAF0_k3_subset_1_0
% 4.05/1.00      | v4_pre_topc(arAF0_k3_subset_1_0,X0) != iProver_top
% 4.05/1.00      | l1_pre_topc(X0) != iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_10420,c_9887]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_12603,plain,
% 4.05/1.00      ( k2_pre_topc(X0,arAF0_k3_subset_1_0) = arAF0_k3_subset_1_0
% 4.05/1.00      | v4_pre_topc(arAF0_k5_xboole_0_0,X0) != iProver_top
% 4.05/1.00      | l1_pre_topc(X0) != iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top
% 4.05/1.00      | iProver_ARSWP_78 != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_9873,c_11424]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_11031,plain,
% 4.05/1.00      ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) = iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),sK0) != iProver_top
% 4.05/1.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.05/1.00      | l1_pre_topc(sK0) != iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_11024,c_9891]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_12281,plain,
% 4.05/1.00      ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),sK0) != iProver_top
% 4.05/1.00      | v3_pre_topc(arAF0_k3_subset_1_0,sK0) = iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top ),
% 4.05/1.00      inference(global_propositional_subsumption,[status(thm)],[c_11031,c_19]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_12282,plain,
% 4.05/1.00      ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) = iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),sK0) != iProver_top
% 4.05/1.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top ),
% 4.05/1.00      inference(renaming,[status(thm)],[c_12281]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_12289,plain,
% 4.05/1.00      ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) = iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),sK0) != iProver_top
% 4.05/1.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k5_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top
% 4.05/1.00      | iProver_ARSWP_78 != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_9873,c_12282]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_10866,plain,
% 4.05/1.00      ( k2_pre_topc(sK0,arAF0_k5_xboole_0_0) = arAF0_k5_xboole_0_0
% 4.05/1.00      | v4_pre_topc(arAF0_k5_xboole_0_0,sK0) != iProver_top
% 4.05/1.00      | l1_pre_topc(sK0) != iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top
% 4.05/1.00      | iProver_ARSWP_78 != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_10719,c_9887]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_12088,plain,
% 4.05/1.00      ( v4_pre_topc(arAF0_k5_xboole_0_0,sK0) != iProver_top
% 4.05/1.00      | k2_pre_topc(sK0,arAF0_k5_xboole_0_0) = arAF0_k5_xboole_0_0
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top
% 4.05/1.00      | iProver_ARSWP_78 != iProver_top ),
% 4.05/1.00      inference(global_propositional_subsumption,[status(thm)],[c_10866,c_19]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_12089,plain,
% 4.05/1.00      ( k2_pre_topc(sK0,arAF0_k5_xboole_0_0) = arAF0_k5_xboole_0_0
% 4.05/1.00      | v4_pre_topc(arAF0_k5_xboole_0_0,sK0) != iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top
% 4.05/1.00      | iProver_ARSWP_78 != iProver_top ),
% 4.05/1.00      inference(renaming,[status(thm)],[c_12088]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_10547,plain,
% 4.05/1.00      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) = sK1
% 4.05/1.00      | l1_struct_0(sK0) != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_9883,c_9889]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_36,plain,
% 4.05/1.00      ( l1_struct_0(sK0) | ~ l1_pre_topc(sK0) ),
% 4.05/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_8134,plain,
% 4.05/1.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 4.05/1.00      | ~ l1_struct_0(sK0)
% 4.05/1.00      | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) = sK1 ),
% 4.05/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_10856,plain,
% 4.05/1.00      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) = sK1 ),
% 4.05/1.00      inference(global_propositional_subsumption,
% 4.05/1.00                [status(thm)],
% 4.05/1.00                [c_10547,c_18,c_17,c_36,c_8134]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_11397,plain,
% 4.05/1.00      ( v3_pre_topc(sK1,sK0) != iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) = iProver_top
% 4.05/1.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.05/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_10856,c_9892]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_11789,plain,
% 4.05/1.00      ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) = iProver_top
% 4.05/1.00      | v3_pre_topc(sK1,sK0) != iProver_top ),
% 4.05/1.00      inference(global_propositional_subsumption,[status(thm)],[c_11397,c_19]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_11790,plain,
% 4.05/1.00      ( v3_pre_topc(sK1,sK0) != iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) = iProver_top
% 4.05/1.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.05/1.00      inference(renaming,[status(thm)],[c_11789]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_11597,plain,
% 4.05/1.00      ( k7_subset_1(u1_struct_0(sK0),arAF0_k5_xboole_0_0,X0) = arAF0_k5_xboole_0_0
% 4.05/1.00      | iProver_ARSWP_80 != iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top
% 4.05/1.00      | iProver_ARSWP_78 != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_10719,c_9876]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_11596,plain,
% 4.05/1.00      ( k7_subset_1(X0,arAF0_k3_subset_1_0,X1) = arAF0_k5_xboole_0_0
% 4.05/1.00      | iProver_ARSWP_80 != iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_10420,c_9876]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_11594,plain,
% 4.05/1.00      ( k7_subset_1(X0,X0,X1) = arAF0_k5_xboole_0_0
% 4.05/1.00      | iProver_ARSWP_80 != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_9900,c_9876]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_11593,plain,
% 4.05/1.00      ( k7_subset_1(u1_struct_0(sK0),sK1,X0) = arAF0_k5_xboole_0_0
% 4.05/1.00      | iProver_ARSWP_80 != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_9883,c_9876]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_11423,plain,
% 4.05/1.00      ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),arAF0_k3_subset_1_0)) = arAF0_k3_subset_1_0
% 4.05/1.00      | l1_struct_0(X0) != iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_10420,c_9889]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_10721,plain,
% 4.05/1.00      ( k2_pre_topc(sK0,arAF0_k3_subset_1_0) = arAF0_k3_subset_1_0
% 4.05/1.00      | v4_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
% 4.05/1.00      | l1_pre_topc(sK0) != iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_10419,c_9887]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_11014,plain,
% 4.05/1.00      ( v4_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
% 4.05/1.00      | k2_pre_topc(sK0,arAF0_k3_subset_1_0) = arAF0_k3_subset_1_0
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top ),
% 4.05/1.00      inference(global_propositional_subsumption,[status(thm)],[c_10721,c_19]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_11015,plain,
% 4.05/1.00      ( k2_pre_topc(sK0,arAF0_k3_subset_1_0) = arAF0_k3_subset_1_0
% 4.05/1.00      | v4_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top ),
% 4.05/1.00      inference(renaming,[status(thm)],[c_11014]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_11021,plain,
% 4.05/1.00      ( k2_pre_topc(sK0,arAF0_k3_subset_1_0) = arAF0_k3_subset_1_0
% 4.05/1.00      | v4_pre_topc(arAF0_k5_xboole_0_0,sK0) != iProver_top
% 4.05/1.00      | iProver_ARSWP_79 != iProver_top
% 4.05/1.00      | iProver_ARSWP_78 != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_9873,c_11015]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_10525,plain,
% 4.05/1.00      ( k2_pre_topc(sK0,sK1) = sK1
% 4.05/1.00      | v4_pre_topc(sK1,sK0) != iProver_top
% 4.05/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_9883,c_9887]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_10746,plain,
% 4.05/1.00      ( v4_pre_topc(sK1,sK0) != iProver_top | k2_pre_topc(sK0,sK1) = sK1 ),
% 4.05/1.00      inference(global_propositional_subsumption,[status(thm)],[c_10525,c_19]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_10747,plain,
% 4.05/1.00      ( k2_pre_topc(sK0,sK1) = sK1 | v4_pre_topc(sK1,sK0) != iProver_top ),
% 4.05/1.00      inference(renaming,[status(thm)],[c_10746]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_10526,plain,
% 4.05/1.00      ( k2_pre_topc(X0,u1_struct_0(X0)) = u1_struct_0(X0)
% 4.05/1.00      | v4_pre_topc(u1_struct_0(X0),X0) != iProver_top
% 4.05/1.00      | l1_pre_topc(X0) != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_9900,c_9887]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_12756,plain,
% 4.05/1.00      ( v3_pre_topc(u1_struct_0(sK0),sK0) = iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),sK0) != iProver_top
% 4.05/1.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.05/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_12409,c_9891]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_8010,plain,
% 4.05/1.00      ( l1_pre_topc(sK0) = iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_8016,plain,
% 4.05/1.00      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_8298,plain,
% 4.05/1.00      ( l1_struct_0(sK0) = iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_8010,c_8016]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_8018,plain,
% 4.05/1.00      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_8025,plain,
% 4.05/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 4.05/1.00      inference(light_normalisation,[status(thm)],[c_8018,c_0]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_8015,plain,
% 4.05/1.00      ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
% 4.05/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.05/1.00      | l1_struct_0(X0) != iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_8383,plain,
% 4.05/1.00      ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),u1_struct_0(X0))) = u1_struct_0(X0)
% 4.05/1.00      | l1_struct_0(X0) != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_8025,c_8015]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_8601,plain,
% 4.05/1.00      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) = u1_struct_0(sK0) ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_8298,c_8383]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_8017,plain,
% 4.05/1.00      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) = iProver_top
% 4.05/1.00      | v4_pre_topc(X1,X0) != iProver_top
% 4.05/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.05/1.00      | l1_pre_topc(X0) != iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_8603,plain,
% 4.05/1.00      ( v3_pre_topc(u1_struct_0(sK0),sK0) = iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),sK0) != iProver_top
% 4.05/1.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.05/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_8601,c_8017]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_8709,plain,
% 4.05/1.00      ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),sK0) != iProver_top
% 4.05/1.00      | v3_pre_topc(u1_struct_0(sK0),sK0) = iProver_top ),
% 4.05/1.00      inference(global_propositional_subsumption,[status(thm)],[c_8603,c_19]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_8710,plain,
% 4.05/1.00      ( v3_pre_topc(u1_struct_0(sK0),sK0) = iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),sK0) != iProver_top
% 4.05/1.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.05/1.00      inference(renaming,[status(thm)],[c_8709]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_12948,plain,
% 4.05/1.00      ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),sK0) != iProver_top
% 4.05/1.00      | v3_pre_topc(u1_struct_0(sK0),sK0) = iProver_top ),
% 4.05/1.00      inference(global_propositional_subsumption,
% 4.05/1.00                [status(thm)],
% 4.05/1.00                [c_12756,c_19,c_8603]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_12949,plain,
% 4.05/1.00      ( v3_pre_topc(u1_struct_0(sK0),sK0) = iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),sK0) != iProver_top
% 4.05/1.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.05/1.00      inference(renaming,[status(thm)],[c_12948]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_10859,plain,
% 4.05/1.00      ( v3_pre_topc(sK1,sK0) = iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) != iProver_top
% 4.05/1.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.05/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_10856,c_9891]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_8011,plain,
% 4.05/1.00      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_8382,plain,
% 4.05/1.00      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) = sK1
% 4.05/1.00      | l1_struct_0(sK0) != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_8011,c_8015]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_8484,plain,
% 4.05/1.00      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) = sK1 ),
% 4.05/1.00      inference(global_propositional_subsumption,
% 4.05/1.00                [status(thm)],
% 4.05/1.00                [c_8382,c_18,c_17,c_36,c_8134]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_8487,plain,
% 4.05/1.00      ( v3_pre_topc(sK1,sK0) = iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) != iProver_top
% 4.05/1.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.05/1.00      | l1_pre_topc(sK0) != iProver_top ),
% 4.05/1.00      inference(superposition,[status(thm)],[c_8484,c_8017]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_8701,plain,
% 4.05/1.00      ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) != iProver_top
% 4.05/1.00      | v3_pre_topc(sK1,sK0) = iProver_top ),
% 4.05/1.00      inference(global_propositional_subsumption,[status(thm)],[c_8487,c_19]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_8702,plain,
% 4.05/1.00      ( v3_pre_topc(sK1,sK0) = iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) != iProver_top
% 4.05/1.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.05/1.00      inference(renaming,[status(thm)],[c_8701]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_11154,plain,
% 4.05/1.00      ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) != iProver_top
% 4.05/1.00      | v3_pre_topc(sK1,sK0) = iProver_top ),
% 4.05/1.00      inference(global_propositional_subsumption,
% 4.05/1.00                [status(thm)],
% 4.05/1.00                [c_10859,c_19,c_8487]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_11155,plain,
% 4.05/1.00      ( v3_pre_topc(sK1,sK0) = iProver_top
% 4.05/1.00      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) != iProver_top
% 4.05/1.00      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 4.05/1.00      inference(renaming,[status(thm)],[c_11154]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_9,plain,
% 4.05/1.00      ( v4_pre_topc(X0,X1)
% 4.05/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 4.05/1.00      | ~ v2_pre_topc(X1)
% 4.05/1.00      | ~ l1_pre_topc(X1)
% 4.05/1.00      | k2_pre_topc(X1,X0) != X0 ),
% 4.05/1.00      inference(cnf_transformation,[],[f40]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_9888,plain,
% 4.05/1.00      ( k2_pre_topc(X0,X1) != X1
% 4.05/1.00      | v4_pre_topc(X1,X0) = iProver_top
% 4.05/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 4.05/1.00      | v2_pre_topc(X0) != iProver_top
% 4.05/1.00      | l1_pre_topc(X0) != iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_11,negated_conjecture,
% 4.05/1.00      ( ~ v3_pre_topc(sK1,sK0)
% 4.05/1.00      | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) ),
% 4.05/1.00      inference(cnf_transformation,[],[f48]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_9886,plain,
% 4.05/1.00      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))
% 4.05/1.00      | v3_pre_topc(sK1,sK0) != iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_14,negated_conjecture,
% 4.05/1.00      ( v3_pre_topc(sK1,sK0)
% 4.05/1.00      | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) ),
% 4.05/1.00      inference(cnf_transformation,[],[f45]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_9885,plain,
% 4.05/1.00      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))
% 4.05/1.00      | v3_pre_topc(sK1,sK0) = iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_16,negated_conjecture,
% 4.05/1.00      ( v3_pre_topc(sK1,sK0) | v2_pre_topc(sK0) ),
% 4.05/1.00      inference(cnf_transformation,[],[f43]) ).
% 4.05/1.00  
% 4.05/1.00  cnf(c_9884,plain,
% 4.05/1.00      ( v3_pre_topc(sK1,sK0) = iProver_top | v2_pre_topc(sK0) = iProver_top ),
% 4.05/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.05/1.00  
% 4.05/1.00  
% 4.05/1.00  % SZS output end Saturation for theBenchmark.p
% 4.05/1.00  
% 4.05/1.00  ------                               Statistics
% 4.05/1.00  
% 4.05/1.00  ------ Selected
% 4.05/1.00  
% 4.05/1.00  total_time:                             0.424
% 4.05/1.00  
%------------------------------------------------------------------------------
