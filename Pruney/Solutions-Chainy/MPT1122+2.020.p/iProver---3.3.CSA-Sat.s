%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:11:39 EST 2020

% Result     : CounterSatisfiable 3.69s
% Output     : Saturation 3.69s
% Verified   : 
% Statistics : Number of formulae       :  151 (1181 expanded)
%              Number of clauses        :  114 ( 498 expanded)
%              Number of leaves         :   13 ( 245 expanded)
%              Depth                    :   16
%              Number of atoms          :  504 (5311 expanded)
%              Number of equality atoms :  316 (1856 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
                & v2_pre_topc(X0) )
             => v3_pre_topc(X1,X0) )
            & ( v3_pre_topc(X1,X0)
             => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
                  & v2_pre_topc(X0) )
               => v3_pre_topc(X1,X0) )
              & ( v3_pre_topc(X1,X0)
               => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ~ v3_pre_topc(X1,X0)
              & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              & v2_pre_topc(X0) )
            | ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              & v3_pre_topc(X1,X0) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ~ v3_pre_topc(X1,X0)
              & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              & v2_pre_topc(X0) )
            | ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))
              & v3_pre_topc(X1,X0) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f22,plain,(
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

fof(f21,plain,
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

fof(f23,plain,
    ( ( ( ~ v3_pre_topc(sK1,sK0)
        & k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))
        & v2_pre_topc(sK0) )
      | ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))
        & v3_pre_topc(sK1,sK0) ) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f22,f21])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f29,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f37,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f40,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) != X1
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f35,plain,
    ( v2_pre_topc(sK0)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_168,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X1,X0) = k3_subset_1(X1,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_301,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | k4_xboole_0(X1_44,X0_44) = k3_subset_1(X1_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_3431,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | ~ iProver_ARSWP_65
    | arAF0_k4_xboole_0_0 = arAF0_k3_subset_1_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_301])).

cnf(c_3618,plain,
    ( arAF0_k4_xboole_0_0 = arAF0_k3_subset_1_0
    | m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) != iProver_top
    | iProver_ARSWP_65 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3431])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_289,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_3896,plain,
    ( ~ iProver_ARSWP_65
    | arAF0_k4_xboole_0_0 = arAF0_k3_subset_1_0 ),
    inference(resolution,[status(thm)],[c_3431,c_289])).

cnf(c_3897,plain,
    ( arAF0_k4_xboole_0_0 = arAF0_k3_subset_1_0
    | iProver_ARSWP_65 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3896])).

cnf(c_3977,plain,
    ( arAF0_k4_xboole_0_0 = arAF0_k3_subset_1_0
    | iProver_ARSWP_65 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3618,c_3897])).

cnf(c_3632,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_289])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_300,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | m1_subset_1(k3_subset_1(X1_44,X0_44),k1_zfmisc_1(X1_44)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_3430,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(X1_44))
    | ~ iProver_ARSWP_64 ),
    inference(arg_filter_abstr,[status(unp)],[c_300])).

cnf(c_3619,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) != iProver_top
    | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(X1_44)) = iProver_top
    | iProver_ARSWP_64 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3430])).

cnf(c_4093,plain,
    ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | iProver_ARSWP_64 != iProver_top ),
    inference(superposition,[status(thm)],[c_3632,c_3619])).

cnf(c_4339,plain,
    ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
    | iProver_ARSWP_65 != iProver_top
    | iProver_ARSWP_64 != iProver_top ),
    inference(superposition,[status(thm)],[c_3977,c_4093])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_struct_0(X1)
    | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_295,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43)))
    | ~ l1_struct_0(X0_43)
    | k7_subset_1(u1_struct_0(X0_43),k2_struct_0(X0_43),k7_subset_1(u1_struct_0(X0_43),k2_struct_0(X0_43),X0_44)) = X0_44 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_3626,plain,
    ( k7_subset_1(u1_struct_0(X0_43),k2_struct_0(X0_43),k7_subset_1(u1_struct_0(X0_43),k2_struct_0(X0_43),X0_44)) = X0_44
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43))) != iProver_top
    | l1_struct_0(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_295])).

cnf(c_4621,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0)) = arAF0_k4_xboole_0_0
    | l1_struct_0(sK0) != iProver_top
    | iProver_ARSWP_65 != iProver_top
    | iProver_ARSWP_64 != iProver_top ),
    inference(superposition,[status(thm)],[c_4339,c_3626])).

cnf(c_16,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_17,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_33,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_35,plain,
    ( l1_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_5550,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0)) = arAF0_k4_xboole_0_0
    | iProver_ARSWP_65 != iProver_top
    | iProver_ARSWP_64 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4621,c_17,c_35])).

cnf(c_3,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
    | v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_298,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0_43),k2_struct_0(X0_43),X0_44),X0_43)
    | v4_pre_topc(X0_44,X0_43)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43)))
    | ~ l1_pre_topc(X0_43) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_3623,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(X0_43),k2_struct_0(X0_43),X0_44),X0_43) != iProver_top
    | v4_pre_topc(X0_44,X0_43) = iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43))) != iProver_top
    | l1_pre_topc(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_298])).

cnf(c_5559,plain,
    ( v3_pre_topc(arAF0_k4_xboole_0_0,sK0) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),sK0) = iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | iProver_ARSWP_65 != iProver_top
    | iProver_ARSWP_64 != iProver_top ),
    inference(superposition,[status(thm)],[c_5550,c_3623])).

cnf(c_6271,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),sK0) = iProver_top
    | v3_pre_topc(arAF0_k4_xboole_0_0,sK0) != iProver_top
    | iProver_ARSWP_65 != iProver_top
    | iProver_ARSWP_64 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5559,c_17])).

cnf(c_6272,plain,
    ( v3_pre_topc(arAF0_k4_xboole_0_0,sK0) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),sK0) = iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | iProver_ARSWP_65 != iProver_top
    | iProver_ARSWP_64 != iProver_top ),
    inference(renaming,[status(thm)],[c_6271])).

cnf(c_4,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
    | ~ v4_pre_topc(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_297,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(X0_43),k2_struct_0(X0_43),X0_44),X0_43)
    | ~ v4_pre_topc(X0_44,X0_43)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43)))
    | ~ l1_pre_topc(X0_43) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_3624,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(X0_43),k2_struct_0(X0_43),X0_44),X0_43) = iProver_top
    | v4_pre_topc(X0_44,X0_43) != iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43))) != iProver_top
    | l1_pre_topc(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_297])).

cnf(c_5558,plain,
    ( v3_pre_topc(arAF0_k4_xboole_0_0,sK0) = iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),sK0) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | iProver_ARSWP_65 != iProver_top
    | iProver_ARSWP_64 != iProver_top ),
    inference(superposition,[status(thm)],[c_5550,c_3624])).

cnf(c_6116,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),sK0) != iProver_top
    | v3_pre_topc(arAF0_k4_xboole_0_0,sK0) = iProver_top
    | iProver_ARSWP_65 != iProver_top
    | iProver_ARSWP_64 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5558,c_17])).

cnf(c_6117,plain,
    ( v3_pre_topc(arAF0_k4_xboole_0_0,sK0) = iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),sK0) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | iProver_ARSWP_65 != iProver_top
    | iProver_ARSWP_64 != iProver_top ),
    inference(renaming,[status(thm)],[c_6116])).

cnf(c_4340,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0)) = arAF0_k3_subset_1_0
    | l1_struct_0(sK0) != iProver_top
    | iProver_ARSWP_64 != iProver_top ),
    inference(superposition,[status(thm)],[c_4093,c_3626])).

cnf(c_4756,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0)) = arAF0_k3_subset_1_0
    | iProver_ARSWP_64 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4340,c_17,c_35])).

cnf(c_4762,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0)) = arAF0_k3_subset_1_0
    | iProver_ARSWP_65 != iProver_top
    | iProver_ARSWP_64 != iProver_top ),
    inference(superposition,[status(thm)],[c_3977,c_4756])).

cnf(c_5522,plain,
    ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),sK0) = iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | iProver_ARSWP_65 != iProver_top
    | iProver_ARSWP_64 != iProver_top ),
    inference(superposition,[status(thm)],[c_4762,c_3623])).

cnf(c_6106,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),sK0) = iProver_top
    | v3_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
    | iProver_ARSWP_65 != iProver_top
    | iProver_ARSWP_64 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5522,c_17])).

cnf(c_6107,plain,
    ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),sK0) = iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | iProver_ARSWP_65 != iProver_top
    | iProver_ARSWP_64 != iProver_top ),
    inference(renaming,[status(thm)],[c_6106])).

cnf(c_5521,plain,
    ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) = iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),sK0) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | iProver_ARSWP_65 != iProver_top
    | iProver_ARSWP_64 != iProver_top ),
    inference(superposition,[status(thm)],[c_4762,c_3624])).

cnf(c_5957,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),sK0) != iProver_top
    | v3_pre_topc(arAF0_k3_subset_1_0,sK0) = iProver_top
    | iProver_ARSWP_65 != iProver_top
    | iProver_ARSWP_64 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5521,c_17])).

cnf(c_5958,plain,
    ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) = iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),sK0) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | iProver_ARSWP_65 != iProver_top
    | iProver_ARSWP_64 != iProver_top ),
    inference(renaming,[status(thm)],[c_5957])).

cnf(c_4764,plain,
    ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),sK0) = iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | iProver_ARSWP_64 != iProver_top ),
    inference(superposition,[status(thm)],[c_4756,c_3623])).

cnf(c_5791,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),sK0) = iProver_top
    | v3_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
    | iProver_ARSWP_64 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4764,c_17])).

cnf(c_5792,plain,
    ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),sK0) = iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | iProver_ARSWP_64 != iProver_top ),
    inference(renaming,[status(thm)],[c_5791])).

cnf(c_5799,plain,
    ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),sK0) = iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | iProver_ARSWP_65 != iProver_top
    | iProver_ARSWP_64 != iProver_top ),
    inference(superposition,[status(thm)],[c_3977,c_5792])).

cnf(c_4763,plain,
    ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) = iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),sK0) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | iProver_ARSWP_64 != iProver_top ),
    inference(superposition,[status(thm)],[c_4756,c_3624])).

cnf(c_5780,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),sK0) != iProver_top
    | v3_pre_topc(arAF0_k3_subset_1_0,sK0) = iProver_top
    | iProver_ARSWP_64 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4763,c_17])).

cnf(c_5781,plain,
    ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) = iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),sK0) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | iProver_ARSWP_64 != iProver_top ),
    inference(renaming,[status(thm)],[c_5780])).

cnf(c_5788,plain,
    ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) = iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),sK0) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | iProver_ARSWP_65 != iProver_top
    | iProver_ARSWP_64 != iProver_top ),
    inference(superposition,[status(thm)],[c_3977,c_5781])).

cnf(c_8,plain,
    ( ~ v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_293,plain,
    ( ~ v4_pre_topc(X0_44,X0_43)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43)))
    | ~ l1_pre_topc(X0_43)
    | k2_pre_topc(X0_43,X0_44) = X0_44 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_3628,plain,
    ( k2_pre_topc(X0_43,X0_44) = X0_44
    | v4_pre_topc(X0_44,X0_43) != iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43))) != iProver_top
    | l1_pre_topc(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_293])).

cnf(c_4622,plain,
    ( k2_pre_topc(sK0,arAF0_k4_xboole_0_0) = arAF0_k4_xboole_0_0
    | v4_pre_topc(arAF0_k4_xboole_0_0,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | iProver_ARSWP_65 != iProver_top
    | iProver_ARSWP_64 != iProver_top ),
    inference(superposition,[status(thm)],[c_4339,c_3628])).

cnf(c_5175,plain,
    ( v4_pre_topc(arAF0_k4_xboole_0_0,sK0) != iProver_top
    | k2_pre_topc(sK0,arAF0_k4_xboole_0_0) = arAF0_k4_xboole_0_0
    | iProver_ARSWP_65 != iProver_top
    | iProver_ARSWP_64 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4622,c_17])).

cnf(c_5176,plain,
    ( k2_pre_topc(sK0,arAF0_k4_xboole_0_0) = arAF0_k4_xboole_0_0
    | v4_pre_topc(arAF0_k4_xboole_0_0,sK0) != iProver_top
    | iProver_ARSWP_65 != iProver_top
    | iProver_ARSWP_64 != iProver_top ),
    inference(renaming,[status(thm)],[c_5175])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_299,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | k7_subset_1(X1_44,X0_44,X2_44) = k4_xboole_0(X0_44,X2_44) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_3429,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | ~ iProver_ARSWP_63
    | k7_subset_1(X1_44,X0_44,X2_44) = arAF0_k4_xboole_0_0 ),
    inference(arg_filter_abstr,[status(unp)],[c_299])).

cnf(c_3620,plain,
    ( k7_subset_1(X0_44,X1_44,X2_44) = arAF0_k4_xboole_0_0
    | m1_subset_1(X1_44,k1_zfmisc_1(X0_44)) != iProver_top
    | iProver_ARSWP_63 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3429])).

cnf(c_4945,plain,
    ( k7_subset_1(u1_struct_0(sK0),arAF0_k4_xboole_0_0,X0_44) = arAF0_k4_xboole_0_0
    | iProver_ARSWP_65 != iProver_top
    | iProver_ARSWP_64 != iProver_top
    | iProver_ARSWP_63 != iProver_top ),
    inference(superposition,[status(thm)],[c_4339,c_3620])).

cnf(c_4944,plain,
    ( k7_subset_1(u1_struct_0(sK0),arAF0_k3_subset_1_0,X0_44) = arAF0_k4_xboole_0_0
    | iProver_ARSWP_64 != iProver_top
    | iProver_ARSWP_63 != iProver_top ),
    inference(superposition,[status(thm)],[c_4093,c_3620])).

cnf(c_4943,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,X0_44) = arAF0_k4_xboole_0_0
    | iProver_ARSWP_63 != iProver_top ),
    inference(superposition,[status(thm)],[c_3632,c_3620])).

cnf(c_4209,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) = sK1
    | l1_struct_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3632,c_3626])).

cnf(c_34,plain,
    ( l1_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_336,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) = sK1 ),
    inference(instantiation,[status(thm)],[c_295])).

cnf(c_4485,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4209,c_16,c_15,c_34,c_336])).

cnf(c_4489,plain,
    ( v3_pre_topc(sK1,sK0) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4485,c_3623])).

cnf(c_4932,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) = iProver_top
    | v3_pre_topc(sK1,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4489,c_17])).

cnf(c_4933,plain,
    ( v3_pre_topc(sK1,sK0) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) = iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4932])).

cnf(c_4488,plain,
    ( v3_pre_topc(sK1,sK0) = iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4485,c_3624])).

cnf(c_4795,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) != iProver_top
    | v3_pre_topc(sK1,sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4488,c_17])).

cnf(c_4796,plain,
    ( v3_pre_topc(sK1,sK0) = iProver_top
    | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) != iProver_top
    | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4795])).

cnf(c_4341,plain,
    ( k2_pre_topc(sK0,arAF0_k3_subset_1_0) = arAF0_k3_subset_1_0
    | v4_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | iProver_ARSWP_64 != iProver_top ),
    inference(superposition,[status(thm)],[c_4093,c_3628])).

cnf(c_4648,plain,
    ( v4_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
    | k2_pre_topc(sK0,arAF0_k3_subset_1_0) = arAF0_k3_subset_1_0
    | iProver_ARSWP_64 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4341,c_17])).

cnf(c_4649,plain,
    ( k2_pre_topc(sK0,arAF0_k3_subset_1_0) = arAF0_k3_subset_1_0
    | v4_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
    | iProver_ARSWP_64 != iProver_top ),
    inference(renaming,[status(thm)],[c_4648])).

cnf(c_4655,plain,
    ( k2_pre_topc(sK0,arAF0_k3_subset_1_0) = arAF0_k3_subset_1_0
    | v4_pre_topc(arAF0_k4_xboole_0_0,sK0) != iProver_top
    | iProver_ARSWP_65 != iProver_top
    | iProver_ARSWP_64 != iProver_top ),
    inference(superposition,[status(thm)],[c_3977,c_4649])).

cnf(c_4100,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3632,c_3628])).

cnf(c_18,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_341,plain,
    ( k2_pre_topc(X0_43,X0_44) = X0_44
    | v4_pre_topc(X0_44,X0_43) != iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43))) != iProver_top
    | l1_pre_topc(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_293])).

cnf(c_343,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_341])).

cnf(c_4478,plain,
    ( v4_pre_topc(sK1,sK0) != iProver_top
    | k2_pre_topc(sK0,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4100,c_17,c_18,c_343])).

cnf(c_4479,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | v4_pre_topc(sK1,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4478])).

cnf(c_5560,plain,
    ( arAF0_k3_subset_1_0 = arAF0_k4_xboole_0_0
    | iProver_ARSWP_65 != iProver_top
    | iProver_ARSWP_64 != iProver_top ),
    inference(superposition,[status(thm)],[c_5550,c_4762])).

cnf(c_305,plain,
    ( X0_44 != X1_44
    | X2_44 != X1_44
    | X2_44 = X0_44 ),
    theory(equality)).

cnf(c_303,plain,
    ( X0_44 = X0_44 ),
    theory(equality)).

cnf(c_4118,plain,
    ( X0_44 != X1_44
    | X1_44 = X0_44 ),
    inference(resolution,[status(thm)],[c_305,c_303])).

cnf(c_4239,plain,
    ( ~ iProver_ARSWP_65
    | arAF0_k3_subset_1_0 = arAF0_k4_xboole_0_0 ),
    inference(resolution,[status(thm)],[c_4118,c_3896])).

cnf(c_4240,plain,
    ( arAF0_k3_subset_1_0 = arAF0_k4_xboole_0_0
    | iProver_ARSWP_65 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4239])).

cnf(c_5944,plain,
    ( iProver_ARSWP_65 != iProver_top
    | arAF0_k3_subset_1_0 = arAF0_k4_xboole_0_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5560,c_4240])).

cnf(c_5945,plain,
    ( arAF0_k3_subset_1_0 = arAF0_k4_xboole_0_0
    | iProver_ARSWP_65 != iProver_top ),
    inference(renaming,[status(thm)],[c_5944])).

cnf(c_288,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_3631,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_288])).

cnf(c_296,plain,
    ( l1_struct_0(X0_43)
    | ~ l1_pre_topc(X0_43) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_3625,plain,
    ( l1_struct_0(X0_43) = iProver_top
    | l1_pre_topc(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_296])).

cnf(c_3869,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3631,c_3625])).

cnf(c_12,negated_conjecture,
    ( v3_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_291,negated_conjecture,
    ( v3_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_3630,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))
    | v3_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_291])).

cnf(c_9,negated_conjecture,
    ( ~ v3_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_292,negated_conjecture,
    ( ~ v3_pre_topc(sK1,sK0)
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_3629,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))
    | v3_pre_topc(sK1,sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_292])).

cnf(c_7,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_294,plain,
    ( v4_pre_topc(X0_44,X0_43)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43)))
    | ~ v2_pre_topc(X0_43)
    | ~ l1_pre_topc(X0_43)
    | k2_pre_topc(X0_43,X0_44) != X0_44 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_3627,plain,
    ( k2_pre_topc(X0_43,X0_44) != X0_44
    | v4_pre_topc(X0_44,X0_43) = iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43))) != iProver_top
    | v2_pre_topc(X0_43) != iProver_top
    | l1_pre_topc(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_294])).

cnf(c_14,negated_conjecture,
    ( v3_pre_topc(sK1,sK0)
    | v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_290,negated_conjecture,
    ( v3_pre_topc(sK1,sK0)
    | v2_pre_topc(sK0) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_3633,plain,
    ( v3_pre_topc(sK1,sK0) = iProver_top
    | v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_290])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:30:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.69/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.69/0.99  
% 3.69/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.69/0.99  
% 3.69/0.99  ------  iProver source info
% 3.69/0.99  
% 3.69/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.69/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.69/0.99  git: non_committed_changes: false
% 3.69/0.99  git: last_make_outside_of_git: false
% 3.69/0.99  
% 3.69/0.99  ------ 
% 3.69/0.99  ------ Parsing...
% 3.69/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.69/0.99  
% 3.69/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.69/0.99  
% 3.69/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.69/0.99  
% 3.69/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.69/0.99  ------ Proving...
% 3.69/0.99  ------ Problem Properties 
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  clauses                                 14
% 3.69/0.99  conjectures                             5
% 3.69/0.99  EPR                                     3
% 3.69/0.99  Horn                                    12
% 3.69/0.99  unary                                   2
% 3.69/0.99  binary                                  7
% 3.69/0.99  lits                                    36
% 3.69/0.99  lits eq                                 7
% 3.69/0.99  fd_pure                                 0
% 3.69/0.99  fd_pseudo                               0
% 3.69/0.99  fd_cond                                 0
% 3.69/0.99  fd_pseudo_cond                          0
% 3.69/0.99  AC symbols                              0
% 3.69/0.99  
% 3.69/0.99  ------ Input Options Time Limit: Unbounded
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.69/0.99  Current options:
% 3.69/0.99  ------ 
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  ------ Proving...
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.69/0.99  
% 3.69/0.99  ------ Proving...
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.69/0.99  
% 3.69/0.99  ------ Proving...
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.69/0.99  
% 3.69/0.99  ------ Proving...
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  ------ Preprocessing... sf_s  rm: 12 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.69/0.99  
% 3.69/0.99  ------ Proving...
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  ------ Preprocessing... sf_s  rm: 12 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.69/0.99  
% 3.69/0.99  ------ Proving...
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.69/0.99  
% 3.69/0.99  ------ Proving...
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  ------ Preprocessing... sf_s  rm: 14 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.69/0.99  
% 3.69/0.99  ------ Proving...
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  ------ Preprocessing... sf_s  rm: 14 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.69/0.99  
% 3.69/0.99  ------ Proving...
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.69/0.99  
% 3.69/0.99  ------ Proving...
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  % SZS status CounterSatisfiable for theBenchmark.p
% 3.69/0.99  
% 3.69/0.99  % SZS output start Saturation for theBenchmark.p
% 3.69/0.99  
% 3.69/0.99  fof(f1,axiom,(
% 3.69/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f10,plain,(
% 3.69/0.99    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.69/0.99    inference(ennf_transformation,[],[f1])).
% 3.69/0.99  
% 3.69/0.99  fof(f24,plain,(
% 3.69/0.99    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.69/0.99    inference(cnf_transformation,[],[f10])).
% 3.69/0.99  
% 3.69/0.99  fof(f8,conjecture,(
% 3.69/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v2_pre_topc(X0)) => v3_pre_topc(X1,X0)) & (v3_pre_topc(X1,X0) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))))))),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f9,negated_conjecture,(
% 3.69/0.99    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v2_pre_topc(X0)) => v3_pre_topc(X1,X0)) & (v3_pre_topc(X1,X0) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1))))))),
% 3.69/0.99    inference(negated_conjecture,[],[f8])).
% 3.69/0.99  
% 3.69/0.99  fof(f18,plain,(
% 3.69/0.99    ? [X0] : (? [X1] : (((~v3_pre_topc(X1,X0) & (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v2_pre_topc(X0))) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.69/0.99    inference(ennf_transformation,[],[f9])).
% 3.69/0.99  
% 3.69/0.99  fof(f19,plain,(
% 3.69/0.99    ? [X0] : (? [X1] : (((~v3_pre_topc(X1,X0) & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v2_pre_topc(X0)) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 3.69/0.99    inference(flattening,[],[f18])).
% 3.69/0.99  
% 3.69/0.99  fof(f22,plain,(
% 3.69/0.99    ( ! [X0] : (? [X1] : (((~v3_pre_topc(X1,X0) & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v2_pre_topc(X0)) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (((~v3_pre_topc(sK1,X0) & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1)) & v2_pre_topc(X0)) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1)) & v3_pre_topc(sK1,X0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.69/0.99    introduced(choice_axiom,[])).
% 3.69/0.99  
% 3.69/0.99  fof(f21,plain,(
% 3.69/0.99    ? [X0] : (? [X1] : (((~v3_pre_topc(X1,X0) & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v2_pre_topc(X0)) | (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k2_pre_topc(X0,k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (((~v3_pre_topc(X1,sK0) & k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1)) & v2_pre_topc(sK0)) | (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1)) & v3_pre_topc(X1,sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 3.69/0.99    introduced(choice_axiom,[])).
% 3.69/0.99  
% 3.69/0.99  fof(f23,plain,(
% 3.69/0.99    (((~v3_pre_topc(sK1,sK0) & k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) & v2_pre_topc(sK0)) | (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) & v3_pre_topc(sK1,sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 3.69/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f22,f21])).
% 3.69/0.99  
% 3.69/0.99  fof(f34,plain,(
% 3.69/0.99    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.69/0.99    inference(cnf_transformation,[],[f23])).
% 3.69/0.99  
% 3.69/0.99  fof(f2,axiom,(
% 3.69/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f11,plain,(
% 3.69/0.99    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.69/0.99    inference(ennf_transformation,[],[f2])).
% 3.69/0.99  
% 3.69/0.99  fof(f25,plain,(
% 3.69/0.99    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.69/0.99    inference(cnf_transformation,[],[f11])).
% 3.69/0.99  
% 3.69/0.99  fof(f6,axiom,(
% 3.69/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1))),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f15,plain,(
% 3.69/0.99    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 3.69/0.99    inference(ennf_transformation,[],[f6])).
% 3.69/0.99  
% 3.69/0.99  fof(f30,plain,(
% 3.69/0.99    ( ! [X0,X1] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f15])).
% 3.69/0.99  
% 3.69/0.99  fof(f33,plain,(
% 3.69/0.99    l1_pre_topc(sK0)),
% 3.69/0.99    inference(cnf_transformation,[],[f23])).
% 3.69/0.99  
% 3.69/0.99  fof(f5,axiom,(
% 3.69/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f14,plain,(
% 3.69/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 3.69/0.99    inference(ennf_transformation,[],[f5])).
% 3.69/0.99  
% 3.69/0.99  fof(f29,plain,(
% 3.69/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f14])).
% 3.69/0.99  
% 3.69/0.99  fof(f4,axiom,(
% 3.69/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0))))),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f13,plain,(
% 3.69/0.99    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.69/0.99    inference(ennf_transformation,[],[f4])).
% 3.69/0.99  
% 3.69/0.99  fof(f20,plain,(
% 3.69/0.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)) & (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.69/0.99    inference(nnf_transformation,[],[f13])).
% 3.69/0.99  
% 3.69/0.99  fof(f28,plain,(
% 3.69/0.99    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f20])).
% 3.69/0.99  
% 3.69/0.99  fof(f27,plain,(
% 3.69/0.99    ( ! [X0,X1] : (v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f20])).
% 3.69/0.99  
% 3.69/0.99  fof(f7,axiom,(
% 3.69/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f16,plain,(
% 3.69/0.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.69/0.99    inference(ennf_transformation,[],[f7])).
% 3.69/0.99  
% 3.69/0.99  fof(f17,plain,(
% 3.69/0.99    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.69/0.99    inference(flattening,[],[f16])).
% 3.69/0.99  
% 3.69/0.99  fof(f31,plain,(
% 3.69/0.99    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f17])).
% 3.69/0.99  
% 3.69/0.99  fof(f3,axiom,(
% 3.69/0.99    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.69/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.69/0.99  
% 3.69/0.99  fof(f12,plain,(
% 3.69/0.99    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.69/0.99    inference(ennf_transformation,[],[f3])).
% 3.69/0.99  
% 3.69/0.99  fof(f26,plain,(
% 3.69/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.69/0.99    inference(cnf_transformation,[],[f12])).
% 3.69/0.99  
% 3.69/0.99  fof(f37,plain,(
% 3.69/0.99    k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) | v3_pre_topc(sK1,sK0)),
% 3.69/0.99    inference(cnf_transformation,[],[f23])).
% 3.69/0.99  
% 3.69/0.99  fof(f40,plain,(
% 3.69/0.99    ~v3_pre_topc(sK1,sK0) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))),
% 3.69/0.99    inference(cnf_transformation,[],[f23])).
% 3.69/0.99  
% 3.69/0.99  fof(f32,plain,(
% 3.69/0.99    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.69/0.99    inference(cnf_transformation,[],[f17])).
% 3.69/0.99  
% 3.69/0.99  fof(f35,plain,(
% 3.69/0.99    v2_pre_topc(sK0) | v3_pre_topc(sK1,sK0)),
% 3.69/0.99    inference(cnf_transformation,[],[f23])).
% 3.69/0.99  
% 3.69/0.99  cnf(c_168,plain,( X0_2 = X0_2 ),theory(equality) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_0,plain,
% 3.69/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.69/0.99      | k4_xboole_0(X1,X0) = k3_subset_1(X1,X0) ),
% 3.69/0.99      inference(cnf_transformation,[],[f24]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_301,plain,
% 3.69/0.99      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
% 3.69/0.99      | k4_xboole_0(X1_44,X0_44) = k3_subset_1(X1_44,X0_44) ),
% 3.69/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3431,plain,
% 3.69/0.99      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
% 3.69/0.99      | ~ iProver_ARSWP_65
% 3.69/0.99      | arAF0_k4_xboole_0_0 = arAF0_k3_subset_1_0 ),
% 3.69/0.99      inference(arg_filter_abstr,[status(unp)],[c_301]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3618,plain,
% 3.69/0.99      ( arAF0_k4_xboole_0_0 = arAF0_k3_subset_1_0
% 3.69/0.99      | m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) != iProver_top
% 3.69/0.99      | iProver_ARSWP_65 != iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_3431]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_15,negated_conjecture,
% 3.69/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.69/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_289,negated_conjecture,
% 3.69/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
% 3.69/0.99      inference(subtyping,[status(esa)],[c_15]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3896,plain,
% 3.69/0.99      ( ~ iProver_ARSWP_65 | arAF0_k4_xboole_0_0 = arAF0_k3_subset_1_0 ),
% 3.69/0.99      inference(resolution,[status(thm)],[c_3431,c_289]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3897,plain,
% 3.69/0.99      ( arAF0_k4_xboole_0_0 = arAF0_k3_subset_1_0
% 3.69/0.99      | iProver_ARSWP_65 != iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_3896]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3977,plain,
% 3.69/0.99      ( arAF0_k4_xboole_0_0 = arAF0_k3_subset_1_0
% 3.69/0.99      | iProver_ARSWP_65 != iProver_top ),
% 3.69/0.99      inference(global_propositional_subsumption,[status(thm)],[c_3618,c_3897]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3632,plain,
% 3.69/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_289]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_1,plain,
% 3.69/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.69/0.99      | m1_subset_1(k3_subset_1(X1,X0),k1_zfmisc_1(X1)) ),
% 3.69/0.99      inference(cnf_transformation,[],[f25]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_300,plain,
% 3.69/0.99      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
% 3.69/0.99      | m1_subset_1(k3_subset_1(X1_44,X0_44),k1_zfmisc_1(X1_44)) ),
% 3.69/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3430,plain,
% 3.69/0.99      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
% 3.69/0.99      | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(X1_44))
% 3.69/0.99      | ~ iProver_ARSWP_64 ),
% 3.69/0.99      inference(arg_filter_abstr,[status(unp)],[c_300]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3619,plain,
% 3.69/0.99      ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) != iProver_top
% 3.69/0.99      | m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(X1_44)) = iProver_top
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_3430]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4093,plain,
% 3.69/0.99      ( m1_subset_1(arAF0_k3_subset_1_0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_3632,c_3619]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4339,plain,
% 3.69/0.99      ( m1_subset_1(arAF0_k4_xboole_0_0,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top
% 3.69/0.99      | iProver_ARSWP_65 != iProver_top
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_3977,c_4093]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_6,plain,
% 3.69/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/0.99      | ~ l1_struct_0(X1)
% 3.69/0.99      | k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),k7_subset_1(u1_struct_0(X1),k2_struct_0(X1),X0)) = X0 ),
% 3.69/0.99      inference(cnf_transformation,[],[f30]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_295,plain,
% 3.69/0.99      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43)))
% 3.69/0.99      | ~ l1_struct_0(X0_43)
% 3.69/0.99      | k7_subset_1(u1_struct_0(X0_43),k2_struct_0(X0_43),k7_subset_1(u1_struct_0(X0_43),k2_struct_0(X0_43),X0_44)) = X0_44 ),
% 3.69/0.99      inference(subtyping,[status(esa)],[c_6]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3626,plain,
% 3.69/0.99      ( k7_subset_1(u1_struct_0(X0_43),k2_struct_0(X0_43),k7_subset_1(u1_struct_0(X0_43),k2_struct_0(X0_43),X0_44)) = X0_44
% 3.69/0.99      | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43))) != iProver_top
% 3.69/0.99      | l1_struct_0(X0_43) != iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_295]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4621,plain,
% 3.69/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0)) = arAF0_k4_xboole_0_0
% 3.69/0.99      | l1_struct_0(sK0) != iProver_top
% 3.69/0.99      | iProver_ARSWP_65 != iProver_top
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_4339,c_3626]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_16,negated_conjecture,
% 3.69/0.99      ( l1_pre_topc(sK0) ),
% 3.69/0.99      inference(cnf_transformation,[],[f33]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_17,plain,
% 3.69/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5,plain,
% 3.69/0.99      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 3.69/0.99      inference(cnf_transformation,[],[f29]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_33,plain,
% 3.69/0.99      ( l1_struct_0(X0) = iProver_top | l1_pre_topc(X0) != iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_35,plain,
% 3.69/0.99      ( l1_struct_0(sK0) = iProver_top | l1_pre_topc(sK0) != iProver_top ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_33]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5550,plain,
% 3.69/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0)) = arAF0_k4_xboole_0_0
% 3.69/0.99      | iProver_ARSWP_65 != iProver_top
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top ),
% 3.69/0.99      inference(global_propositional_subsumption,
% 3.69/0.99                [status(thm)],
% 3.69/0.99                [c_4621,c_17,c_35]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3,plain,
% 3.69/0.99      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
% 3.69/0.99      | v4_pre_topc(X1,X0)
% 3.69/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.69/0.99      | ~ l1_pre_topc(X0) ),
% 3.69/0.99      inference(cnf_transformation,[],[f28]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_298,plain,
% 3.69/0.99      ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0_43),k2_struct_0(X0_43),X0_44),X0_43)
% 3.69/0.99      | v4_pre_topc(X0_44,X0_43)
% 3.69/0.99      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43)))
% 3.69/0.99      | ~ l1_pre_topc(X0_43) ),
% 3.69/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3623,plain,
% 3.69/0.99      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0_43),k2_struct_0(X0_43),X0_44),X0_43) != iProver_top
% 3.69/0.99      | v4_pre_topc(X0_44,X0_43) = iProver_top
% 3.69/0.99      | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43))) != iProver_top
% 3.69/0.99      | l1_pre_topc(X0_43) != iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_298]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5559,plain,
% 3.69/0.99      ( v3_pre_topc(arAF0_k4_xboole_0_0,sK0) != iProver_top
% 3.69/0.99      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),sK0) = iProver_top
% 3.69/0.99      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.69/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.69/0.99      | iProver_ARSWP_65 != iProver_top
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_5550,c_3623]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_6271,plain,
% 3.69/0.99      ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.69/0.99      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),sK0) = iProver_top
% 3.69/0.99      | v3_pre_topc(arAF0_k4_xboole_0_0,sK0) != iProver_top
% 3.69/0.99      | iProver_ARSWP_65 != iProver_top
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top ),
% 3.69/0.99      inference(global_propositional_subsumption,[status(thm)],[c_5559,c_17]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_6272,plain,
% 3.69/0.99      ( v3_pre_topc(arAF0_k4_xboole_0_0,sK0) != iProver_top
% 3.69/0.99      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),sK0) = iProver_top
% 3.69/0.99      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.69/0.99      | iProver_ARSWP_65 != iProver_top
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top ),
% 3.69/0.99      inference(renaming,[status(thm)],[c_6271]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4,plain,
% 3.69/0.99      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
% 3.69/0.99      | ~ v4_pre_topc(X1,X0)
% 3.69/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 3.69/0.99      | ~ l1_pre_topc(X0) ),
% 3.69/0.99      inference(cnf_transformation,[],[f27]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_297,plain,
% 3.69/0.99      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0_43),k2_struct_0(X0_43),X0_44),X0_43)
% 3.69/0.99      | ~ v4_pre_topc(X0_44,X0_43)
% 3.69/0.99      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43)))
% 3.69/0.99      | ~ l1_pre_topc(X0_43) ),
% 3.69/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3624,plain,
% 3.69/0.99      ( v3_pre_topc(k7_subset_1(u1_struct_0(X0_43),k2_struct_0(X0_43),X0_44),X0_43) = iProver_top
% 3.69/0.99      | v4_pre_topc(X0_44,X0_43) != iProver_top
% 3.69/0.99      | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43))) != iProver_top
% 3.69/0.99      | l1_pre_topc(X0_43) != iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_297]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5558,plain,
% 3.69/0.99      ( v3_pre_topc(arAF0_k4_xboole_0_0,sK0) = iProver_top
% 3.69/0.99      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),sK0) != iProver_top
% 3.69/0.99      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.69/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.69/0.99      | iProver_ARSWP_65 != iProver_top
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_5550,c_3624]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_6116,plain,
% 3.69/0.99      ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.69/0.99      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),sK0) != iProver_top
% 3.69/0.99      | v3_pre_topc(arAF0_k4_xboole_0_0,sK0) = iProver_top
% 3.69/0.99      | iProver_ARSWP_65 != iProver_top
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top ),
% 3.69/0.99      inference(global_propositional_subsumption,[status(thm)],[c_5558,c_17]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_6117,plain,
% 3.69/0.99      ( v3_pre_topc(arAF0_k4_xboole_0_0,sK0) = iProver_top
% 3.69/0.99      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),sK0) != iProver_top
% 3.69/0.99      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.69/0.99      | iProver_ARSWP_65 != iProver_top
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top ),
% 3.69/0.99      inference(renaming,[status(thm)],[c_6116]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4340,plain,
% 3.69/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0)) = arAF0_k3_subset_1_0
% 3.69/0.99      | l1_struct_0(sK0) != iProver_top
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_4093,c_3626]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4756,plain,
% 3.69/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0)) = arAF0_k3_subset_1_0
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top ),
% 3.69/0.99      inference(global_propositional_subsumption,
% 3.69/0.99                [status(thm)],
% 3.69/0.99                [c_4340,c_17,c_35]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4762,plain,
% 3.69/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0)) = arAF0_k3_subset_1_0
% 3.69/0.99      | iProver_ARSWP_65 != iProver_top
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_3977,c_4756]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5522,plain,
% 3.69/0.99      ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
% 3.69/0.99      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),sK0) = iProver_top
% 3.69/0.99      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.69/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.69/0.99      | iProver_ARSWP_65 != iProver_top
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_4762,c_3623]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_6106,plain,
% 3.69/0.99      ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.69/0.99      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),sK0) = iProver_top
% 3.69/0.99      | v3_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
% 3.69/0.99      | iProver_ARSWP_65 != iProver_top
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top ),
% 3.69/0.99      inference(global_propositional_subsumption,[status(thm)],[c_5522,c_17]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_6107,plain,
% 3.69/0.99      ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
% 3.69/0.99      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),sK0) = iProver_top
% 3.69/0.99      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.69/0.99      | iProver_ARSWP_65 != iProver_top
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top ),
% 3.69/0.99      inference(renaming,[status(thm)],[c_6106]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5521,plain,
% 3.69/0.99      ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) = iProver_top
% 3.69/0.99      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),sK0) != iProver_top
% 3.69/0.99      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.69/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.69/0.99      | iProver_ARSWP_65 != iProver_top
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_4762,c_3624]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5957,plain,
% 3.69/0.99      ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.69/0.99      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),sK0) != iProver_top
% 3.69/0.99      | v3_pre_topc(arAF0_k3_subset_1_0,sK0) = iProver_top
% 3.69/0.99      | iProver_ARSWP_65 != iProver_top
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top ),
% 3.69/0.99      inference(global_propositional_subsumption,[status(thm)],[c_5521,c_17]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5958,plain,
% 3.69/0.99      ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) = iProver_top
% 3.69/0.99      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),sK0) != iProver_top
% 3.69/0.99      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.69/0.99      | iProver_ARSWP_65 != iProver_top
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top ),
% 3.69/0.99      inference(renaming,[status(thm)],[c_5957]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4764,plain,
% 3.69/0.99      ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
% 3.69/0.99      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),sK0) = iProver_top
% 3.69/0.99      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.69/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_4756,c_3623]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5791,plain,
% 3.69/0.99      ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.69/0.99      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),sK0) = iProver_top
% 3.69/0.99      | v3_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top ),
% 3.69/0.99      inference(global_propositional_subsumption,[status(thm)],[c_4764,c_17]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5792,plain,
% 3.69/0.99      ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
% 3.69/0.99      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),sK0) = iProver_top
% 3.69/0.99      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top ),
% 3.69/0.99      inference(renaming,[status(thm)],[c_5791]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5799,plain,
% 3.69/0.99      ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
% 3.69/0.99      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),sK0) = iProver_top
% 3.69/0.99      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.69/0.99      | iProver_ARSWP_65 != iProver_top
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_3977,c_5792]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4763,plain,
% 3.69/0.99      ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) = iProver_top
% 3.69/0.99      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),sK0) != iProver_top
% 3.69/0.99      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.69/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_4756,c_3624]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5780,plain,
% 3.69/0.99      ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.69/0.99      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),sK0) != iProver_top
% 3.69/0.99      | v3_pre_topc(arAF0_k3_subset_1_0,sK0) = iProver_top
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top ),
% 3.69/0.99      inference(global_propositional_subsumption,[status(thm)],[c_4763,c_17]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5781,plain,
% 3.69/0.99      ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) = iProver_top
% 3.69/0.99      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),sK0) != iProver_top
% 3.69/0.99      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top ),
% 3.69/0.99      inference(renaming,[status(thm)],[c_5780]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5788,plain,
% 3.69/0.99      ( v3_pre_topc(arAF0_k3_subset_1_0,sK0) = iProver_top
% 3.69/0.99      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k3_subset_1_0),sK0) != iProver_top
% 3.69/0.99      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),arAF0_k4_xboole_0_0),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.69/0.99      | iProver_ARSWP_65 != iProver_top
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_3977,c_5781]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_8,plain,
% 3.69/0.99      ( ~ v4_pre_topc(X0,X1)
% 3.69/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/0.99      | ~ l1_pre_topc(X1)
% 3.69/0.99      | k2_pre_topc(X1,X0) = X0 ),
% 3.69/0.99      inference(cnf_transformation,[],[f31]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_293,plain,
% 3.69/0.99      ( ~ v4_pre_topc(X0_44,X0_43)
% 3.69/0.99      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43)))
% 3.69/0.99      | ~ l1_pre_topc(X0_43)
% 3.69/0.99      | k2_pre_topc(X0_43,X0_44) = X0_44 ),
% 3.69/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3628,plain,
% 3.69/0.99      ( k2_pre_topc(X0_43,X0_44) = X0_44
% 3.69/0.99      | v4_pre_topc(X0_44,X0_43) != iProver_top
% 3.69/0.99      | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43))) != iProver_top
% 3.69/0.99      | l1_pre_topc(X0_43) != iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_293]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4622,plain,
% 3.69/0.99      ( k2_pre_topc(sK0,arAF0_k4_xboole_0_0) = arAF0_k4_xboole_0_0
% 3.69/0.99      | v4_pre_topc(arAF0_k4_xboole_0_0,sK0) != iProver_top
% 3.69/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.69/0.99      | iProver_ARSWP_65 != iProver_top
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_4339,c_3628]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5175,plain,
% 3.69/0.99      ( v4_pre_topc(arAF0_k4_xboole_0_0,sK0) != iProver_top
% 3.69/0.99      | k2_pre_topc(sK0,arAF0_k4_xboole_0_0) = arAF0_k4_xboole_0_0
% 3.69/0.99      | iProver_ARSWP_65 != iProver_top
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top ),
% 3.69/0.99      inference(global_propositional_subsumption,[status(thm)],[c_4622,c_17]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5176,plain,
% 3.69/0.99      ( k2_pre_topc(sK0,arAF0_k4_xboole_0_0) = arAF0_k4_xboole_0_0
% 3.69/0.99      | v4_pre_topc(arAF0_k4_xboole_0_0,sK0) != iProver_top
% 3.69/0.99      | iProver_ARSWP_65 != iProver_top
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top ),
% 3.69/0.99      inference(renaming,[status(thm)],[c_5175]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_2,plain,
% 3.69/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.69/0.99      | k7_subset_1(X1,X0,X2) = k4_xboole_0(X0,X2) ),
% 3.69/0.99      inference(cnf_transformation,[],[f26]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_299,plain,
% 3.69/0.99      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
% 3.69/0.99      | k7_subset_1(X1_44,X0_44,X2_44) = k4_xboole_0(X0_44,X2_44) ),
% 3.69/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3429,plain,
% 3.69/0.99      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
% 3.69/0.99      | ~ iProver_ARSWP_63
% 3.69/0.99      | k7_subset_1(X1_44,X0_44,X2_44) = arAF0_k4_xboole_0_0 ),
% 3.69/0.99      inference(arg_filter_abstr,[status(unp)],[c_299]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3620,plain,
% 3.69/0.99      ( k7_subset_1(X0_44,X1_44,X2_44) = arAF0_k4_xboole_0_0
% 3.69/0.99      | m1_subset_1(X1_44,k1_zfmisc_1(X0_44)) != iProver_top
% 3.69/0.99      | iProver_ARSWP_63 != iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_3429]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4945,plain,
% 3.69/0.99      ( k7_subset_1(u1_struct_0(sK0),arAF0_k4_xboole_0_0,X0_44) = arAF0_k4_xboole_0_0
% 3.69/0.99      | iProver_ARSWP_65 != iProver_top
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top
% 3.69/0.99      | iProver_ARSWP_63 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_4339,c_3620]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4944,plain,
% 3.69/0.99      ( k7_subset_1(u1_struct_0(sK0),arAF0_k3_subset_1_0,X0_44) = arAF0_k4_xboole_0_0
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top
% 3.69/0.99      | iProver_ARSWP_63 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_4093,c_3620]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4943,plain,
% 3.69/0.99      ( k7_subset_1(u1_struct_0(sK0),sK1,X0_44) = arAF0_k4_xboole_0_0
% 3.69/0.99      | iProver_ARSWP_63 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_3632,c_3620]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4209,plain,
% 3.69/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) = sK1
% 3.69/0.99      | l1_struct_0(sK0) != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_3632,c_3626]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_34,plain,
% 3.69/0.99      ( l1_struct_0(sK0) | ~ l1_pre_topc(sK0) ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_336,plain,
% 3.69/0.99      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
% 3.69/0.99      | ~ l1_struct_0(sK0)
% 3.69/0.99      | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) = sK1 ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_295]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4485,plain,
% 3.69/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) = sK1 ),
% 3.69/0.99      inference(global_propositional_subsumption,
% 3.69/0.99                [status(thm)],
% 3.69/0.99                [c_4209,c_16,c_15,c_34,c_336]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4489,plain,
% 3.69/0.99      ( v3_pre_topc(sK1,sK0) != iProver_top
% 3.69/0.99      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) = iProver_top
% 3.69/0.99      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.69/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_4485,c_3623]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4932,plain,
% 3.69/0.99      ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.69/0.99      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) = iProver_top
% 3.69/0.99      | v3_pre_topc(sK1,sK0) != iProver_top ),
% 3.69/0.99      inference(global_propositional_subsumption,[status(thm)],[c_4489,c_17]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4933,plain,
% 3.69/0.99      ( v3_pre_topc(sK1,sK0) != iProver_top
% 3.69/0.99      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) = iProver_top
% 3.69/0.99      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.69/0.99      inference(renaming,[status(thm)],[c_4932]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4488,plain,
% 3.69/0.99      ( v3_pre_topc(sK1,sK0) = iProver_top
% 3.69/0.99      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) != iProver_top
% 3.69/0.99      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.69/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_4485,c_3624]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4795,plain,
% 3.69/0.99      ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.69/0.99      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) != iProver_top
% 3.69/0.99      | v3_pre_topc(sK1,sK0) = iProver_top ),
% 3.69/0.99      inference(global_propositional_subsumption,[status(thm)],[c_4488,c_17]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4796,plain,
% 3.69/0.99      ( v3_pre_topc(sK1,sK0) = iProver_top
% 3.69/0.99      | v4_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0) != iProver_top
% 3.69/0.99      | m1_subset_1(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top ),
% 3.69/0.99      inference(renaming,[status(thm)],[c_4795]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4341,plain,
% 3.69/0.99      ( k2_pre_topc(sK0,arAF0_k3_subset_1_0) = arAF0_k3_subset_1_0
% 3.69/0.99      | v4_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
% 3.69/0.99      | l1_pre_topc(sK0) != iProver_top
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_4093,c_3628]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4648,plain,
% 3.69/0.99      ( v4_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
% 3.69/0.99      | k2_pre_topc(sK0,arAF0_k3_subset_1_0) = arAF0_k3_subset_1_0
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top ),
% 3.69/0.99      inference(global_propositional_subsumption,[status(thm)],[c_4341,c_17]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4649,plain,
% 3.69/0.99      ( k2_pre_topc(sK0,arAF0_k3_subset_1_0) = arAF0_k3_subset_1_0
% 3.69/0.99      | v4_pre_topc(arAF0_k3_subset_1_0,sK0) != iProver_top
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top ),
% 3.69/0.99      inference(renaming,[status(thm)],[c_4648]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4655,plain,
% 3.69/0.99      ( k2_pre_topc(sK0,arAF0_k3_subset_1_0) = arAF0_k3_subset_1_0
% 3.69/0.99      | v4_pre_topc(arAF0_k4_xboole_0_0,sK0) != iProver_top
% 3.69/0.99      | iProver_ARSWP_65 != iProver_top
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_3977,c_4649]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4100,plain,
% 3.69/0.99      ( k2_pre_topc(sK0,sK1) = sK1
% 3.69/0.99      | v4_pre_topc(sK1,sK0) != iProver_top
% 3.69/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_3632,c_3628]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_18,plain,
% 3.69/0.99      ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) = iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_341,plain,
% 3.69/0.99      ( k2_pre_topc(X0_43,X0_44) = X0_44
% 3.69/0.99      | v4_pre_topc(X0_44,X0_43) != iProver_top
% 3.69/0.99      | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43))) != iProver_top
% 3.69/0.99      | l1_pre_topc(X0_43) != iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_293]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_343,plain,
% 3.69/0.99      ( k2_pre_topc(sK0,sK1) = sK1
% 3.69/0.99      | v4_pre_topc(sK1,sK0) != iProver_top
% 3.69/0.99      | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
% 3.69/0.99      | l1_pre_topc(sK0) != iProver_top ),
% 3.69/0.99      inference(instantiation,[status(thm)],[c_341]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4478,plain,
% 3.69/0.99      ( v4_pre_topc(sK1,sK0) != iProver_top | k2_pre_topc(sK0,sK1) = sK1 ),
% 3.69/0.99      inference(global_propositional_subsumption,
% 3.69/0.99                [status(thm)],
% 3.69/0.99                [c_4100,c_17,c_18,c_343]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4479,plain,
% 3.69/0.99      ( k2_pre_topc(sK0,sK1) = sK1 | v4_pre_topc(sK1,sK0) != iProver_top ),
% 3.69/0.99      inference(renaming,[status(thm)],[c_4478]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5560,plain,
% 3.69/0.99      ( arAF0_k3_subset_1_0 = arAF0_k4_xboole_0_0
% 3.69/0.99      | iProver_ARSWP_65 != iProver_top
% 3.69/0.99      | iProver_ARSWP_64 != iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_5550,c_4762]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_305,plain,
% 3.69/0.99      ( X0_44 != X1_44 | X2_44 != X1_44 | X2_44 = X0_44 ),
% 3.69/0.99      theory(equality) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_303,plain,( X0_44 = X0_44 ),theory(equality) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4118,plain,
% 3.69/0.99      ( X0_44 != X1_44 | X1_44 = X0_44 ),
% 3.69/0.99      inference(resolution,[status(thm)],[c_305,c_303]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4239,plain,
% 3.69/0.99      ( ~ iProver_ARSWP_65 | arAF0_k3_subset_1_0 = arAF0_k4_xboole_0_0 ),
% 3.69/0.99      inference(resolution,[status(thm)],[c_4118,c_3896]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_4240,plain,
% 3.69/0.99      ( arAF0_k3_subset_1_0 = arAF0_k4_xboole_0_0
% 3.69/0.99      | iProver_ARSWP_65 != iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_4239]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5944,plain,
% 3.69/0.99      ( iProver_ARSWP_65 != iProver_top
% 3.69/0.99      | arAF0_k3_subset_1_0 = arAF0_k4_xboole_0_0 ),
% 3.69/0.99      inference(global_propositional_subsumption,[status(thm)],[c_5560,c_4240]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_5945,plain,
% 3.69/0.99      ( arAF0_k3_subset_1_0 = arAF0_k4_xboole_0_0
% 3.69/0.99      | iProver_ARSWP_65 != iProver_top ),
% 3.69/0.99      inference(renaming,[status(thm)],[c_5944]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_288,negated_conjecture,
% 3.69/0.99      ( l1_pre_topc(sK0) ),
% 3.69/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3631,plain,
% 3.69/0.99      ( l1_pre_topc(sK0) = iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_288]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_296,plain,
% 3.69/0.99      ( l1_struct_0(X0_43) | ~ l1_pre_topc(X0_43) ),
% 3.69/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3625,plain,
% 3.69/0.99      ( l1_struct_0(X0_43) = iProver_top | l1_pre_topc(X0_43) != iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_296]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3869,plain,
% 3.69/0.99      ( l1_struct_0(sK0) = iProver_top ),
% 3.69/0.99      inference(superposition,[status(thm)],[c_3631,c_3625]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_12,negated_conjecture,
% 3.69/0.99      ( v3_pre_topc(sK1,sK0)
% 3.69/0.99      | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) ),
% 3.69/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_291,negated_conjecture,
% 3.69/0.99      ( v3_pre_topc(sK1,sK0)
% 3.69/0.99      | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) ),
% 3.69/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3630,plain,
% 3.69/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))
% 3.69/0.99      | v3_pre_topc(sK1,sK0) = iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_291]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_9,negated_conjecture,
% 3.69/0.99      ( ~ v3_pre_topc(sK1,sK0)
% 3.69/0.99      | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) ),
% 3.69/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_292,negated_conjecture,
% 3.69/0.99      ( ~ v3_pre_topc(sK1,sK0)
% 3.69/0.99      | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) ),
% 3.69/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3629,plain,
% 3.69/0.99      ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k2_pre_topc(sK0,k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))
% 3.69/0.99      | v3_pre_topc(sK1,sK0) != iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_292]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_7,plain,
% 3.69/0.99      ( v4_pre_topc(X0,X1)
% 3.69/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.69/0.99      | ~ v2_pre_topc(X1)
% 3.69/0.99      | ~ l1_pre_topc(X1)
% 3.69/0.99      | k2_pre_topc(X1,X0) != X0 ),
% 3.69/0.99      inference(cnf_transformation,[],[f32]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_294,plain,
% 3.69/0.99      ( v4_pre_topc(X0_44,X0_43)
% 3.69/0.99      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43)))
% 3.69/0.99      | ~ v2_pre_topc(X0_43)
% 3.69/0.99      | ~ l1_pre_topc(X0_43)
% 3.69/0.99      | k2_pre_topc(X0_43,X0_44) != X0_44 ),
% 3.69/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3627,plain,
% 3.69/0.99      ( k2_pre_topc(X0_43,X0_44) != X0_44
% 3.69/0.99      | v4_pre_topc(X0_44,X0_43) = iProver_top
% 3.69/0.99      | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(X0_43))) != iProver_top
% 3.69/0.99      | v2_pre_topc(X0_43) != iProver_top
% 3.69/0.99      | l1_pre_topc(X0_43) != iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_294]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_14,negated_conjecture,
% 3.69/0.99      ( v3_pre_topc(sK1,sK0) | v2_pre_topc(sK0) ),
% 3.69/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_290,negated_conjecture,
% 3.69/0.99      ( v3_pre_topc(sK1,sK0) | v2_pre_topc(sK0) ),
% 3.69/0.99      inference(subtyping,[status(esa)],[c_14]) ).
% 3.69/0.99  
% 3.69/0.99  cnf(c_3633,plain,
% 3.69/0.99      ( v3_pre_topc(sK1,sK0) = iProver_top | v2_pre_topc(sK0) = iProver_top ),
% 3.69/0.99      inference(predicate_to_equality,[status(thm)],[c_290]) ).
% 3.69/0.99  
% 3.69/0.99  
% 3.69/0.99  % SZS output end Saturation for theBenchmark.p
% 3.69/0.99  
% 3.69/0.99  ------                               Statistics
% 3.69/0.99  
% 3.69/0.99  ------ Selected
% 3.69/0.99  
% 3.69/0.99  total_time:                             0.185
% 3.69/0.99  
%------------------------------------------------------------------------------
