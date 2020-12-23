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
% DateTime   : Thu Dec  3 12:25:13 EST 2020

% Result     : Theorem 3.54s
% Output     : CNFRefutation 3.54s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 313 expanded)
%              Number of clauses        :   81 ( 101 expanded)
%              Number of leaves         :   27 (  76 expanded)
%              Depth                    :   22
%              Number of atoms          :  362 ( 823 expanded)
%              Number of equality atoms :  155 ( 216 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
     => ( v1_zfmisc_1(X0)
        & v1_subset_1(k6_domain_1(X0,sK3),X0)
        & m1_subset_1(sK3,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_zfmisc_1(X0)
            & v1_subset_1(k6_domain_1(X0,X1),X0)
            & m1_subset_1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( v1_zfmisc_1(sK2)
          & v1_subset_1(k6_domain_1(sK2,X1),sK2)
          & m1_subset_1(X1,sK2) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,
    ( v1_zfmisc_1(sK2)
    & v1_subset_1(k6_domain_1(sK2,sK3),sK2)
    & m1_subset_1(sK3,sK2)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f44,f57,f56])).

fof(f91,plain,(
    m1_subset_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f24,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
         => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
          | v1_xboole_0(k3_xboole_0(X0,X1)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
          | v1_xboole_0(k3_xboole_0(X0,X1)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | v1_xboole_0(k3_xboole_0(X0,X1))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f15,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f94,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f78,f75])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | v1_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X1)))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f89,f94])).

fof(f93,plain,(
    v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f90,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f64,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f53])).

fof(f67,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f92,plain,(
    v1_subset_1(k6_domain_1(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f23,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f105,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f84,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f86,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f81,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f100,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f73,f75,f75])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f9])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(ennf_transformation,[],[f27])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f95,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f68,f94])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) != X0 ) ),
    inference(definition_unfolding,[],[f72,f95])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f31])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f97,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f74,f75])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X1,X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f85,f97])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f96,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f76,f75])).

fof(f98,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f69,f96])).

fof(f14,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f101,plain,(
    ! [X0,X1] : k1_xboole_0 != k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),X1)) ),
    inference(definition_unfolding,[],[f77,f96,f97])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1515,plain,
    ( m1_subset_1(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1518,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1519,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2579,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r1_tarski(k6_domain_1(X1,X0),X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1518,c_1519])).

cnf(c_24,plain,
    ( r1_tarski(X0,X1)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | v1_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_25,negated_conjecture,
    ( v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_397,plain,
    ( r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | v1_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X1)))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_25])).

cnf(c_398,plain,
    ( r1_tarski(sK2,X0)
    | v1_xboole_0(k1_setfam_1(k1_enumset1(sK2,sK2,X0)))
    | v1_xboole_0(sK2) ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_28,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_400,plain,
    ( v1_xboole_0(k1_setfam_1(k1_enumset1(sK2,sK2,X0)))
    | r1_tarski(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_398,c_28])).

cnf(c_401,plain,
    ( r1_tarski(sK2,X0)
    | v1_xboole_0(k1_setfam_1(k1_enumset1(sK2,sK2,X0))) ),
    inference(renaming,[status(thm)],[c_400])).

cnf(c_1511,plain,
    ( r1_tarski(sK2,X0) = iProver_top
    | v1_xboole_0(k1_setfam_1(k1_enumset1(sK2,sK2,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_401])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1523,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2291,plain,
    ( k1_setfam_1(k1_enumset1(sK2,sK2,X0)) = k1_xboole_0
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1511,c_1523])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1522,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3722,plain,
    ( k1_setfam_1(k1_enumset1(sK2,sK2,X0)) = k1_xboole_0
    | sK2 = X0
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2291,c_1522])).

cnf(c_4364,plain,
    ( k6_domain_1(sK2,X0) = sK2
    | k1_setfam_1(k1_enumset1(sK2,sK2,k6_domain_1(sK2,X0))) = k1_xboole_0
    | m1_subset_1(X0,sK2) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2579,c_3722])).

cnf(c_29,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_8239,plain,
    ( m1_subset_1(X0,sK2) != iProver_top
    | k1_setfam_1(k1_enumset1(sK2,sK2,k6_domain_1(sK2,X0))) = k1_xboole_0
    | k6_domain_1(sK2,X0) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4364,c_29])).

cnf(c_8240,plain,
    ( k6_domain_1(sK2,X0) = sK2
    | k1_setfam_1(k1_enumset1(sK2,sK2,k6_domain_1(sK2,X0))) = k1_xboole_0
    | m1_subset_1(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_8239])).

cnf(c_8245,plain,
    ( k6_domain_1(sK2,sK3) = sK2
    | k1_setfam_1(k1_enumset1(sK2,sK2,k6_domain_1(sK2,sK3))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1515,c_8240])).

cnf(c_26,negated_conjecture,
    ( v1_subset_1(k6_domain_1(sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_23,plain,
    ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_36,plain,
    ( u1_struct_0(k2_yellow_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_8,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_72,plain,
    ( r1_tarski(sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_76,plain,
    ( ~ r1_tarski(sK2,sK2)
    | sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_18,plain,
    ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_20,plain,
    ( ~ l1_orders_2(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_22,plain,
    ( l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_340,plain,
    ( l1_struct_0(X0)
    | k2_yellow_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_22])).

cnf(c_341,plain,
    ( l1_struct_0(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_340])).

cnf(c_351,plain,
    ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
    | k2_yellow_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_341])).

cnf(c_352,plain,
    ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0))) ),
    inference(unflattening,[status(thm)],[c_351])).

cnf(c_354,plain,
    ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(sK2)),u1_struct_0(k2_yellow_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_352])).

cnf(c_1019,plain,
    ( ~ v1_subset_1(X0,X1)
    | v1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1628,plain,
    ( v1_subset_1(X0,X1)
    | ~ v1_subset_1(k6_domain_1(sK2,sK3),sK2)
    | X0 != k6_domain_1(sK2,sK3)
    | X1 != sK2 ),
    inference(instantiation,[status(thm)],[c_1019])).

cnf(c_1630,plain,
    ( ~ v1_subset_1(k6_domain_1(sK2,sK3),sK2)
    | v1_subset_1(sK2,sK2)
    | sK2 != k6_domain_1(sK2,sK3)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1628])).

cnf(c_1008,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1759,plain,
    ( X0 != X1
    | X0 = k6_domain_1(sK2,sK3)
    | k6_domain_1(sK2,sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_1008])).

cnf(c_1760,plain,
    ( k6_domain_1(sK2,sK3) != sK2
    | sK2 = k6_domain_1(sK2,sK3)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1759])).

cnf(c_2567,plain,
    ( ~ v1_subset_1(X0,X1)
    | v1_subset_1(k2_struct_0(k2_yellow_1(X2)),u1_struct_0(k2_yellow_1(X2)))
    | u1_struct_0(k2_yellow_1(X2)) != X1
    | k2_struct_0(k2_yellow_1(X2)) != X0 ),
    inference(instantiation,[status(thm)],[c_1019])).

cnf(c_2569,plain,
    ( v1_subset_1(k2_struct_0(k2_yellow_1(sK2)),u1_struct_0(k2_yellow_1(sK2)))
    | ~ v1_subset_1(sK2,sK2)
    | u1_struct_0(k2_yellow_1(sK2)) != sK2
    | k2_struct_0(k2_yellow_1(sK2)) != sK2 ),
    inference(instantiation,[status(thm)],[c_2567])).

cnf(c_17,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_360,plain,
    ( k2_yellow_1(X0) != X1
    | u1_struct_0(X1) = k2_struct_0(X1) ),
    inference(resolution_lifted,[status(thm)],[c_17,c_341])).

cnf(c_361,plain,
    ( u1_struct_0(k2_yellow_1(X0)) = k2_struct_0(k2_yellow_1(X0)) ),
    inference(unflattening,[status(thm)],[c_360])).

cnf(c_3053,plain,
    ( k2_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(superposition,[status(thm)],[c_361,c_23])).

cnf(c_3054,plain,
    ( k2_struct_0(k2_yellow_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_3053])).

cnf(c_8259,plain,
    ( k1_setfam_1(k1_enumset1(sK2,sK2,k6_domain_1(sK2,sK3))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8245,c_26,c_36,c_72,c_76,c_354,c_1630,c_1760,c_2569,c_3054])).

cnf(c_13,plain,
    ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_12,plain,
    ( r1_xboole_0(X0,X1)
    | k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) != X0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_379,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) != X0 ),
    inference(resolution,[status(thm)],[c_12,c_11])).

cnf(c_1512,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) != X0
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_379])).

cnf(c_1661,plain,
    ( k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X1,X1,X0))) != X0
    | r1_tarski(X0,X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_1512])).

cnf(c_8263,plain,
    ( k5_xboole_0(k6_domain_1(sK2,sK3),k1_xboole_0) != k6_domain_1(sK2,sK3)
    | r1_tarski(k6_domain_1(sK2,sK3),sK2) != iProver_top
    | v1_xboole_0(k6_domain_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8259,c_1661])).

cnf(c_30,plain,
    ( m1_subset_1(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1607,plain,
    ( m1_subset_1(k6_domain_1(sK2,sK3),k1_zfmisc_1(sK2))
    | ~ m1_subset_1(sK3,sK2)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1608,plain,
    ( m1_subset_1(k6_domain_1(sK2,sK3),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK3,sK2) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1607])).

cnf(c_10,plain,
    ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1773,plain,
    ( k5_xboole_0(k6_domain_1(sK2,sK3),k1_xboole_0) = k6_domain_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2045,plain,
    ( ~ m1_subset_1(k6_domain_1(sK2,sK3),k1_zfmisc_1(X0))
    | r1_tarski(k6_domain_1(sK2,sK3),X0) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2046,plain,
    ( m1_subset_1(k6_domain_1(sK2,sK3),k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(k6_domain_1(sK2,sK3),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2045])).

cnf(c_2048,plain,
    ( m1_subset_1(k6_domain_1(sK2,sK3),k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(k6_domain_1(sK2,sK3),sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2046])).

cnf(c_8268,plain,
    ( v1_xboole_0(k6_domain_1(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8263,c_29,c_30,c_1608,c_1773,c_2048])).

cnf(c_8276,plain,
    ( k6_domain_1(sK2,sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8268,c_1523])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1517,plain,
    ( k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0)
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2183,plain,
    ( k1_enumset1(sK3,sK3,sK3) = k6_domain_1(sK2,sK3)
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1515,c_1517])).

cnf(c_1615,plain,
    ( ~ m1_subset_1(sK3,sK2)
    | v1_xboole_0(sK2)
    | k1_enumset1(sK3,sK3,sK3) = k6_domain_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_3283,plain,
    ( k1_enumset1(sK3,sK3,sK3) = k6_domain_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2183,c_28,c_27,c_1615])).

cnf(c_9,plain,
    ( k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_14,plain,
    ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1707,plain,
    ( k1_enumset1(X0,X0,X0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9,c_14])).

cnf(c_3287,plain,
    ( k6_domain_1(sK2,sK3) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3283,c_1707])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8276,c_3287])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:42:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.54/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.54/0.98  
% 3.54/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.54/0.98  
% 3.54/0.98  ------  iProver source info
% 3.54/0.98  
% 3.54/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.54/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.54/0.98  git: non_committed_changes: false
% 3.54/0.98  git: last_make_outside_of_git: false
% 3.54/0.98  
% 3.54/0.98  ------ 
% 3.54/0.98  ------ Parsing...
% 3.54/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.54/0.98  
% 3.54/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.54/0.98  ------ Proving...
% 3.54/0.98  ------ Problem Properties 
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  clauses                                 24
% 3.54/0.98  conjectures                             3
% 3.54/0.98  EPR                                     7
% 3.54/0.98  Horn                                    19
% 3.54/0.98  unary                                   11
% 3.54/0.98  binary                                  8
% 3.54/0.98  lits                                    42
% 3.54/0.98  lits eq                                 10
% 3.54/0.98  fd_pure                                 0
% 3.54/0.98  fd_pseudo                               0
% 3.54/0.98  fd_cond                                 1
% 3.54/0.98  fd_pseudo_cond                          1
% 3.54/0.98  AC symbols                              0
% 3.54/0.98  
% 3.54/0.98  ------ Input Options Time Limit: Unbounded
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  ------ 
% 3.54/0.98  Current options:
% 3.54/0.98  ------ 
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  ------ Proving...
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  % SZS status Theorem for theBenchmark.p
% 3.54/0.98  
% 3.54/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.54/0.98  
% 3.54/0.98  fof(f25,conjecture,(
% 3.54/0.98    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f26,negated_conjecture,(
% 3.54/0.98    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 3.54/0.98    inference(negated_conjecture,[],[f25])).
% 3.54/0.98  
% 3.54/0.98  fof(f43,plain,(
% 3.54/0.98    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 3.54/0.98    inference(ennf_transformation,[],[f26])).
% 3.54/0.98  
% 3.54/0.98  fof(f44,plain,(
% 3.54/0.98    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 3.54/0.98    inference(flattening,[],[f43])).
% 3.54/0.98  
% 3.54/0.98  fof(f57,plain,(
% 3.54/0.98    ( ! [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) => (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,sK3),X0) & m1_subset_1(sK3,X0))) )),
% 3.54/0.98    introduced(choice_axiom,[])).
% 3.54/0.98  
% 3.54/0.98  fof(f56,plain,(
% 3.54/0.98    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK2) & v1_subset_1(k6_domain_1(sK2,X1),sK2) & m1_subset_1(X1,sK2)) & ~v1_xboole_0(sK2))),
% 3.54/0.98    introduced(choice_axiom,[])).
% 3.54/0.98  
% 3.54/0.98  fof(f58,plain,(
% 3.54/0.98    (v1_zfmisc_1(sK2) & v1_subset_1(k6_domain_1(sK2,sK3),sK2) & m1_subset_1(sK3,sK2)) & ~v1_xboole_0(sK2)),
% 3.54/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f44,f57,f56])).
% 3.54/0.98  
% 3.54/0.98  fof(f91,plain,(
% 3.54/0.98    m1_subset_1(sK3,sK2)),
% 3.54/0.98    inference(cnf_transformation,[],[f58])).
% 3.54/0.98  
% 3.54/0.98  fof(f19,axiom,(
% 3.54/0.98    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f36,plain,(
% 3.54/0.98    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.54/0.98    inference(ennf_transformation,[],[f19])).
% 3.54/0.98  
% 3.54/0.98  fof(f37,plain,(
% 3.54/0.98    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.54/0.98    inference(flattening,[],[f36])).
% 3.54/0.98  
% 3.54/0.98  fof(f83,plain,(
% 3.54/0.98    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f37])).
% 3.54/0.98  
% 3.54/0.98  fof(f16,axiom,(
% 3.54/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f55,plain,(
% 3.54/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.54/0.98    inference(nnf_transformation,[],[f16])).
% 3.54/0.98  
% 3.54/0.98  fof(f79,plain,(
% 3.54/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.54/0.98    inference(cnf_transformation,[],[f55])).
% 3.54/0.98  
% 3.54/0.98  fof(f24,axiom,(
% 3.54/0.98    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f41,plain,(
% 3.54/0.98    ! [X0] : (! [X1] : (r1_tarski(X0,X1) | v1_xboole_0(k3_xboole_0(X0,X1))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 3.54/0.98    inference(ennf_transformation,[],[f24])).
% 3.54/0.98  
% 3.54/0.98  fof(f42,plain,(
% 3.54/0.98    ! [X0] : (! [X1] : (r1_tarski(X0,X1) | v1_xboole_0(k3_xboole_0(X0,X1))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 3.54/0.98    inference(flattening,[],[f41])).
% 3.54/0.98  
% 3.54/0.98  fof(f89,plain,(
% 3.54/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | v1_xboole_0(k3_xboole_0(X0,X1)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f42])).
% 3.54/0.98  
% 3.54/0.98  fof(f15,axiom,(
% 3.54/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f78,plain,(
% 3.54/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.54/0.98    inference(cnf_transformation,[],[f15])).
% 3.54/0.98  
% 3.54/0.98  fof(f12,axiom,(
% 3.54/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f75,plain,(
% 3.54/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f12])).
% 3.54/0.98  
% 3.54/0.98  fof(f94,plain,(
% 3.54/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 3.54/0.98    inference(definition_unfolding,[],[f78,f75])).
% 3.54/0.98  
% 3.54/0.98  fof(f103,plain,(
% 3.54/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | v1_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X1))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 3.54/0.98    inference(definition_unfolding,[],[f89,f94])).
% 3.54/0.98  
% 3.54/0.98  fof(f93,plain,(
% 3.54/0.98    v1_zfmisc_1(sK2)),
% 3.54/0.98    inference(cnf_transformation,[],[f58])).
% 3.54/0.98  
% 3.54/0.98  fof(f90,plain,(
% 3.54/0.98    ~v1_xboole_0(sK2)),
% 3.54/0.98    inference(cnf_transformation,[],[f58])).
% 3.54/0.98  
% 3.54/0.98  fof(f3,axiom,(
% 3.54/0.98    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f30,plain,(
% 3.54/0.98    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.54/0.98    inference(ennf_transformation,[],[f3])).
% 3.54/0.98  
% 3.54/0.98  fof(f64,plain,(
% 3.54/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f30])).
% 3.54/0.98  
% 3.54/0.98  fof(f4,axiom,(
% 3.54/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f53,plain,(
% 3.54/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.54/0.98    inference(nnf_transformation,[],[f4])).
% 3.54/0.98  
% 3.54/0.98  fof(f54,plain,(
% 3.54/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.54/0.98    inference(flattening,[],[f53])).
% 3.54/0.98  
% 3.54/0.98  fof(f67,plain,(
% 3.54/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f54])).
% 3.54/0.98  
% 3.54/0.98  fof(f92,plain,(
% 3.54/0.98    v1_subset_1(k6_domain_1(sK2,sK3),sK2)),
% 3.54/0.98    inference(cnf_transformation,[],[f58])).
% 3.54/0.98  
% 3.54/0.98  fof(f23,axiom,(
% 3.54/0.98    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f87,plain,(
% 3.54/0.98    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 3.54/0.98    inference(cnf_transformation,[],[f23])).
% 3.54/0.98  
% 3.54/0.98  fof(f65,plain,(
% 3.54/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.54/0.98    inference(cnf_transformation,[],[f54])).
% 3.54/0.98  
% 3.54/0.98  fof(f105,plain,(
% 3.54/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.54/0.98    inference(equality_resolution,[],[f65])).
% 3.54/0.98  
% 3.54/0.98  fof(f18,axiom,(
% 3.54/0.98    ! [X0] : (l1_struct_0(X0) => ~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)))),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f35,plain,(
% 3.54/0.98    ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0))),
% 3.54/0.98    inference(ennf_transformation,[],[f18])).
% 3.54/0.98  
% 3.54/0.98  fof(f82,plain,(
% 3.54/0.98    ( ! [X0] : (~v1_subset_1(k2_struct_0(X0),u1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f35])).
% 3.54/0.98  
% 3.54/0.98  fof(f20,axiom,(
% 3.54/0.98    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f38,plain,(
% 3.54/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 3.54/0.98    inference(ennf_transformation,[],[f20])).
% 3.54/0.98  
% 3.54/0.98  fof(f84,plain,(
% 3.54/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f38])).
% 3.54/0.98  
% 3.54/0.98  fof(f22,axiom,(
% 3.54/0.98    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f28,plain,(
% 3.54/0.98    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 3.54/0.98    inference(pure_predicate_removal,[],[f22])).
% 3.54/0.98  
% 3.54/0.98  fof(f86,plain,(
% 3.54/0.98    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 3.54/0.98    inference(cnf_transformation,[],[f28])).
% 3.54/0.98  
% 3.54/0.98  fof(f17,axiom,(
% 3.54/0.98    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f34,plain,(
% 3.54/0.98    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.54/0.98    inference(ennf_transformation,[],[f17])).
% 3.54/0.98  
% 3.54/0.98  fof(f81,plain,(
% 3.54/0.98    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f34])).
% 3.54/0.98  
% 3.54/0.98  fof(f10,axiom,(
% 3.54/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f73,plain,(
% 3.54/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f10])).
% 3.54/0.98  
% 3.54/0.98  fof(f100,plain,(
% 3.54/0.98    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 3.54/0.98    inference(definition_unfolding,[],[f73,f75,f75])).
% 3.54/0.98  
% 3.54/0.98  fof(f9,axiom,(
% 3.54/0.98    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f27,plain,(
% 3.54/0.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 => r1_xboole_0(X0,X1))),
% 3.54/0.98    inference(unused_predicate_definition_removal,[],[f9])).
% 3.54/0.98  
% 3.54/0.98  fof(f33,plain,(
% 3.54/0.98    ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 3.54/0.98    inference(ennf_transformation,[],[f27])).
% 3.54/0.98  
% 3.54/0.98  fof(f72,plain,(
% 3.54/0.98    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 3.54/0.98    inference(cnf_transformation,[],[f33])).
% 3.54/0.98  
% 3.54/0.98  fof(f5,axiom,(
% 3.54/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f68,plain,(
% 3.54/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.54/0.98    inference(cnf_transformation,[],[f5])).
% 3.54/0.98  
% 3.54/0.98  fof(f95,plain,(
% 3.54/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 3.54/0.98    inference(definition_unfolding,[],[f68,f94])).
% 3.54/0.98  
% 3.54/0.98  fof(f99,plain,(
% 3.54/0.98    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) != X0) )),
% 3.54/0.98    inference(definition_unfolding,[],[f72,f95])).
% 3.54/0.98  
% 3.54/0.98  fof(f8,axiom,(
% 3.54/0.98    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f31,plain,(
% 3.54/0.98    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 3.54/0.98    inference(ennf_transformation,[],[f8])).
% 3.54/0.98  
% 3.54/0.98  fof(f32,plain,(
% 3.54/0.98    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 3.54/0.98    inference(flattening,[],[f31])).
% 3.54/0.98  
% 3.54/0.98  fof(f71,plain,(
% 3.54/0.98    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f32])).
% 3.54/0.98  
% 3.54/0.98  fof(f7,axiom,(
% 3.54/0.98    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f70,plain,(
% 3.54/0.98    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.54/0.98    inference(cnf_transformation,[],[f7])).
% 3.54/0.98  
% 3.54/0.98  fof(f21,axiom,(
% 3.54/0.98    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f39,plain,(
% 3.54/0.98    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.54/0.98    inference(ennf_transformation,[],[f21])).
% 3.54/0.98  
% 3.54/0.98  fof(f40,plain,(
% 3.54/0.98    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.54/0.98    inference(flattening,[],[f39])).
% 3.54/0.98  
% 3.54/0.98  fof(f85,plain,(
% 3.54/0.98    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f40])).
% 3.54/0.98  
% 3.54/0.98  fof(f11,axiom,(
% 3.54/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f74,plain,(
% 3.54/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f11])).
% 3.54/0.98  
% 3.54/0.98  fof(f97,plain,(
% 3.54/0.98    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 3.54/0.98    inference(definition_unfolding,[],[f74,f75])).
% 3.54/0.98  
% 3.54/0.98  fof(f102,plain,(
% 3.54/0.98    ( ! [X0,X1] : (k1_enumset1(X1,X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.54/0.98    inference(definition_unfolding,[],[f85,f97])).
% 3.54/0.98  
% 3.54/0.98  fof(f6,axiom,(
% 3.54/0.98    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f69,plain,(
% 3.54/0.98    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.54/0.98    inference(cnf_transformation,[],[f6])).
% 3.54/0.98  
% 3.54/0.98  fof(f13,axiom,(
% 3.54/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f76,plain,(
% 3.54/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.54/0.98    inference(cnf_transformation,[],[f13])).
% 3.54/0.98  
% 3.54/0.98  fof(f96,plain,(
% 3.54/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 3.54/0.98    inference(definition_unfolding,[],[f76,f75])).
% 3.54/0.98  
% 3.54/0.98  fof(f98,plain,(
% 3.54/0.98    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0) )),
% 3.54/0.98    inference(definition_unfolding,[],[f69,f96])).
% 3.54/0.98  
% 3.54/0.98  fof(f14,axiom,(
% 3.54/0.98    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 3.54/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.54/0.98  
% 3.54/0.98  fof(f77,plain,(
% 3.54/0.98    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 3.54/0.98    inference(cnf_transformation,[],[f14])).
% 3.54/0.98  
% 3.54/0.98  fof(f101,plain,(
% 3.54/0.98    ( ! [X0,X1] : (k1_xboole_0 != k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),X1))) )),
% 3.54/0.98    inference(definition_unfolding,[],[f77,f96,f97])).
% 3.54/0.98  
% 3.54/0.98  cnf(c_27,negated_conjecture,
% 3.54/0.98      ( m1_subset_1(sK3,sK2) ),
% 3.54/0.98      inference(cnf_transformation,[],[f91]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_1515,plain,
% 3.54/0.98      ( m1_subset_1(sK3,sK2) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_19,plain,
% 3.54/0.98      ( ~ m1_subset_1(X0,X1)
% 3.54/0.98      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 3.54/0.98      | v1_xboole_0(X1) ),
% 3.54/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_1518,plain,
% 3.54/0.98      ( m1_subset_1(X0,X1) != iProver_top
% 3.54/0.98      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
% 3.54/0.98      | v1_xboole_0(X1) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_16,plain,
% 3.54/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.54/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_1519,plain,
% 3.54/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.54/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2579,plain,
% 3.54/0.98      ( m1_subset_1(X0,X1) != iProver_top
% 3.54/0.98      | r1_tarski(k6_domain_1(X1,X0),X1) = iProver_top
% 3.54/0.98      | v1_xboole_0(X1) = iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_1518,c_1519]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_24,plain,
% 3.54/0.98      ( r1_tarski(X0,X1)
% 3.54/0.98      | ~ v1_zfmisc_1(X0)
% 3.54/0.98      | v1_xboole_0(X0)
% 3.54/0.98      | v1_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
% 3.54/0.98      inference(cnf_transformation,[],[f103]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_25,negated_conjecture,
% 3.54/0.98      ( v1_zfmisc_1(sK2) ),
% 3.54/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_397,plain,
% 3.54/0.98      ( r1_tarski(X0,X1)
% 3.54/0.98      | v1_xboole_0(X0)
% 3.54/0.98      | v1_xboole_0(k1_setfam_1(k1_enumset1(X0,X0,X1)))
% 3.54/0.98      | sK2 != X0 ),
% 3.54/0.98      inference(resolution_lifted,[status(thm)],[c_24,c_25]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_398,plain,
% 3.54/0.98      ( r1_tarski(sK2,X0)
% 3.54/0.98      | v1_xboole_0(k1_setfam_1(k1_enumset1(sK2,sK2,X0)))
% 3.54/0.98      | v1_xboole_0(sK2) ),
% 3.54/0.98      inference(unflattening,[status(thm)],[c_397]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_28,negated_conjecture,
% 3.54/0.98      ( ~ v1_xboole_0(sK2) ),
% 3.54/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_400,plain,
% 3.54/0.98      ( v1_xboole_0(k1_setfam_1(k1_enumset1(sK2,sK2,X0)))
% 3.54/0.98      | r1_tarski(sK2,X0) ),
% 3.54/0.98      inference(global_propositional_subsumption,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_398,c_28]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_401,plain,
% 3.54/0.98      ( r1_tarski(sK2,X0)
% 3.54/0.98      | v1_xboole_0(k1_setfam_1(k1_enumset1(sK2,sK2,X0))) ),
% 3.54/0.98      inference(renaming,[status(thm)],[c_400]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_1511,plain,
% 3.54/0.98      ( r1_tarski(sK2,X0) = iProver_top
% 3.54/0.98      | v1_xboole_0(k1_setfam_1(k1_enumset1(sK2,sK2,X0))) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_401]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_5,plain,
% 3.54/0.98      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.54/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_1523,plain,
% 3.54/0.98      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2291,plain,
% 3.54/0.98      ( k1_setfam_1(k1_enumset1(sK2,sK2,X0)) = k1_xboole_0
% 3.54/0.98      | r1_tarski(sK2,X0) = iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_1511,c_1523]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_6,plain,
% 3.54/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.54/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_1522,plain,
% 3.54/0.98      ( X0 = X1
% 3.54/0.98      | r1_tarski(X1,X0) != iProver_top
% 3.54/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3722,plain,
% 3.54/0.98      ( k1_setfam_1(k1_enumset1(sK2,sK2,X0)) = k1_xboole_0
% 3.54/0.98      | sK2 = X0
% 3.54/0.98      | r1_tarski(X0,sK2) != iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_2291,c_1522]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_4364,plain,
% 3.54/0.98      ( k6_domain_1(sK2,X0) = sK2
% 3.54/0.98      | k1_setfam_1(k1_enumset1(sK2,sK2,k6_domain_1(sK2,X0))) = k1_xboole_0
% 3.54/0.98      | m1_subset_1(X0,sK2) != iProver_top
% 3.54/0.98      | v1_xboole_0(sK2) = iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_2579,c_3722]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_29,plain,
% 3.54/0.98      ( v1_xboole_0(sK2) != iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_8239,plain,
% 3.54/0.98      ( m1_subset_1(X0,sK2) != iProver_top
% 3.54/0.98      | k1_setfam_1(k1_enumset1(sK2,sK2,k6_domain_1(sK2,X0))) = k1_xboole_0
% 3.54/0.98      | k6_domain_1(sK2,X0) = sK2 ),
% 3.54/0.98      inference(global_propositional_subsumption,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_4364,c_29]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_8240,plain,
% 3.54/0.98      ( k6_domain_1(sK2,X0) = sK2
% 3.54/0.98      | k1_setfam_1(k1_enumset1(sK2,sK2,k6_domain_1(sK2,X0))) = k1_xboole_0
% 3.54/0.98      | m1_subset_1(X0,sK2) != iProver_top ),
% 3.54/0.98      inference(renaming,[status(thm)],[c_8239]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_8245,plain,
% 3.54/0.98      ( k6_domain_1(sK2,sK3) = sK2
% 3.54/0.98      | k1_setfam_1(k1_enumset1(sK2,sK2,k6_domain_1(sK2,sK3))) = k1_xboole_0 ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_1515,c_8240]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_26,negated_conjecture,
% 3.54/0.98      ( v1_subset_1(k6_domain_1(sK2,sK3),sK2) ),
% 3.54/0.98      inference(cnf_transformation,[],[f92]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_23,plain,
% 3.54/0.98      ( u1_struct_0(k2_yellow_1(X0)) = X0 ),
% 3.54/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_36,plain,
% 3.54/0.98      ( u1_struct_0(k2_yellow_1(sK2)) = sK2 ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_23]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_8,plain,
% 3.54/0.98      ( r1_tarski(X0,X0) ),
% 3.54/0.98      inference(cnf_transformation,[],[f105]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_72,plain,
% 3.54/0.98      ( r1_tarski(sK2,sK2) ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_76,plain,
% 3.54/0.98      ( ~ r1_tarski(sK2,sK2) | sK2 = sK2 ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_18,plain,
% 3.54/0.98      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
% 3.54/0.98      | ~ l1_struct_0(X0) ),
% 3.54/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_20,plain,
% 3.54/0.98      ( ~ l1_orders_2(X0) | l1_struct_0(X0) ),
% 3.54/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_22,plain,
% 3.54/0.98      ( l1_orders_2(k2_yellow_1(X0)) ),
% 3.54/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_340,plain,
% 3.54/0.98      ( l1_struct_0(X0) | k2_yellow_1(X1) != X0 ),
% 3.54/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_22]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_341,plain,
% 3.54/0.98      ( l1_struct_0(k2_yellow_1(X0)) ),
% 3.54/0.98      inference(unflattening,[status(thm)],[c_340]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_351,plain,
% 3.54/0.98      ( ~ v1_subset_1(k2_struct_0(X0),u1_struct_0(X0))
% 3.54/0.98      | k2_yellow_1(X1) != X0 ),
% 3.54/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_341]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_352,plain,
% 3.54/0.98      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(X0)),u1_struct_0(k2_yellow_1(X0))) ),
% 3.54/0.98      inference(unflattening,[status(thm)],[c_351]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_354,plain,
% 3.54/0.98      ( ~ v1_subset_1(k2_struct_0(k2_yellow_1(sK2)),u1_struct_0(k2_yellow_1(sK2))) ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_352]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_1019,plain,
% 3.54/0.98      ( ~ v1_subset_1(X0,X1) | v1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.54/0.98      theory(equality) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_1628,plain,
% 3.54/0.98      ( v1_subset_1(X0,X1)
% 3.54/0.98      | ~ v1_subset_1(k6_domain_1(sK2,sK3),sK2)
% 3.54/0.98      | X0 != k6_domain_1(sK2,sK3)
% 3.54/0.98      | X1 != sK2 ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_1019]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_1630,plain,
% 3.54/0.98      ( ~ v1_subset_1(k6_domain_1(sK2,sK3),sK2)
% 3.54/0.98      | v1_subset_1(sK2,sK2)
% 3.54/0.98      | sK2 != k6_domain_1(sK2,sK3)
% 3.54/0.98      | sK2 != sK2 ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_1628]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_1008,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_1759,plain,
% 3.54/0.98      ( X0 != X1
% 3.54/0.98      | X0 = k6_domain_1(sK2,sK3)
% 3.54/0.98      | k6_domain_1(sK2,sK3) != X1 ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_1008]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_1760,plain,
% 3.54/0.98      ( k6_domain_1(sK2,sK3) != sK2
% 3.54/0.98      | sK2 = k6_domain_1(sK2,sK3)
% 3.54/0.98      | sK2 != sK2 ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_1759]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2567,plain,
% 3.54/0.98      ( ~ v1_subset_1(X0,X1)
% 3.54/0.98      | v1_subset_1(k2_struct_0(k2_yellow_1(X2)),u1_struct_0(k2_yellow_1(X2)))
% 3.54/0.98      | u1_struct_0(k2_yellow_1(X2)) != X1
% 3.54/0.98      | k2_struct_0(k2_yellow_1(X2)) != X0 ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_1019]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2569,plain,
% 3.54/0.98      ( v1_subset_1(k2_struct_0(k2_yellow_1(sK2)),u1_struct_0(k2_yellow_1(sK2)))
% 3.54/0.98      | ~ v1_subset_1(sK2,sK2)
% 3.54/0.98      | u1_struct_0(k2_yellow_1(sK2)) != sK2
% 3.54/0.98      | k2_struct_0(k2_yellow_1(sK2)) != sK2 ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_2567]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_17,plain,
% 3.54/0.98      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.54/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_360,plain,
% 3.54/0.98      ( k2_yellow_1(X0) != X1 | u1_struct_0(X1) = k2_struct_0(X1) ),
% 3.54/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_341]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_361,plain,
% 3.54/0.98      ( u1_struct_0(k2_yellow_1(X0)) = k2_struct_0(k2_yellow_1(X0)) ),
% 3.54/0.98      inference(unflattening,[status(thm)],[c_360]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3053,plain,
% 3.54/0.98      ( k2_struct_0(k2_yellow_1(X0)) = X0 ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_361,c_23]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3054,plain,
% 3.54/0.98      ( k2_struct_0(k2_yellow_1(sK2)) = sK2 ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_3053]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_8259,plain,
% 3.54/0.98      ( k1_setfam_1(k1_enumset1(sK2,sK2,k6_domain_1(sK2,sK3))) = k1_xboole_0 ),
% 3.54/0.98      inference(global_propositional_subsumption,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_8245,c_26,c_36,c_72,c_76,c_354,c_1630,c_1760,c_2569,
% 3.54/0.98                 c_3054]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_13,plain,
% 3.54/0.98      ( k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
% 3.54/0.98      inference(cnf_transformation,[],[f100]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_12,plain,
% 3.54/0.98      ( r1_xboole_0(X0,X1)
% 3.54/0.98      | k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) != X0 ),
% 3.54/0.98      inference(cnf_transformation,[],[f99]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_11,plain,
% 3.54/0.98      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 3.54/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_379,plain,
% 3.54/0.98      ( ~ r1_tarski(X0,X1)
% 3.54/0.98      | v1_xboole_0(X0)
% 3.54/0.98      | k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) != X0 ),
% 3.54/0.98      inference(resolution,[status(thm)],[c_12,c_11]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_1512,plain,
% 3.54/0.98      ( k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) != X0
% 3.54/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.54/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_379]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_1661,plain,
% 3.54/0.98      ( k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X1,X1,X0))) != X0
% 3.54/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.54/0.98      | v1_xboole_0(X0) = iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_13,c_1512]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_8263,plain,
% 3.54/0.98      ( k5_xboole_0(k6_domain_1(sK2,sK3),k1_xboole_0) != k6_domain_1(sK2,sK3)
% 3.54/0.98      | r1_tarski(k6_domain_1(sK2,sK3),sK2) != iProver_top
% 3.54/0.98      | v1_xboole_0(k6_domain_1(sK2,sK3)) = iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_8259,c_1661]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_30,plain,
% 3.54/0.98      ( m1_subset_1(sK3,sK2) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_1607,plain,
% 3.54/0.98      ( m1_subset_1(k6_domain_1(sK2,sK3),k1_zfmisc_1(sK2))
% 3.54/0.98      | ~ m1_subset_1(sK3,sK2)
% 3.54/0.98      | v1_xboole_0(sK2) ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_19]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_1608,plain,
% 3.54/0.98      ( m1_subset_1(k6_domain_1(sK2,sK3),k1_zfmisc_1(sK2)) = iProver_top
% 3.54/0.98      | m1_subset_1(sK3,sK2) != iProver_top
% 3.54/0.98      | v1_xboole_0(sK2) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_1607]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_10,plain,
% 3.54/0.98      ( k5_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.54/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_1773,plain,
% 3.54/0.98      ( k5_xboole_0(k6_domain_1(sK2,sK3),k1_xboole_0) = k6_domain_1(sK2,sK3) ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_10]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2045,plain,
% 3.54/0.98      ( ~ m1_subset_1(k6_domain_1(sK2,sK3),k1_zfmisc_1(X0))
% 3.54/0.98      | r1_tarski(k6_domain_1(sK2,sK3),X0) ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_16]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2046,plain,
% 3.54/0.98      ( m1_subset_1(k6_domain_1(sK2,sK3),k1_zfmisc_1(X0)) != iProver_top
% 3.54/0.98      | r1_tarski(k6_domain_1(sK2,sK3),X0) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_2045]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2048,plain,
% 3.54/0.98      ( m1_subset_1(k6_domain_1(sK2,sK3),k1_zfmisc_1(sK2)) != iProver_top
% 3.54/0.98      | r1_tarski(k6_domain_1(sK2,sK3),sK2) = iProver_top ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_2046]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_8268,plain,
% 3.54/0.98      ( v1_xboole_0(k6_domain_1(sK2,sK3)) = iProver_top ),
% 3.54/0.98      inference(global_propositional_subsumption,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_8263,c_29,c_30,c_1608,c_1773,c_2048]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_8276,plain,
% 3.54/0.98      ( k6_domain_1(sK2,sK3) = k1_xboole_0 ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_8268,c_1523]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_21,plain,
% 3.54/0.98      ( ~ m1_subset_1(X0,X1)
% 3.54/0.98      | v1_xboole_0(X1)
% 3.54/0.98      | k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0) ),
% 3.54/0.98      inference(cnf_transformation,[],[f102]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_1517,plain,
% 3.54/0.98      ( k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0)
% 3.54/0.98      | m1_subset_1(X0,X1) != iProver_top
% 3.54/0.98      | v1_xboole_0(X1) = iProver_top ),
% 3.54/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_2183,plain,
% 3.54/0.98      ( k1_enumset1(sK3,sK3,sK3) = k6_domain_1(sK2,sK3)
% 3.54/0.98      | v1_xboole_0(sK2) = iProver_top ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_1515,c_1517]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_1615,plain,
% 3.54/0.98      ( ~ m1_subset_1(sK3,sK2)
% 3.54/0.98      | v1_xboole_0(sK2)
% 3.54/0.98      | k1_enumset1(sK3,sK3,sK3) = k6_domain_1(sK2,sK3) ),
% 3.54/0.98      inference(instantiation,[status(thm)],[c_21]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3283,plain,
% 3.54/0.98      ( k1_enumset1(sK3,sK3,sK3) = k6_domain_1(sK2,sK3) ),
% 3.54/0.98      inference(global_propositional_subsumption,
% 3.54/0.98                [status(thm)],
% 3.54/0.98                [c_2183,c_28,c_27,c_1615]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_9,plain,
% 3.54/0.98      ( k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
% 3.54/0.98      inference(cnf_transformation,[],[f98]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_14,plain,
% 3.54/0.98      ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),X1)) != k1_xboole_0 ),
% 3.54/0.98      inference(cnf_transformation,[],[f101]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_1707,plain,
% 3.54/0.98      ( k1_enumset1(X0,X0,X0) != k1_xboole_0 ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_9,c_14]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(c_3287,plain,
% 3.54/0.98      ( k6_domain_1(sK2,sK3) != k1_xboole_0 ),
% 3.54/0.98      inference(superposition,[status(thm)],[c_3283,c_1707]) ).
% 3.54/0.98  
% 3.54/0.98  cnf(contradiction,plain,
% 3.54/0.98      ( $false ),
% 3.54/0.98      inference(minisat,[status(thm)],[c_8276,c_3287]) ).
% 3.54/0.98  
% 3.54/0.98  
% 3.54/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.54/0.98  
% 3.54/0.98  ------                               Statistics
% 3.54/0.98  
% 3.54/0.98  ------ Selected
% 3.54/0.98  
% 3.54/0.98  total_time:                             0.303
% 3.54/0.98  
%------------------------------------------------------------------------------
