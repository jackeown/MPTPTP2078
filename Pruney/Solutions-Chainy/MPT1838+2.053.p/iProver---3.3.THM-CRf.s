%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:24:40 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 226 expanded)
%              Number of clauses        :   43 (  61 expanded)
%              Number of leaves         :   15 (  58 expanded)
%              Depth                    :   18
%              Number of atoms          :  263 ( 881 expanded)
%              Number of equality atoms :  127 ( 293 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
     => ( sK2 != X0
        & r1_tarski(X0,sK2)
        & v1_zfmisc_1(sK2)
        & ~ v1_xboole_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r1_tarski(X0,X1)
            & v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( sK1 != X1
          & r1_tarski(sK1,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( sK1 != sK2
    & r1_tarski(sK1,sK2)
    & v1_zfmisc_1(sK2)
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f23,f31,f30])).

fof(f59,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_tarski(X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f51])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f52,f37])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X1] :
              ( k6_domain_1(X0,X1) = X0
              & m1_subset_1(X1,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f27,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X2] :
              ( k6_domain_1(X0,X2) = X0
              & m1_subset_1(X2,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK0(X0)) = X0
        & m1_subset_1(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK0(X0)) = X0
            & m1_subset_1(sK0(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f53,plain,(
    ! [X0] :
      ( m1_subset_1(sK0(X0),X0)
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f58,plain,(
    v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f57,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f54,plain,(
    ! [X0] :
      ( k6_domain_1(X0,sK0(X0)) = X0
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k2_xboole_0(X1,X2) = k1_tarski(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = X2
        & k1_tarski(X0) = X1 )
      | ( k1_tarski(X0) = X2
        & k1_xboole_0 = X1 )
      | ( k1_tarski(X0) = X2
        & k1_tarski(X0) = X1 )
      | k2_xboole_0(X1,X2) != k1_tarski(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = X1
      | k1_xboole_0 = X1
      | k1_tarski(X0) = X1
      | k2_xboole_0(X1,X2) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X0) = X1
      | k1_xboole_0 = X1
      | k2_tarski(X0,X0) = X1
      | k2_tarski(X0,X0) != k3_tarski(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f43,f37,f37,f51,f37])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f24])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f72,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f15])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f56,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_544,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_tarski(k2_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_546,plain,
    ( k3_tarski(k2_tarski(X0,X1)) = X1
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3494,plain,
    ( k3_tarski(k2_tarski(sK1,sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_544,c_546])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_20,plain,
    ( m1_subset_1(sK0(X0),X0)
    | ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_197,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X0)
    | X0 != X1
    | k6_domain_1(X1,X2) = k2_tarski(X2,X2)
    | sK0(X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_20])).

cnf(c_198,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | k6_domain_1(X0,sK0(X0)) = k2_tarski(sK0(X0),sK0(X0)) ),
    inference(unflattening,[status(thm)],[c_197])).

cnf(c_23,negated_conjecture,
    ( v1_zfmisc_1(sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_216,plain,
    ( v1_xboole_0(X0)
    | k2_tarski(sK0(X0),sK0(X0)) = k6_domain_1(X0,sK0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_198,c_23])).

cnf(c_217,plain,
    ( v1_xboole_0(sK2)
    | k2_tarski(sK0(sK2),sK0(sK2)) = k6_domain_1(sK2,sK0(sK2)) ),
    inference(unflattening,[status(thm)],[c_216])).

cnf(c_24,negated_conjecture,
    ( ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_219,plain,
    ( k2_tarski(sK0(sK2),sK0(sK2)) = k6_domain_1(sK2,sK0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_217,c_24])).

cnf(c_19,plain,
    ( ~ v1_zfmisc_1(X0)
    | v1_xboole_0(X0)
    | k6_domain_1(X0,sK0(X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_224,plain,
    ( v1_xboole_0(X0)
    | k6_domain_1(X0,sK0(X0)) = X0
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_23])).

cnf(c_225,plain,
    ( v1_xboole_0(sK2)
    | k6_domain_1(sK2,sK0(sK2)) = sK2 ),
    inference(unflattening,[status(thm)],[c_224])).

cnf(c_227,plain,
    ( k6_domain_1(sK2,sK0(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_225,c_24])).

cnf(c_563,plain,
    ( k2_tarski(sK0(sK2),sK0(sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_219,c_227])).

cnf(c_16,plain,
    ( k2_tarski(X0,X0) = X1
    | k3_tarski(k2_tarski(X1,X2)) != k2_tarski(X0,X0)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2664,plain,
    ( k2_tarski(sK0(sK2),sK0(sK2)) = X0
    | k3_tarski(k2_tarski(X0,X1)) != sK2
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_563,c_16])).

cnf(c_2668,plain,
    ( k3_tarski(k2_tarski(X0,X1)) != sK2
    | sK2 = X0
    | k1_xboole_0 = X0 ),
    inference(demodulation,[status(thm)],[c_2664,c_563])).

cnf(c_3692,plain,
    ( sK2 = sK1
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3494,c_2668])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_48,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_49,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_57,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_3,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_180,plain,
    ( ~ r1_tarski(X0,X1)
    | v1_xboole_0(X0)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_3])).

cnf(c_181,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_180])).

cnf(c_25,negated_conjecture,
    ( ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_241,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_181,c_25])).

cnf(c_242,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_241])).

cnf(c_377,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_678,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k1_xboole_0)
    | sK1 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_377])).

cnf(c_680,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK1 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_678])).

cnf(c_3708,plain,
    ( sK2 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3692,c_48,c_49,c_57,c_242,c_680])).

cnf(c_21,negated_conjecture,
    ( sK1 != sK2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_3725,plain,
    ( sK1 != sK1 ),
    inference(demodulation,[status(thm)],[c_3708,c_21])).

cnf(c_3726,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_3725])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:20:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 1.81/1.05  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.05  
% 1.81/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.81/1.05  
% 1.81/1.05  ------  iProver source info
% 1.81/1.05  
% 1.81/1.05  git: date: 2020-06-30 10:37:57 +0100
% 1.81/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.81/1.05  git: non_committed_changes: false
% 1.81/1.05  git: last_make_outside_of_git: false
% 1.81/1.05  
% 1.81/1.05  ------ 
% 1.81/1.05  
% 1.81/1.05  ------ Input Options
% 1.81/1.05  
% 1.81/1.05  --out_options                           all
% 1.81/1.05  --tptp_safe_out                         true
% 1.81/1.05  --problem_path                          ""
% 1.81/1.05  --include_path                          ""
% 1.81/1.05  --clausifier                            res/vclausify_rel
% 1.81/1.05  --clausifier_options                    --mode clausify
% 1.81/1.05  --stdin                                 false
% 1.81/1.05  --stats_out                             all
% 1.81/1.05  
% 1.81/1.05  ------ General Options
% 1.81/1.05  
% 1.81/1.05  --fof                                   false
% 1.81/1.05  --time_out_real                         305.
% 1.81/1.05  --time_out_virtual                      -1.
% 1.81/1.05  --symbol_type_check                     false
% 1.81/1.05  --clausify_out                          false
% 1.81/1.05  --sig_cnt_out                           false
% 1.81/1.05  --trig_cnt_out                          false
% 1.81/1.05  --trig_cnt_out_tolerance                1.
% 1.81/1.05  --trig_cnt_out_sk_spl                   false
% 1.81/1.05  --abstr_cl_out                          false
% 1.81/1.05  
% 1.81/1.05  ------ Global Options
% 1.81/1.05  
% 1.81/1.05  --schedule                              default
% 1.81/1.05  --add_important_lit                     false
% 1.81/1.05  --prop_solver_per_cl                    1000
% 1.81/1.05  --min_unsat_core                        false
% 1.81/1.05  --soft_assumptions                      false
% 1.81/1.05  --soft_lemma_size                       3
% 1.81/1.05  --prop_impl_unit_size                   0
% 1.81/1.05  --prop_impl_unit                        []
% 1.81/1.05  --share_sel_clauses                     true
% 1.81/1.05  --reset_solvers                         false
% 1.81/1.05  --bc_imp_inh                            [conj_cone]
% 1.81/1.05  --conj_cone_tolerance                   3.
% 1.81/1.05  --extra_neg_conj                        none
% 1.81/1.05  --large_theory_mode                     true
% 1.81/1.05  --prolific_symb_bound                   200
% 1.81/1.05  --lt_threshold                          2000
% 1.81/1.05  --clause_weak_htbl                      true
% 1.81/1.05  --gc_record_bc_elim                     false
% 1.81/1.05  
% 1.81/1.05  ------ Preprocessing Options
% 1.81/1.05  
% 1.81/1.05  --preprocessing_flag                    true
% 1.81/1.05  --time_out_prep_mult                    0.1
% 1.81/1.05  --splitting_mode                        input
% 1.81/1.05  --splitting_grd                         true
% 1.81/1.05  --splitting_cvd                         false
% 1.81/1.05  --splitting_cvd_svl                     false
% 1.81/1.05  --splitting_nvd                         32
% 1.81/1.05  --sub_typing                            true
% 1.81/1.05  --prep_gs_sim                           true
% 1.81/1.05  --prep_unflatten                        true
% 1.81/1.05  --prep_res_sim                          true
% 1.81/1.05  --prep_upred                            true
% 1.81/1.05  --prep_sem_filter                       exhaustive
% 1.81/1.05  --prep_sem_filter_out                   false
% 1.81/1.05  --pred_elim                             true
% 1.81/1.05  --res_sim_input                         true
% 1.81/1.05  --eq_ax_congr_red                       true
% 1.81/1.05  --pure_diseq_elim                       true
% 1.81/1.05  --brand_transform                       false
% 1.81/1.05  --non_eq_to_eq                          false
% 1.81/1.05  --prep_def_merge                        true
% 1.81/1.05  --prep_def_merge_prop_impl              false
% 1.81/1.05  --prep_def_merge_mbd                    true
% 1.81/1.05  --prep_def_merge_tr_red                 false
% 1.81/1.05  --prep_def_merge_tr_cl                  false
% 1.81/1.05  --smt_preprocessing                     true
% 1.81/1.05  --smt_ac_axioms                         fast
% 1.81/1.05  --preprocessed_out                      false
% 1.81/1.05  --preprocessed_stats                    false
% 1.81/1.05  
% 1.81/1.05  ------ Abstraction refinement Options
% 1.81/1.05  
% 1.81/1.05  --abstr_ref                             []
% 1.81/1.05  --abstr_ref_prep                        false
% 1.81/1.05  --abstr_ref_until_sat                   false
% 1.81/1.05  --abstr_ref_sig_restrict                funpre
% 1.81/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 1.81/1.05  --abstr_ref_under                       []
% 1.81/1.05  
% 1.81/1.05  ------ SAT Options
% 1.81/1.05  
% 1.81/1.05  --sat_mode                              false
% 1.81/1.05  --sat_fm_restart_options                ""
% 1.81/1.05  --sat_gr_def                            false
% 1.81/1.05  --sat_epr_types                         true
% 1.81/1.05  --sat_non_cyclic_types                  false
% 1.81/1.05  --sat_finite_models                     false
% 1.81/1.05  --sat_fm_lemmas                         false
% 1.81/1.05  --sat_fm_prep                           false
% 1.81/1.05  --sat_fm_uc_incr                        true
% 1.81/1.05  --sat_out_model                         small
% 1.81/1.05  --sat_out_clauses                       false
% 1.81/1.05  
% 1.81/1.05  ------ QBF Options
% 1.81/1.05  
% 1.81/1.05  --qbf_mode                              false
% 1.81/1.05  --qbf_elim_univ                         false
% 1.81/1.05  --qbf_dom_inst                          none
% 1.81/1.05  --qbf_dom_pre_inst                      false
% 1.81/1.05  --qbf_sk_in                             false
% 1.81/1.05  --qbf_pred_elim                         true
% 1.81/1.05  --qbf_split                             512
% 1.81/1.05  
% 1.81/1.05  ------ BMC1 Options
% 1.81/1.05  
% 1.81/1.05  --bmc1_incremental                      false
% 1.81/1.05  --bmc1_axioms                           reachable_all
% 1.81/1.05  --bmc1_min_bound                        0
% 1.81/1.05  --bmc1_max_bound                        -1
% 1.81/1.05  --bmc1_max_bound_default                -1
% 1.81/1.05  --bmc1_symbol_reachability              true
% 1.81/1.05  --bmc1_property_lemmas                  false
% 1.81/1.05  --bmc1_k_induction                      false
% 1.81/1.05  --bmc1_non_equiv_states                 false
% 1.81/1.05  --bmc1_deadlock                         false
% 1.81/1.05  --bmc1_ucm                              false
% 1.81/1.05  --bmc1_add_unsat_core                   none
% 1.81/1.05  --bmc1_unsat_core_children              false
% 1.81/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 1.81/1.05  --bmc1_out_stat                         full
% 1.81/1.05  --bmc1_ground_init                      false
% 1.81/1.05  --bmc1_pre_inst_next_state              false
% 1.81/1.05  --bmc1_pre_inst_state                   false
% 1.81/1.05  --bmc1_pre_inst_reach_state             false
% 1.81/1.05  --bmc1_out_unsat_core                   false
% 1.81/1.05  --bmc1_aig_witness_out                  false
% 1.81/1.05  --bmc1_verbose                          false
% 1.81/1.05  --bmc1_dump_clauses_tptp                false
% 1.81/1.05  --bmc1_dump_unsat_core_tptp             false
% 1.81/1.05  --bmc1_dump_file                        -
% 1.81/1.05  --bmc1_ucm_expand_uc_limit              128
% 1.81/1.05  --bmc1_ucm_n_expand_iterations          6
% 1.81/1.05  --bmc1_ucm_extend_mode                  1
% 1.81/1.05  --bmc1_ucm_init_mode                    2
% 1.81/1.05  --bmc1_ucm_cone_mode                    none
% 1.81/1.05  --bmc1_ucm_reduced_relation_type        0
% 1.81/1.05  --bmc1_ucm_relax_model                  4
% 1.81/1.05  --bmc1_ucm_full_tr_after_sat            true
% 1.81/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 1.81/1.05  --bmc1_ucm_layered_model                none
% 1.81/1.05  --bmc1_ucm_max_lemma_size               10
% 1.81/1.05  
% 1.81/1.05  ------ AIG Options
% 1.81/1.05  
% 1.81/1.05  --aig_mode                              false
% 1.81/1.05  
% 1.81/1.05  ------ Instantiation Options
% 1.81/1.05  
% 1.81/1.05  --instantiation_flag                    true
% 1.81/1.05  --inst_sos_flag                         false
% 1.81/1.05  --inst_sos_phase                        true
% 1.81/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.81/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.81/1.05  --inst_lit_sel_side                     num_symb
% 1.81/1.05  --inst_solver_per_active                1400
% 1.81/1.05  --inst_solver_calls_frac                1.
% 1.81/1.05  --inst_passive_queue_type               priority_queues
% 1.81/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.81/1.05  --inst_passive_queues_freq              [25;2]
% 1.81/1.05  --inst_dismatching                      true
% 1.81/1.05  --inst_eager_unprocessed_to_passive     true
% 1.81/1.05  --inst_prop_sim_given                   true
% 1.81/1.05  --inst_prop_sim_new                     false
% 1.81/1.05  --inst_subs_new                         false
% 1.81/1.05  --inst_eq_res_simp                      false
% 1.81/1.05  --inst_subs_given                       false
% 1.81/1.05  --inst_orphan_elimination               true
% 1.81/1.05  --inst_learning_loop_flag               true
% 1.81/1.05  --inst_learning_start                   3000
% 1.81/1.05  --inst_learning_factor                  2
% 1.81/1.05  --inst_start_prop_sim_after_learn       3
% 1.81/1.05  --inst_sel_renew                        solver
% 1.81/1.05  --inst_lit_activity_flag                true
% 1.81/1.05  --inst_restr_to_given                   false
% 1.81/1.05  --inst_activity_threshold               500
% 1.81/1.05  --inst_out_proof                        true
% 1.81/1.05  
% 1.81/1.05  ------ Resolution Options
% 1.81/1.05  
% 1.81/1.05  --resolution_flag                       true
% 1.81/1.05  --res_lit_sel                           adaptive
% 1.81/1.05  --res_lit_sel_side                      none
% 1.81/1.05  --res_ordering                          kbo
% 1.81/1.05  --res_to_prop_solver                    active
% 1.81/1.05  --res_prop_simpl_new                    false
% 1.81/1.05  --res_prop_simpl_given                  true
% 1.81/1.05  --res_passive_queue_type                priority_queues
% 1.81/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.81/1.05  --res_passive_queues_freq               [15;5]
% 1.81/1.05  --res_forward_subs                      full
% 1.81/1.05  --res_backward_subs                     full
% 1.81/1.05  --res_forward_subs_resolution           true
% 1.81/1.05  --res_backward_subs_resolution          true
% 1.81/1.05  --res_orphan_elimination                true
% 1.81/1.05  --res_time_limit                        2.
% 1.81/1.05  --res_out_proof                         true
% 1.81/1.05  
% 1.81/1.05  ------ Superposition Options
% 1.81/1.05  
% 1.81/1.05  --superposition_flag                    true
% 1.81/1.05  --sup_passive_queue_type                priority_queues
% 1.81/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.81/1.05  --sup_passive_queues_freq               [8;1;4]
% 1.81/1.05  --demod_completeness_check              fast
% 1.81/1.05  --demod_use_ground                      true
% 1.81/1.05  --sup_to_prop_solver                    passive
% 1.81/1.05  --sup_prop_simpl_new                    true
% 1.81/1.05  --sup_prop_simpl_given                  true
% 1.81/1.05  --sup_fun_splitting                     false
% 1.81/1.05  --sup_smt_interval                      50000
% 1.81/1.05  
% 1.81/1.05  ------ Superposition Simplification Setup
% 1.81/1.05  
% 1.81/1.05  --sup_indices_passive                   []
% 1.81/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 1.81/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/1.05  --sup_full_bw                           [BwDemod]
% 1.81/1.05  --sup_immed_triv                        [TrivRules]
% 1.81/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.81/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/1.05  --sup_immed_bw_main                     []
% 1.81/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.81/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 1.81/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.81/1.05  
% 1.81/1.05  ------ Combination Options
% 1.81/1.05  
% 1.81/1.05  --comb_res_mult                         3
% 1.81/1.05  --comb_sup_mult                         2
% 1.81/1.05  --comb_inst_mult                        10
% 1.81/1.05  
% 1.81/1.05  ------ Debug Options
% 1.81/1.05  
% 1.81/1.05  --dbg_backtrace                         false
% 1.81/1.05  --dbg_dump_prop_clauses                 false
% 1.81/1.05  --dbg_dump_prop_clauses_file            -
% 1.81/1.05  --dbg_out_stat                          false
% 1.81/1.05  ------ Parsing...
% 1.81/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.81/1.05  
% 1.81/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.81/1.05  
% 1.81/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.81/1.05  
% 1.81/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.81/1.05  ------ Proving...
% 1.81/1.05  ------ Problem Properties 
% 1.81/1.05  
% 1.81/1.05  
% 1.81/1.05  clauses                                 18
% 1.81/1.05  conjectures                             2
% 1.81/1.05  EPR                                     5
% 1.81/1.05  Horn                                    14
% 1.81/1.05  unary                                   9
% 1.81/1.05  binary                                  5
% 1.81/1.05  lits                                    31
% 1.81/1.05  lits eq                                 18
% 1.81/1.05  fd_pure                                 0
% 1.81/1.05  fd_pseudo                               0
% 1.81/1.05  fd_cond                                 1
% 1.81/1.05  fd_pseudo_cond                          3
% 1.81/1.05  AC symbols                              0
% 1.81/1.05  
% 1.81/1.05  ------ Schedule dynamic 5 is on 
% 1.81/1.05  
% 1.81/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.81/1.05  
% 1.81/1.05  
% 1.81/1.05  ------ 
% 1.81/1.05  Current options:
% 1.81/1.05  ------ 
% 1.81/1.05  
% 1.81/1.05  ------ Input Options
% 1.81/1.05  
% 1.81/1.05  --out_options                           all
% 1.81/1.05  --tptp_safe_out                         true
% 1.81/1.05  --problem_path                          ""
% 1.81/1.05  --include_path                          ""
% 1.81/1.05  --clausifier                            res/vclausify_rel
% 1.81/1.05  --clausifier_options                    --mode clausify
% 1.81/1.05  --stdin                                 false
% 1.81/1.05  --stats_out                             all
% 1.81/1.05  
% 1.81/1.05  ------ General Options
% 1.81/1.05  
% 1.81/1.05  --fof                                   false
% 1.81/1.05  --time_out_real                         305.
% 1.81/1.05  --time_out_virtual                      -1.
% 1.81/1.05  --symbol_type_check                     false
% 1.81/1.05  --clausify_out                          false
% 1.81/1.05  --sig_cnt_out                           false
% 1.81/1.05  --trig_cnt_out                          false
% 1.81/1.05  --trig_cnt_out_tolerance                1.
% 1.81/1.05  --trig_cnt_out_sk_spl                   false
% 1.81/1.05  --abstr_cl_out                          false
% 1.81/1.05  
% 1.81/1.05  ------ Global Options
% 1.81/1.05  
% 1.81/1.05  --schedule                              default
% 1.81/1.05  --add_important_lit                     false
% 1.81/1.05  --prop_solver_per_cl                    1000
% 1.81/1.05  --min_unsat_core                        false
% 1.81/1.05  --soft_assumptions                      false
% 1.81/1.05  --soft_lemma_size                       3
% 1.81/1.05  --prop_impl_unit_size                   0
% 1.81/1.05  --prop_impl_unit                        []
% 1.81/1.05  --share_sel_clauses                     true
% 1.81/1.05  --reset_solvers                         false
% 1.81/1.05  --bc_imp_inh                            [conj_cone]
% 1.81/1.05  --conj_cone_tolerance                   3.
% 1.81/1.05  --extra_neg_conj                        none
% 1.81/1.05  --large_theory_mode                     true
% 1.81/1.05  --prolific_symb_bound                   200
% 1.81/1.05  --lt_threshold                          2000
% 1.81/1.05  --clause_weak_htbl                      true
% 1.81/1.05  --gc_record_bc_elim                     false
% 1.81/1.05  
% 1.81/1.05  ------ Preprocessing Options
% 1.81/1.05  
% 1.81/1.05  --preprocessing_flag                    true
% 1.81/1.05  --time_out_prep_mult                    0.1
% 1.81/1.05  --splitting_mode                        input
% 1.81/1.05  --splitting_grd                         true
% 1.81/1.05  --splitting_cvd                         false
% 1.81/1.05  --splitting_cvd_svl                     false
% 1.81/1.05  --splitting_nvd                         32
% 1.81/1.05  --sub_typing                            true
% 1.81/1.05  --prep_gs_sim                           true
% 1.81/1.05  --prep_unflatten                        true
% 1.81/1.05  --prep_res_sim                          true
% 1.81/1.05  --prep_upred                            true
% 1.81/1.05  --prep_sem_filter                       exhaustive
% 1.81/1.05  --prep_sem_filter_out                   false
% 1.81/1.05  --pred_elim                             true
% 1.81/1.05  --res_sim_input                         true
% 1.81/1.05  --eq_ax_congr_red                       true
% 1.81/1.05  --pure_diseq_elim                       true
% 1.81/1.05  --brand_transform                       false
% 1.81/1.05  --non_eq_to_eq                          false
% 1.81/1.05  --prep_def_merge                        true
% 1.81/1.05  --prep_def_merge_prop_impl              false
% 1.81/1.05  --prep_def_merge_mbd                    true
% 1.81/1.05  --prep_def_merge_tr_red                 false
% 1.81/1.05  --prep_def_merge_tr_cl                  false
% 1.81/1.05  --smt_preprocessing                     true
% 1.81/1.05  --smt_ac_axioms                         fast
% 1.81/1.05  --preprocessed_out                      false
% 1.81/1.05  --preprocessed_stats                    false
% 1.81/1.05  
% 1.81/1.05  ------ Abstraction refinement Options
% 1.81/1.05  
% 1.81/1.05  --abstr_ref                             []
% 1.81/1.05  --abstr_ref_prep                        false
% 1.81/1.05  --abstr_ref_until_sat                   false
% 1.81/1.05  --abstr_ref_sig_restrict                funpre
% 1.81/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 1.81/1.05  --abstr_ref_under                       []
% 1.81/1.05  
% 1.81/1.05  ------ SAT Options
% 1.81/1.05  
% 1.81/1.05  --sat_mode                              false
% 1.81/1.05  --sat_fm_restart_options                ""
% 1.81/1.05  --sat_gr_def                            false
% 1.81/1.05  --sat_epr_types                         true
% 1.81/1.05  --sat_non_cyclic_types                  false
% 1.81/1.05  --sat_finite_models                     false
% 1.81/1.05  --sat_fm_lemmas                         false
% 1.81/1.05  --sat_fm_prep                           false
% 1.81/1.05  --sat_fm_uc_incr                        true
% 1.81/1.05  --sat_out_model                         small
% 1.81/1.05  --sat_out_clauses                       false
% 1.81/1.05  
% 1.81/1.05  ------ QBF Options
% 1.81/1.05  
% 1.81/1.05  --qbf_mode                              false
% 1.81/1.05  --qbf_elim_univ                         false
% 1.81/1.05  --qbf_dom_inst                          none
% 1.81/1.05  --qbf_dom_pre_inst                      false
% 1.81/1.05  --qbf_sk_in                             false
% 1.81/1.05  --qbf_pred_elim                         true
% 1.81/1.05  --qbf_split                             512
% 1.81/1.05  
% 1.81/1.05  ------ BMC1 Options
% 1.81/1.05  
% 1.81/1.05  --bmc1_incremental                      false
% 1.81/1.05  --bmc1_axioms                           reachable_all
% 1.81/1.05  --bmc1_min_bound                        0
% 1.81/1.05  --bmc1_max_bound                        -1
% 1.81/1.05  --bmc1_max_bound_default                -1
% 1.81/1.05  --bmc1_symbol_reachability              true
% 1.81/1.05  --bmc1_property_lemmas                  false
% 1.81/1.05  --bmc1_k_induction                      false
% 1.81/1.05  --bmc1_non_equiv_states                 false
% 1.81/1.05  --bmc1_deadlock                         false
% 1.81/1.05  --bmc1_ucm                              false
% 1.81/1.05  --bmc1_add_unsat_core                   none
% 1.81/1.05  --bmc1_unsat_core_children              false
% 1.81/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 1.81/1.05  --bmc1_out_stat                         full
% 1.81/1.05  --bmc1_ground_init                      false
% 1.81/1.05  --bmc1_pre_inst_next_state              false
% 1.81/1.05  --bmc1_pre_inst_state                   false
% 1.81/1.05  --bmc1_pre_inst_reach_state             false
% 1.81/1.05  --bmc1_out_unsat_core                   false
% 1.81/1.05  --bmc1_aig_witness_out                  false
% 1.81/1.05  --bmc1_verbose                          false
% 1.81/1.05  --bmc1_dump_clauses_tptp                false
% 1.81/1.05  --bmc1_dump_unsat_core_tptp             false
% 1.81/1.05  --bmc1_dump_file                        -
% 1.81/1.05  --bmc1_ucm_expand_uc_limit              128
% 1.81/1.05  --bmc1_ucm_n_expand_iterations          6
% 1.81/1.05  --bmc1_ucm_extend_mode                  1
% 1.81/1.05  --bmc1_ucm_init_mode                    2
% 1.81/1.05  --bmc1_ucm_cone_mode                    none
% 1.81/1.05  --bmc1_ucm_reduced_relation_type        0
% 1.81/1.05  --bmc1_ucm_relax_model                  4
% 1.81/1.05  --bmc1_ucm_full_tr_after_sat            true
% 1.81/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 1.81/1.05  --bmc1_ucm_layered_model                none
% 1.81/1.05  --bmc1_ucm_max_lemma_size               10
% 1.81/1.05  
% 1.81/1.05  ------ AIG Options
% 1.81/1.05  
% 1.81/1.05  --aig_mode                              false
% 1.81/1.05  
% 1.81/1.05  ------ Instantiation Options
% 1.81/1.05  
% 1.81/1.05  --instantiation_flag                    true
% 1.81/1.05  --inst_sos_flag                         false
% 1.81/1.05  --inst_sos_phase                        true
% 1.81/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.81/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.81/1.05  --inst_lit_sel_side                     none
% 1.81/1.05  --inst_solver_per_active                1400
% 1.81/1.05  --inst_solver_calls_frac                1.
% 1.81/1.05  --inst_passive_queue_type               priority_queues
% 1.81/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.81/1.05  --inst_passive_queues_freq              [25;2]
% 1.81/1.05  --inst_dismatching                      true
% 1.81/1.05  --inst_eager_unprocessed_to_passive     true
% 1.81/1.05  --inst_prop_sim_given                   true
% 1.81/1.05  --inst_prop_sim_new                     false
% 1.81/1.05  --inst_subs_new                         false
% 1.81/1.05  --inst_eq_res_simp                      false
% 1.81/1.05  --inst_subs_given                       false
% 1.81/1.05  --inst_orphan_elimination               true
% 1.81/1.05  --inst_learning_loop_flag               true
% 1.81/1.05  --inst_learning_start                   3000
% 1.81/1.05  --inst_learning_factor                  2
% 1.81/1.05  --inst_start_prop_sim_after_learn       3
% 1.81/1.05  --inst_sel_renew                        solver
% 1.81/1.05  --inst_lit_activity_flag                true
% 1.81/1.05  --inst_restr_to_given                   false
% 1.81/1.05  --inst_activity_threshold               500
% 1.81/1.05  --inst_out_proof                        true
% 1.81/1.05  
% 1.81/1.05  ------ Resolution Options
% 1.81/1.05  
% 1.81/1.05  --resolution_flag                       false
% 1.81/1.05  --res_lit_sel                           adaptive
% 1.81/1.05  --res_lit_sel_side                      none
% 1.81/1.05  --res_ordering                          kbo
% 1.81/1.05  --res_to_prop_solver                    active
% 1.81/1.05  --res_prop_simpl_new                    false
% 1.81/1.05  --res_prop_simpl_given                  true
% 1.81/1.05  --res_passive_queue_type                priority_queues
% 1.81/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.81/1.05  --res_passive_queues_freq               [15;5]
% 1.81/1.05  --res_forward_subs                      full
% 1.81/1.05  --res_backward_subs                     full
% 1.81/1.05  --res_forward_subs_resolution           true
% 1.81/1.05  --res_backward_subs_resolution          true
% 1.81/1.05  --res_orphan_elimination                true
% 1.81/1.05  --res_time_limit                        2.
% 1.81/1.05  --res_out_proof                         true
% 1.81/1.05  
% 1.81/1.05  ------ Superposition Options
% 1.81/1.05  
% 1.81/1.05  --superposition_flag                    true
% 1.81/1.05  --sup_passive_queue_type                priority_queues
% 1.81/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.81/1.05  --sup_passive_queues_freq               [8;1;4]
% 1.81/1.05  --demod_completeness_check              fast
% 1.81/1.05  --demod_use_ground                      true
% 1.81/1.05  --sup_to_prop_solver                    passive
% 1.81/1.05  --sup_prop_simpl_new                    true
% 1.81/1.05  --sup_prop_simpl_given                  true
% 1.81/1.05  --sup_fun_splitting                     false
% 1.81/1.05  --sup_smt_interval                      50000
% 1.81/1.05  
% 1.81/1.05  ------ Superposition Simplification Setup
% 1.81/1.05  
% 1.81/1.05  --sup_indices_passive                   []
% 1.81/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.81/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 1.81/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/1.05  --sup_full_bw                           [BwDemod]
% 1.81/1.05  --sup_immed_triv                        [TrivRules]
% 1.81/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.81/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/1.05  --sup_immed_bw_main                     []
% 1.81/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.81/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 1.81/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.81/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.81/1.05  
% 1.81/1.05  ------ Combination Options
% 1.81/1.05  
% 1.81/1.05  --comb_res_mult                         3
% 1.81/1.05  --comb_sup_mult                         2
% 1.81/1.05  --comb_inst_mult                        10
% 1.81/1.05  
% 1.81/1.05  ------ Debug Options
% 1.81/1.05  
% 1.81/1.05  --dbg_backtrace                         false
% 1.81/1.05  --dbg_dump_prop_clauses                 false
% 1.81/1.05  --dbg_dump_prop_clauses_file            -
% 1.81/1.05  --dbg_out_stat                          false
% 1.81/1.05  
% 1.81/1.05  
% 1.81/1.05  
% 1.81/1.05  
% 1.81/1.05  ------ Proving...
% 1.81/1.05  
% 1.81/1.05  
% 1.81/1.05  % SZS status Theorem for theBenchmark.p
% 1.81/1.05  
% 1.81/1.05   Resolution empty clause
% 1.81/1.05  
% 1.81/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 1.81/1.05  
% 1.81/1.05  fof(f12,conjecture,(
% 1.81/1.05    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.81/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.05  
% 1.81/1.05  fof(f13,negated_conjecture,(
% 1.81/1.05    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.81/1.05    inference(negated_conjecture,[],[f12])).
% 1.81/1.05  
% 1.81/1.05  fof(f22,plain,(
% 1.81/1.05    ? [X0] : (? [X1] : ((X0 != X1 & r1_tarski(X0,X1)) & (v1_zfmisc_1(X1) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 1.81/1.05    inference(ennf_transformation,[],[f13])).
% 1.81/1.05  
% 1.81/1.05  fof(f23,plain,(
% 1.81/1.05    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.81/1.05    inference(flattening,[],[f22])).
% 1.81/1.05  
% 1.81/1.05  fof(f31,plain,(
% 1.81/1.05    ( ! [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (sK2 != X0 & r1_tarski(X0,sK2) & v1_zfmisc_1(sK2) & ~v1_xboole_0(sK2))) )),
% 1.81/1.05    introduced(choice_axiom,[])).
% 1.81/1.05  
% 1.81/1.05  fof(f30,plain,(
% 1.81/1.05    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (sK1 != X1 & r1_tarski(sK1,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK1))),
% 1.81/1.05    introduced(choice_axiom,[])).
% 1.81/1.05  
% 1.81/1.05  fof(f32,plain,(
% 1.81/1.05    (sK1 != sK2 & r1_tarski(sK1,sK2) & v1_zfmisc_1(sK2) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)),
% 1.81/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f23,f31,f30])).
% 1.81/1.05  
% 1.81/1.05  fof(f59,plain,(
% 1.81/1.05    r1_tarski(sK1,sK2)),
% 1.81/1.05    inference(cnf_transformation,[],[f32])).
% 1.81/1.05  
% 1.81/1.05  fof(f1,axiom,(
% 1.81/1.05    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.81/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.05  
% 1.81/1.05  fof(f14,plain,(
% 1.81/1.05    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.81/1.05    inference(ennf_transformation,[],[f1])).
% 1.81/1.05  
% 1.81/1.05  fof(f33,plain,(
% 1.81/1.05    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.81/1.05    inference(cnf_transformation,[],[f14])).
% 1.81/1.05  
% 1.81/1.05  fof(f9,axiom,(
% 1.81/1.05    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.81/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.05  
% 1.81/1.05  fof(f51,plain,(
% 1.81/1.05    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.81/1.05    inference(cnf_transformation,[],[f9])).
% 1.81/1.05  
% 1.81/1.05  fof(f61,plain,(
% 1.81/1.05    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.81/1.05    inference(definition_unfolding,[],[f33,f51])).
% 1.81/1.05  
% 1.81/1.05  fof(f10,axiom,(
% 1.81/1.05    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 1.81/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.05  
% 1.81/1.05  fof(f19,plain,(
% 1.81/1.05    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.81/1.05    inference(ennf_transformation,[],[f10])).
% 1.81/1.05  
% 1.81/1.05  fof(f20,plain,(
% 1.81/1.05    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.81/1.05    inference(flattening,[],[f19])).
% 1.81/1.05  
% 1.81/1.05  fof(f52,plain,(
% 1.81/1.05    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.81/1.05    inference(cnf_transformation,[],[f20])).
% 1.81/1.05  
% 1.81/1.05  fof(f5,axiom,(
% 1.81/1.05    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.81/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.05  
% 1.81/1.05  fof(f37,plain,(
% 1.81/1.05    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.81/1.05    inference(cnf_transformation,[],[f5])).
% 1.81/1.05  
% 1.81/1.05  fof(f70,plain,(
% 1.81/1.05    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.81/1.05    inference(definition_unfolding,[],[f52,f37])).
% 1.81/1.05  
% 1.81/1.05  fof(f11,axiom,(
% 1.81/1.05    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 1.81/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.05  
% 1.81/1.05  fof(f21,plain,(
% 1.81/1.05    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 1.81/1.05    inference(ennf_transformation,[],[f11])).
% 1.81/1.05  
% 1.81/1.05  fof(f26,plain,(
% 1.81/1.05    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 1.81/1.05    inference(nnf_transformation,[],[f21])).
% 1.81/1.05  
% 1.81/1.05  fof(f27,plain,(
% 1.81/1.05    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 1.81/1.05    inference(rectify,[],[f26])).
% 1.81/1.05  
% 1.81/1.05  fof(f28,plain,(
% 1.81/1.05    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK0(X0)) = X0 & m1_subset_1(sK0(X0),X0)))),
% 1.81/1.05    introduced(choice_axiom,[])).
% 1.81/1.05  
% 1.81/1.05  fof(f29,plain,(
% 1.81/1.05    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK0(X0)) = X0 & m1_subset_1(sK0(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 1.81/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 1.81/1.05  
% 1.81/1.05  fof(f53,plain,(
% 1.81/1.05    ( ! [X0] : (m1_subset_1(sK0(X0),X0) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 1.81/1.05    inference(cnf_transformation,[],[f29])).
% 1.81/1.05  
% 1.81/1.05  fof(f58,plain,(
% 1.81/1.05    v1_zfmisc_1(sK2)),
% 1.81/1.05    inference(cnf_transformation,[],[f32])).
% 1.81/1.05  
% 1.81/1.05  fof(f57,plain,(
% 1.81/1.05    ~v1_xboole_0(sK2)),
% 1.81/1.05    inference(cnf_transformation,[],[f32])).
% 1.81/1.05  
% 1.81/1.05  fof(f54,plain,(
% 1.81/1.05    ( ! [X0] : (k6_domain_1(X0,sK0(X0)) = X0 | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 1.81/1.05    inference(cnf_transformation,[],[f29])).
% 1.81/1.05  
% 1.81/1.05  fof(f8,axiom,(
% 1.81/1.05    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k2_xboole_0(X1,X2) = k1_tarski(X0))),
% 1.81/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.05  
% 1.81/1.05  fof(f18,plain,(
% 1.81/1.05    ! [X0,X1,X2] : ((k1_xboole_0 = X2 & k1_tarski(X0) = X1) | (k1_tarski(X0) = X2 & k1_xboole_0 = X1) | (k1_tarski(X0) = X2 & k1_tarski(X0) = X1) | k2_xboole_0(X1,X2) != k1_tarski(X0))),
% 1.81/1.05    inference(ennf_transformation,[],[f8])).
% 1.81/1.05  
% 1.81/1.05  fof(f43,plain,(
% 1.81/1.05    ( ! [X2,X0,X1] : (k1_tarski(X0) = X1 | k1_xboole_0 = X1 | k1_tarski(X0) = X1 | k2_xboole_0(X1,X2) != k1_tarski(X0)) )),
% 1.81/1.05    inference(cnf_transformation,[],[f18])).
% 1.81/1.05  
% 1.81/1.05  fof(f69,plain,(
% 1.81/1.05    ( ! [X2,X0,X1] : (k2_tarski(X0,X0) = X1 | k1_xboole_0 = X1 | k2_tarski(X0,X0) = X1 | k2_tarski(X0,X0) != k3_tarski(k2_tarski(X1,X2))) )),
% 1.81/1.05    inference(definition_unfolding,[],[f43,f37,f37,f51,f37])).
% 1.81/1.05  
% 1.81/1.05  fof(f6,axiom,(
% 1.81/1.05    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.81/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.05  
% 1.81/1.05  fof(f24,plain,(
% 1.81/1.05    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.81/1.05    inference(nnf_transformation,[],[f6])).
% 1.81/1.05  
% 1.81/1.05  fof(f25,plain,(
% 1.81/1.05    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.81/1.05    inference(flattening,[],[f24])).
% 1.81/1.05  
% 1.81/1.05  fof(f38,plain,(
% 1.81/1.05    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 1.81/1.05    inference(cnf_transformation,[],[f25])).
% 1.81/1.05  
% 1.81/1.05  fof(f39,plain,(
% 1.81/1.05    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.81/1.05    inference(cnf_transformation,[],[f25])).
% 1.81/1.05  
% 1.81/1.05  fof(f72,plain,(
% 1.81/1.05    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.81/1.05    inference(equality_resolution,[],[f39])).
% 1.81/1.05  
% 1.81/1.05  fof(f2,axiom,(
% 1.81/1.05    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.81/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.05  
% 1.81/1.05  fof(f34,plain,(
% 1.81/1.05    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.81/1.05    inference(cnf_transformation,[],[f2])).
% 1.81/1.05  
% 1.81/1.05  fof(f3,axiom,(
% 1.81/1.05    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.81/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.05  
% 1.81/1.05  fof(f35,plain,(
% 1.81/1.05    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.81/1.05    inference(cnf_transformation,[],[f3])).
% 1.81/1.05  
% 1.81/1.05  fof(f4,axiom,(
% 1.81/1.05    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 1.81/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.81/1.05  
% 1.81/1.05  fof(f15,plain,(
% 1.81/1.05    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 1.81/1.05    inference(ennf_transformation,[],[f4])).
% 1.81/1.05  
% 1.81/1.05  fof(f16,plain,(
% 1.81/1.05    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 1.81/1.05    inference(flattening,[],[f15])).
% 1.81/1.05  
% 1.81/1.05  fof(f36,plain,(
% 1.81/1.05    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 1.81/1.05    inference(cnf_transformation,[],[f16])).
% 1.81/1.05  
% 1.81/1.05  fof(f56,plain,(
% 1.81/1.05    ~v1_xboole_0(sK1)),
% 1.81/1.05    inference(cnf_transformation,[],[f32])).
% 1.81/1.05  
% 1.81/1.05  fof(f60,plain,(
% 1.81/1.05    sK1 != sK2),
% 1.81/1.05    inference(cnf_transformation,[],[f32])).
% 1.81/1.05  
% 1.81/1.05  cnf(c_22,negated_conjecture,
% 1.81/1.05      ( r1_tarski(sK1,sK2) ),
% 1.81/1.05      inference(cnf_transformation,[],[f59]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_544,plain,
% 1.81/1.05      ( r1_tarski(sK1,sK2) = iProver_top ),
% 1.81/1.05      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_0,plain,
% 1.81/1.05      ( ~ r1_tarski(X0,X1) | k3_tarski(k2_tarski(X0,X1)) = X1 ),
% 1.81/1.05      inference(cnf_transformation,[],[f61]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_546,plain,
% 1.81/1.05      ( k3_tarski(k2_tarski(X0,X1)) = X1 | r1_tarski(X0,X1) != iProver_top ),
% 1.81/1.05      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_3494,plain,
% 1.81/1.05      ( k3_tarski(k2_tarski(sK1,sK2)) = sK2 ),
% 1.81/1.05      inference(superposition,[status(thm)],[c_544,c_546]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_17,plain,
% 1.81/1.05      ( ~ m1_subset_1(X0,X1)
% 1.81/1.05      | v1_xboole_0(X1)
% 1.81/1.05      | k6_domain_1(X1,X0) = k2_tarski(X0,X0) ),
% 1.81/1.05      inference(cnf_transformation,[],[f70]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_20,plain,
% 1.81/1.05      ( m1_subset_1(sK0(X0),X0) | ~ v1_zfmisc_1(X0) | v1_xboole_0(X0) ),
% 1.81/1.05      inference(cnf_transformation,[],[f53]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_197,plain,
% 1.81/1.05      ( ~ v1_zfmisc_1(X0)
% 1.81/1.05      | v1_xboole_0(X1)
% 1.81/1.05      | v1_xboole_0(X0)
% 1.81/1.05      | X0 != X1
% 1.81/1.05      | k6_domain_1(X1,X2) = k2_tarski(X2,X2)
% 1.81/1.05      | sK0(X0) != X2 ),
% 1.81/1.05      inference(resolution_lifted,[status(thm)],[c_17,c_20]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_198,plain,
% 1.81/1.05      ( ~ v1_zfmisc_1(X0)
% 1.81/1.05      | v1_xboole_0(X0)
% 1.81/1.05      | k6_domain_1(X0,sK0(X0)) = k2_tarski(sK0(X0),sK0(X0)) ),
% 1.81/1.05      inference(unflattening,[status(thm)],[c_197]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_23,negated_conjecture,
% 1.81/1.05      ( v1_zfmisc_1(sK2) ),
% 1.81/1.05      inference(cnf_transformation,[],[f58]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_216,plain,
% 1.81/1.05      ( v1_xboole_0(X0)
% 1.81/1.05      | k2_tarski(sK0(X0),sK0(X0)) = k6_domain_1(X0,sK0(X0))
% 1.81/1.05      | sK2 != X0 ),
% 1.81/1.05      inference(resolution_lifted,[status(thm)],[c_198,c_23]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_217,plain,
% 1.81/1.05      ( v1_xboole_0(sK2)
% 1.81/1.05      | k2_tarski(sK0(sK2),sK0(sK2)) = k6_domain_1(sK2,sK0(sK2)) ),
% 1.81/1.05      inference(unflattening,[status(thm)],[c_216]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_24,negated_conjecture,
% 1.81/1.05      ( ~ v1_xboole_0(sK2) ),
% 1.81/1.05      inference(cnf_transformation,[],[f57]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_219,plain,
% 1.81/1.05      ( k2_tarski(sK0(sK2),sK0(sK2)) = k6_domain_1(sK2,sK0(sK2)) ),
% 1.81/1.05      inference(global_propositional_subsumption,[status(thm)],[c_217,c_24]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_19,plain,
% 1.81/1.05      ( ~ v1_zfmisc_1(X0) | v1_xboole_0(X0) | k6_domain_1(X0,sK0(X0)) = X0 ),
% 1.81/1.05      inference(cnf_transformation,[],[f54]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_224,plain,
% 1.81/1.05      ( v1_xboole_0(X0) | k6_domain_1(X0,sK0(X0)) = X0 | sK2 != X0 ),
% 1.81/1.05      inference(resolution_lifted,[status(thm)],[c_19,c_23]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_225,plain,
% 1.81/1.05      ( v1_xboole_0(sK2) | k6_domain_1(sK2,sK0(sK2)) = sK2 ),
% 1.81/1.05      inference(unflattening,[status(thm)],[c_224]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_227,plain,
% 1.81/1.05      ( k6_domain_1(sK2,sK0(sK2)) = sK2 ),
% 1.81/1.05      inference(global_propositional_subsumption,[status(thm)],[c_225,c_24]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_563,plain,
% 1.81/1.05      ( k2_tarski(sK0(sK2),sK0(sK2)) = sK2 ),
% 1.81/1.05      inference(light_normalisation,[status(thm)],[c_219,c_227]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_16,plain,
% 1.81/1.05      ( k2_tarski(X0,X0) = X1
% 1.81/1.05      | k3_tarski(k2_tarski(X1,X2)) != k2_tarski(X0,X0)
% 1.81/1.05      | k1_xboole_0 = X1 ),
% 1.81/1.05      inference(cnf_transformation,[],[f69]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_2664,plain,
% 1.81/1.05      ( k2_tarski(sK0(sK2),sK0(sK2)) = X0
% 1.81/1.05      | k3_tarski(k2_tarski(X0,X1)) != sK2
% 1.81/1.05      | k1_xboole_0 = X0 ),
% 1.81/1.05      inference(superposition,[status(thm)],[c_563,c_16]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_2668,plain,
% 1.81/1.05      ( k3_tarski(k2_tarski(X0,X1)) != sK2 | sK2 = X0 | k1_xboole_0 = X0 ),
% 1.81/1.05      inference(demodulation,[status(thm)],[c_2664,c_563]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_3692,plain,
% 1.81/1.05      ( sK2 = sK1 | sK1 = k1_xboole_0 ),
% 1.81/1.05      inference(superposition,[status(thm)],[c_3494,c_2668]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_6,plain,
% 1.81/1.05      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 1.81/1.05      | k1_xboole_0 = X1
% 1.81/1.05      | k1_xboole_0 = X0 ),
% 1.81/1.05      inference(cnf_transformation,[],[f38]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_48,plain,
% 1.81/1.05      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 1.81/1.05      | k1_xboole_0 = k1_xboole_0 ),
% 1.81/1.05      inference(instantiation,[status(thm)],[c_6]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_5,plain,
% 1.81/1.05      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.81/1.05      inference(cnf_transformation,[],[f72]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_49,plain,
% 1.81/1.05      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 1.81/1.05      inference(instantiation,[status(thm)],[c_5]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_1,plain,
% 1.81/1.05      ( r1_tarski(k1_xboole_0,X0) ),
% 1.81/1.05      inference(cnf_transformation,[],[f34]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_57,plain,
% 1.81/1.05      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 1.81/1.05      inference(instantiation,[status(thm)],[c_1]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_2,plain,
% 1.81/1.05      ( r1_xboole_0(X0,k1_xboole_0) ),
% 1.81/1.05      inference(cnf_transformation,[],[f35]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_3,plain,
% 1.81/1.05      ( ~ r1_xboole_0(X0,X1) | ~ r1_tarski(X0,X1) | v1_xboole_0(X0) ),
% 1.81/1.05      inference(cnf_transformation,[],[f36]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_180,plain,
% 1.81/1.05      ( ~ r1_tarski(X0,X1) | v1_xboole_0(X0) | X0 != X2 | k1_xboole_0 != X1 ),
% 1.81/1.05      inference(resolution_lifted,[status(thm)],[c_2,c_3]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_181,plain,
% 1.81/1.05      ( ~ r1_tarski(X0,k1_xboole_0) | v1_xboole_0(X0) ),
% 1.81/1.05      inference(unflattening,[status(thm)],[c_180]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_25,negated_conjecture,
% 1.81/1.05      ( ~ v1_xboole_0(sK1) ),
% 1.81/1.05      inference(cnf_transformation,[],[f56]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_241,plain,
% 1.81/1.05      ( ~ r1_tarski(X0,k1_xboole_0) | sK1 != X0 ),
% 1.81/1.05      inference(resolution_lifted,[status(thm)],[c_181,c_25]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_242,plain,
% 1.81/1.05      ( ~ r1_tarski(sK1,k1_xboole_0) ),
% 1.81/1.05      inference(unflattening,[status(thm)],[c_241]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_377,plain,
% 1.81/1.05      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.81/1.05      theory(equality) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_678,plain,
% 1.81/1.05      ( ~ r1_tarski(X0,X1)
% 1.81/1.05      | r1_tarski(sK1,k1_xboole_0)
% 1.81/1.05      | sK1 != X0
% 1.81/1.05      | k1_xboole_0 != X1 ),
% 1.81/1.05      inference(instantiation,[status(thm)],[c_377]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_680,plain,
% 1.81/1.05      ( r1_tarski(sK1,k1_xboole_0)
% 1.81/1.05      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 1.81/1.05      | sK1 != k1_xboole_0
% 1.81/1.05      | k1_xboole_0 != k1_xboole_0 ),
% 1.81/1.05      inference(instantiation,[status(thm)],[c_678]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_3708,plain,
% 1.81/1.05      ( sK2 = sK1 ),
% 1.81/1.05      inference(global_propositional_subsumption,
% 1.81/1.05                [status(thm)],
% 1.81/1.05                [c_3692,c_48,c_49,c_57,c_242,c_680]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_21,negated_conjecture,
% 1.81/1.05      ( sK1 != sK2 ),
% 1.81/1.05      inference(cnf_transformation,[],[f60]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_3725,plain,
% 1.81/1.05      ( sK1 != sK1 ),
% 1.81/1.05      inference(demodulation,[status(thm)],[c_3708,c_21]) ).
% 1.81/1.05  
% 1.81/1.05  cnf(c_3726,plain,
% 1.81/1.05      ( $false ),
% 1.81/1.05      inference(equality_resolution_simp,[status(thm)],[c_3725]) ).
% 1.81/1.05  
% 1.81/1.05  
% 1.81/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 1.81/1.05  
% 1.81/1.05  ------                               Statistics
% 1.81/1.05  
% 1.81/1.05  ------ General
% 1.81/1.05  
% 1.81/1.05  abstr_ref_over_cycles:                  0
% 1.81/1.05  abstr_ref_under_cycles:                 0
% 1.81/1.05  gc_basic_clause_elim:                   0
% 1.81/1.05  forced_gc_time:                         0
% 1.81/1.05  parsing_time:                           0.012
% 1.81/1.05  unif_index_cands_time:                  0.
% 1.81/1.05  unif_index_add_time:                    0.
% 1.81/1.05  orderings_time:                         0.
% 1.81/1.05  out_proof_time:                         0.011
% 1.81/1.05  total_time:                             0.181
% 1.81/1.05  num_of_symbols:                         44
% 1.81/1.05  num_of_terms:                           5291
% 1.81/1.05  
% 1.81/1.05  ------ Preprocessing
% 1.81/1.05  
% 1.81/1.05  num_of_splits:                          0
% 1.81/1.05  num_of_split_atoms:                     0
% 1.81/1.05  num_of_reused_defs:                     0
% 1.81/1.05  num_eq_ax_congr_red:                    6
% 1.81/1.05  num_of_sem_filtered_clauses:            1
% 1.81/1.05  num_of_subtypes:                        0
% 1.81/1.05  monotx_restored_types:                  0
% 1.81/1.05  sat_num_of_epr_types:                   0
% 1.81/1.05  sat_num_of_non_cyclic_types:            0
% 1.81/1.05  sat_guarded_non_collapsed_types:        0
% 1.81/1.05  num_pure_diseq_elim:                    0
% 1.81/1.05  simp_replaced_by:                       0
% 1.81/1.05  res_preprocessed:                       92
% 1.81/1.05  prep_upred:                             0
% 1.81/1.05  prep_unflattend:                        14
% 1.81/1.05  smt_new_axioms:                         0
% 1.81/1.05  pred_elim_cands:                        1
% 1.81/1.05  pred_elim:                              4
% 1.81/1.05  pred_elim_cl:                           3
% 1.81/1.05  pred_elim_cycles:                       6
% 1.81/1.05  merged_defs:                            0
% 1.81/1.05  merged_defs_ncl:                        0
% 1.81/1.05  bin_hyper_res:                          0
% 1.81/1.05  prep_cycles:                            4
% 1.81/1.05  pred_elim_time:                         0.003
% 1.81/1.05  splitting_time:                         0.
% 1.81/1.05  sem_filter_time:                        0.
% 1.81/1.05  monotx_time:                            0.
% 1.81/1.05  subtype_inf_time:                       0.
% 1.81/1.05  
% 1.81/1.05  ------ Problem properties
% 1.81/1.05  
% 1.81/1.05  clauses:                                18
% 1.81/1.05  conjectures:                            2
% 1.81/1.05  epr:                                    5
% 1.81/1.05  horn:                                   14
% 1.81/1.05  ground:                                 6
% 1.81/1.05  unary:                                  9
% 1.81/1.05  binary:                                 5
% 1.81/1.05  lits:                                   31
% 1.81/1.05  lits_eq:                                18
% 1.81/1.05  fd_pure:                                0
% 1.81/1.05  fd_pseudo:                              0
% 1.81/1.05  fd_cond:                                1
% 1.81/1.05  fd_pseudo_cond:                         3
% 1.81/1.05  ac_symbols:                             0
% 1.81/1.05  
% 1.81/1.05  ------ Propositional Solver
% 1.81/1.05  
% 1.81/1.05  prop_solver_calls:                      28
% 1.81/1.05  prop_fast_solver_calls:                 476
% 1.81/1.05  smt_solver_calls:                       0
% 1.81/1.05  smt_fast_solver_calls:                  0
% 1.81/1.05  prop_num_of_clauses:                    2011
% 1.81/1.05  prop_preprocess_simplified:             6452
% 1.81/1.05  prop_fo_subsumed:                       7
% 1.81/1.05  prop_solver_time:                       0.
% 1.81/1.05  smt_solver_time:                        0.
% 1.81/1.05  smt_fast_solver_time:                   0.
% 1.81/1.05  prop_fast_solver_time:                  0.
% 1.81/1.05  prop_unsat_core_time:                   0.
% 1.81/1.05  
% 1.81/1.05  ------ QBF
% 1.81/1.05  
% 1.81/1.05  qbf_q_res:                              0
% 1.81/1.05  qbf_num_tautologies:                    0
% 1.81/1.05  qbf_prep_cycles:                        0
% 1.81/1.05  
% 1.81/1.05  ------ BMC1
% 1.81/1.05  
% 1.81/1.05  bmc1_current_bound:                     -1
% 1.81/1.05  bmc1_last_solved_bound:                 -1
% 1.81/1.05  bmc1_unsat_core_size:                   -1
% 1.81/1.05  bmc1_unsat_core_parents_size:           -1
% 1.81/1.05  bmc1_merge_next_fun:                    0
% 1.81/1.05  bmc1_unsat_core_clauses_time:           0.
% 1.81/1.05  
% 1.81/1.05  ------ Instantiation
% 1.81/1.05  
% 1.81/1.05  inst_num_of_clauses:                    613
% 1.81/1.05  inst_num_in_passive:                    326
% 1.81/1.05  inst_num_in_active:                     148
% 1.81/1.05  inst_num_in_unprocessed:                139
% 1.81/1.05  inst_num_of_loops:                      150
% 1.81/1.05  inst_num_of_learning_restarts:          0
% 1.81/1.05  inst_num_moves_active_passive:          1
% 1.81/1.05  inst_lit_activity:                      0
% 1.81/1.05  inst_lit_activity_moves:                0
% 1.81/1.05  inst_num_tautologies:                   0
% 1.81/1.05  inst_num_prop_implied:                  0
% 1.81/1.05  inst_num_existing_simplified:           0
% 1.81/1.05  inst_num_eq_res_simplified:             0
% 1.81/1.05  inst_num_child_elim:                    0
% 1.81/1.05  inst_num_of_dismatching_blockings:      1
% 1.81/1.05  inst_num_of_non_proper_insts:           248
% 1.81/1.05  inst_num_of_duplicates:                 0
% 1.81/1.05  inst_inst_num_from_inst_to_res:         0
% 1.81/1.05  inst_dismatching_checking_time:         0.
% 1.81/1.05  
% 1.81/1.05  ------ Resolution
% 1.81/1.05  
% 1.81/1.05  res_num_of_clauses:                     0
% 1.81/1.05  res_num_in_passive:                     0
% 1.81/1.05  res_num_in_active:                      0
% 1.81/1.05  res_num_of_loops:                       96
% 1.81/1.05  res_forward_subset_subsumed:            1
% 1.81/1.05  res_backward_subset_subsumed:           0
% 1.81/1.05  res_forward_subsumed:                   0
% 1.81/1.05  res_backward_subsumed:                  0
% 1.81/1.05  res_forward_subsumption_resolution:     0
% 1.81/1.05  res_backward_subsumption_resolution:    0
% 1.81/1.05  res_clause_to_clause_subsumption:       68
% 1.81/1.05  res_orphan_elimination:                 0
% 1.81/1.05  res_tautology_del:                      3
% 1.81/1.05  res_num_eq_res_simplified:              0
% 1.81/1.05  res_num_sel_changes:                    0
% 1.81/1.05  res_moves_from_active_to_pass:          0
% 1.81/1.05  
% 1.81/1.05  ------ Superposition
% 1.81/1.05  
% 1.81/1.05  sup_time_total:                         0.
% 1.81/1.05  sup_time_generating:                    0.
% 1.81/1.05  sup_time_sim_full:                      0.
% 1.81/1.05  sup_time_sim_immed:                     0.
% 1.81/1.05  
% 1.81/1.05  sup_num_of_clauses:                     21
% 1.81/1.05  sup_num_in_active:                      14
% 1.81/1.05  sup_num_in_passive:                     7
% 1.81/1.05  sup_num_of_loops:                       29
% 1.81/1.05  sup_fw_superposition:                   22
% 1.81/1.05  sup_bw_superposition:                   15
% 1.81/1.05  sup_immediate_simplified:               9
% 1.81/1.05  sup_given_eliminated:                   0
% 1.81/1.05  comparisons_done:                       0
% 1.81/1.05  comparisons_avoided:                    0
% 1.81/1.05  
% 1.81/1.05  ------ Simplifications
% 1.81/1.05  
% 1.81/1.05  
% 1.81/1.05  sim_fw_subset_subsumed:                 3
% 1.81/1.05  sim_bw_subset_subsumed:                 1
% 1.81/1.05  sim_fw_subsumed:                        4
% 1.81/1.05  sim_bw_subsumed:                        0
% 1.81/1.05  sim_fw_subsumption_res:                 0
% 1.81/1.05  sim_bw_subsumption_res:                 0
% 1.81/1.05  sim_tautology_del:                      3
% 1.81/1.05  sim_eq_tautology_del:                   3
% 1.81/1.05  sim_eq_res_simp:                        0
% 1.81/1.05  sim_fw_demodulated:                     3
% 1.81/1.05  sim_bw_demodulated:                     15
% 1.81/1.05  sim_light_normalised:                   2
% 1.81/1.05  sim_joinable_taut:                      0
% 1.81/1.05  sim_joinable_simp:                      0
% 1.81/1.05  sim_ac_normalised:                      0
% 1.81/1.05  sim_smt_subsumption:                    0
% 1.81/1.05  
%------------------------------------------------------------------------------
