%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:55:01 EST 2020

% Result     : Theorem 27.60s
% Output     : CNFRefutation 27.60s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 228 expanded)
%              Number of clauses        :   64 ( 102 expanded)
%              Number of leaves         :   19 (  46 expanded)
%              Depth                    :   13
%              Number of atoms          :  256 ( 473 expanded)
%              Number of equality atoms :   74 ( 109 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_xboole_0(X2,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f39])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f38,f39])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f37,f39])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f31,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f33])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f43,plain,(
    ! [X0] :
      ( k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f55,plain,(
    ! [X0] :
      ( k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) = k3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f43,f39])).

fof(f51,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f56,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
    inference(definition_unfolding,[],[f51,f39])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X2)
    | r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1596,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
    | r1_tarski(X0,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_82235,plain,
    ( ~ r1_tarski(X0,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
    | ~ r1_tarski(k1_relat_1(sK2),X0)
    | r1_tarski(k1_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_1596])).

cnf(c_82237,plain,
    ( r1_tarski(k1_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
    | ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ r1_tarski(sK0,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_82235])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,k5_xboole_0(X2,k4_xboole_0(X1,X2))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1604,plain,
    ( r1_tarski(X0,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
    | ~ r1_tarski(X0,sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_26587,plain,
    ( r1_tarski(k2_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
    | ~ r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_1604])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X2,X1)
    | r1_tarski(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2868,plain,
    ( ~ r1_tarski(X0,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
    | ~ r1_tarski(X1,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
    | r1_tarski(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_9763,plain,
    ( r1_tarski(k5_xboole_0(k1_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),k1_relat_1(sK2))),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
    | ~ r1_tarski(k2_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
    | ~ r1_tarski(k1_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_2868])).

cnf(c_377,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_778,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
    | k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != X1
    | k3_relat_1(sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_377])).

cnf(c_5512,plain,
    ( ~ r1_tarski(k5_xboole_0(k1_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),k1_relat_1(sK2))),X0)
    | r1_tarski(k3_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
    | k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != X0
    | k3_relat_1(sK2) != k5_xboole_0(k1_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),k1_relat_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_778])).

cnf(c_8849,plain,
    ( ~ r1_tarski(k5_xboole_0(k1_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),k1_relat_1(sK2))),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
    | r1_tarski(k3_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
    | k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))
    | k3_relat_1(sK2) != k5_xboole_0(k1_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),k1_relat_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_5512])).

cnf(c_373,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2679,plain,
    ( k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) = k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_373])).

cnf(c_2,plain,
    ( r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2276,plain,
    ( r1_tarski(sK0,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_737,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_739,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1284,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_737,c_739])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_740,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1785,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1284,c_740])).

cnf(c_16,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2182,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1785,c_16])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_744,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2186,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2182,c_744])).

cnf(c_2187,plain,
    ( r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2186])).

cnf(c_8,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_742,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1057,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_737,c_744])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_128,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_129,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_128])).

cnf(c_156,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_129])).

cnf(c_736,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_156])).

cnf(c_1539,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1057,c_736])).

cnf(c_1551,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_742,c_1539])).

cnf(c_11,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_217,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_11,c_9])).

cnf(c_735,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_217])).

cnf(c_1137,plain,
    ( k7_relat_1(sK2,sK0) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_737,c_735])).

cnf(c_1657,plain,
    ( k7_relat_1(sK2,sK0) = sK2 ),
    inference(superposition,[status(thm)],[c_1551,c_1137])).

cnf(c_10,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_741,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1658,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1657,c_741])).

cnf(c_1659,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1658])).

cnf(c_1552,plain,
    ( v1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1551])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) = k3_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1180,plain,
    ( ~ v1_relat_1(sK2)
    | k5_xboole_0(k1_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),k1_relat_1(sK2))) = k3_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1181,plain,
    ( k5_xboole_0(k1_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),k1_relat_1(sK2))) = k3_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1180])).

cnf(c_374,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_838,plain,
    ( X0 != X1
    | k3_relat_1(sK2) != X1
    | k3_relat_1(sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_374])).

cnf(c_930,plain,
    ( X0 != k3_relat_1(sK2)
    | k3_relat_1(sK2) = X0
    | k3_relat_1(sK2) != k3_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_838])).

cnf(c_1088,plain,
    ( k5_xboole_0(k1_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),k1_relat_1(sK2))) != k3_relat_1(sK2)
    | k3_relat_1(sK2) = k5_xboole_0(k1_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),k1_relat_1(sK2)))
    | k3_relat_1(sK2) != k3_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_930])).

cnf(c_918,plain,
    ( k3_relat_1(sK2) = k3_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_373])).

cnf(c_14,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
    inference(cnf_transformation,[],[f56])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_82237,c_26587,c_9763,c_8849,c_2679,c_2276,c_2187,c_1659,c_1552,c_1551,c_1181,c_1088,c_918,c_14])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:56:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 27.60/3.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 27.60/3.98  
% 27.60/3.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.60/3.98  
% 27.60/3.98  ------  iProver source info
% 27.60/3.98  
% 27.60/3.98  git: date: 2020-06-30 10:37:57 +0100
% 27.60/3.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.60/3.98  git: non_committed_changes: false
% 27.60/3.98  git: last_make_outside_of_git: false
% 27.60/3.98  
% 27.60/3.98  ------ 
% 27.60/3.98  
% 27.60/3.98  ------ Input Options
% 27.60/3.98  
% 27.60/3.98  --out_options                           all
% 27.60/3.98  --tptp_safe_out                         true
% 27.60/3.98  --problem_path                          ""
% 27.60/3.98  --include_path                          ""
% 27.60/3.98  --clausifier                            res/vclausify_rel
% 27.60/3.98  --clausifier_options                    ""
% 27.60/3.98  --stdin                                 false
% 27.60/3.98  --stats_out                             all
% 27.60/3.98  
% 27.60/3.98  ------ General Options
% 27.60/3.98  
% 27.60/3.98  --fof                                   false
% 27.60/3.98  --time_out_real                         305.
% 27.60/3.98  --time_out_virtual                      -1.
% 27.60/3.98  --symbol_type_check                     false
% 27.60/3.98  --clausify_out                          false
% 27.60/3.98  --sig_cnt_out                           false
% 27.60/3.98  --trig_cnt_out                          false
% 27.60/3.98  --trig_cnt_out_tolerance                1.
% 27.60/3.98  --trig_cnt_out_sk_spl                   false
% 27.60/3.98  --abstr_cl_out                          false
% 27.60/3.98  
% 27.60/3.98  ------ Global Options
% 27.60/3.98  
% 27.60/3.98  --schedule                              default
% 27.60/3.98  --add_important_lit                     false
% 27.60/3.98  --prop_solver_per_cl                    1000
% 27.60/3.98  --min_unsat_core                        false
% 27.60/3.98  --soft_assumptions                      false
% 27.60/3.98  --soft_lemma_size                       3
% 27.60/3.98  --prop_impl_unit_size                   0
% 27.60/3.98  --prop_impl_unit                        []
% 27.60/3.98  --share_sel_clauses                     true
% 27.60/3.98  --reset_solvers                         false
% 27.60/3.98  --bc_imp_inh                            [conj_cone]
% 27.60/3.98  --conj_cone_tolerance                   3.
% 27.60/3.98  --extra_neg_conj                        none
% 27.60/3.98  --large_theory_mode                     true
% 27.60/3.98  --prolific_symb_bound                   200
% 27.60/3.98  --lt_threshold                          2000
% 27.60/3.98  --clause_weak_htbl                      true
% 27.60/3.98  --gc_record_bc_elim                     false
% 27.60/3.98  
% 27.60/3.98  ------ Preprocessing Options
% 27.60/3.98  
% 27.60/3.98  --preprocessing_flag                    true
% 27.60/3.98  --time_out_prep_mult                    0.1
% 27.60/3.98  --splitting_mode                        input
% 27.60/3.98  --splitting_grd                         true
% 27.60/3.98  --splitting_cvd                         false
% 27.60/3.98  --splitting_cvd_svl                     false
% 27.60/3.98  --splitting_nvd                         32
% 27.60/3.98  --sub_typing                            true
% 27.60/3.98  --prep_gs_sim                           true
% 27.60/3.98  --prep_unflatten                        true
% 27.60/3.98  --prep_res_sim                          true
% 27.60/3.98  --prep_upred                            true
% 27.60/3.98  --prep_sem_filter                       exhaustive
% 27.60/3.98  --prep_sem_filter_out                   false
% 27.60/3.98  --pred_elim                             true
% 27.60/3.98  --res_sim_input                         true
% 27.60/3.98  --eq_ax_congr_red                       true
% 27.60/3.98  --pure_diseq_elim                       true
% 27.60/3.98  --brand_transform                       false
% 27.60/3.98  --non_eq_to_eq                          false
% 27.60/3.98  --prep_def_merge                        true
% 27.60/3.98  --prep_def_merge_prop_impl              false
% 27.60/3.98  --prep_def_merge_mbd                    true
% 27.60/3.98  --prep_def_merge_tr_red                 false
% 27.60/3.98  --prep_def_merge_tr_cl                  false
% 27.60/3.98  --smt_preprocessing                     true
% 27.60/3.98  --smt_ac_axioms                         fast
% 27.60/3.98  --preprocessed_out                      false
% 27.60/3.98  --preprocessed_stats                    false
% 27.60/3.98  
% 27.60/3.98  ------ Abstraction refinement Options
% 27.60/3.98  
% 27.60/3.98  --abstr_ref                             []
% 27.60/3.98  --abstr_ref_prep                        false
% 27.60/3.98  --abstr_ref_until_sat                   false
% 27.60/3.98  --abstr_ref_sig_restrict                funpre
% 27.60/3.98  --abstr_ref_af_restrict_to_split_sk     false
% 27.60/3.98  --abstr_ref_under                       []
% 27.60/3.98  
% 27.60/3.98  ------ SAT Options
% 27.60/3.98  
% 27.60/3.98  --sat_mode                              false
% 27.60/3.98  --sat_fm_restart_options                ""
% 27.60/3.98  --sat_gr_def                            false
% 27.60/3.98  --sat_epr_types                         true
% 27.60/3.98  --sat_non_cyclic_types                  false
% 27.60/3.98  --sat_finite_models                     false
% 27.60/3.98  --sat_fm_lemmas                         false
% 27.60/3.98  --sat_fm_prep                           false
% 27.60/3.98  --sat_fm_uc_incr                        true
% 27.60/3.98  --sat_out_model                         small
% 27.60/3.98  --sat_out_clauses                       false
% 27.60/3.98  
% 27.60/3.98  ------ QBF Options
% 27.60/3.98  
% 27.60/3.98  --qbf_mode                              false
% 27.60/3.98  --qbf_elim_univ                         false
% 27.60/3.98  --qbf_dom_inst                          none
% 27.60/3.98  --qbf_dom_pre_inst                      false
% 27.60/3.98  --qbf_sk_in                             false
% 27.60/3.98  --qbf_pred_elim                         true
% 27.60/3.98  --qbf_split                             512
% 27.60/3.98  
% 27.60/3.98  ------ BMC1 Options
% 27.60/3.98  
% 27.60/3.98  --bmc1_incremental                      false
% 27.60/3.98  --bmc1_axioms                           reachable_all
% 27.60/3.98  --bmc1_min_bound                        0
% 27.60/3.98  --bmc1_max_bound                        -1
% 27.60/3.98  --bmc1_max_bound_default                -1
% 27.60/3.98  --bmc1_symbol_reachability              true
% 27.60/3.98  --bmc1_property_lemmas                  false
% 27.60/3.98  --bmc1_k_induction                      false
% 27.60/3.98  --bmc1_non_equiv_states                 false
% 27.60/3.98  --bmc1_deadlock                         false
% 27.60/3.98  --bmc1_ucm                              false
% 27.60/3.98  --bmc1_add_unsat_core                   none
% 27.60/3.98  --bmc1_unsat_core_children              false
% 27.60/3.98  --bmc1_unsat_core_extrapolate_axioms    false
% 27.60/3.98  --bmc1_out_stat                         full
% 27.60/3.98  --bmc1_ground_init                      false
% 27.60/3.98  --bmc1_pre_inst_next_state              false
% 27.60/3.98  --bmc1_pre_inst_state                   false
% 27.60/3.98  --bmc1_pre_inst_reach_state             false
% 27.60/3.98  --bmc1_out_unsat_core                   false
% 27.60/3.98  --bmc1_aig_witness_out                  false
% 27.60/3.98  --bmc1_verbose                          false
% 27.60/3.98  --bmc1_dump_clauses_tptp                false
% 27.60/3.98  --bmc1_dump_unsat_core_tptp             false
% 27.60/3.98  --bmc1_dump_file                        -
% 27.60/3.98  --bmc1_ucm_expand_uc_limit              128
% 27.60/3.98  --bmc1_ucm_n_expand_iterations          6
% 27.60/3.98  --bmc1_ucm_extend_mode                  1
% 27.60/3.98  --bmc1_ucm_init_mode                    2
% 27.60/3.98  --bmc1_ucm_cone_mode                    none
% 27.60/3.98  --bmc1_ucm_reduced_relation_type        0
% 27.60/3.98  --bmc1_ucm_relax_model                  4
% 27.60/3.98  --bmc1_ucm_full_tr_after_sat            true
% 27.60/3.98  --bmc1_ucm_expand_neg_assumptions       false
% 27.60/3.98  --bmc1_ucm_layered_model                none
% 27.60/3.98  --bmc1_ucm_max_lemma_size               10
% 27.60/3.98  
% 27.60/3.98  ------ AIG Options
% 27.60/3.98  
% 27.60/3.98  --aig_mode                              false
% 27.60/3.98  
% 27.60/3.98  ------ Instantiation Options
% 27.60/3.98  
% 27.60/3.98  --instantiation_flag                    true
% 27.60/3.98  --inst_sos_flag                         true
% 27.60/3.98  --inst_sos_phase                        true
% 27.60/3.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.60/3.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.60/3.98  --inst_lit_sel_side                     num_symb
% 27.60/3.98  --inst_solver_per_active                1400
% 27.60/3.98  --inst_solver_calls_frac                1.
% 27.60/3.98  --inst_passive_queue_type               priority_queues
% 27.60/3.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.60/3.98  --inst_passive_queues_freq              [25;2]
% 27.60/3.98  --inst_dismatching                      true
% 27.60/3.98  --inst_eager_unprocessed_to_passive     true
% 27.60/3.98  --inst_prop_sim_given                   true
% 27.60/3.98  --inst_prop_sim_new                     false
% 27.60/3.98  --inst_subs_new                         false
% 27.60/3.98  --inst_eq_res_simp                      false
% 27.60/3.98  --inst_subs_given                       false
% 27.60/3.98  --inst_orphan_elimination               true
% 27.60/3.98  --inst_learning_loop_flag               true
% 27.60/3.98  --inst_learning_start                   3000
% 27.60/3.98  --inst_learning_factor                  2
% 27.60/3.98  --inst_start_prop_sim_after_learn       3
% 27.60/3.98  --inst_sel_renew                        solver
% 27.60/3.98  --inst_lit_activity_flag                true
% 27.60/3.98  --inst_restr_to_given                   false
% 27.60/3.98  --inst_activity_threshold               500
% 27.60/3.98  --inst_out_proof                        true
% 27.60/3.98  
% 27.60/3.98  ------ Resolution Options
% 27.60/3.98  
% 27.60/3.98  --resolution_flag                       true
% 27.60/3.98  --res_lit_sel                           adaptive
% 27.60/3.98  --res_lit_sel_side                      none
% 27.60/3.98  --res_ordering                          kbo
% 27.60/3.98  --res_to_prop_solver                    active
% 27.60/3.98  --res_prop_simpl_new                    false
% 27.60/3.98  --res_prop_simpl_given                  true
% 27.60/3.98  --res_passive_queue_type                priority_queues
% 27.60/3.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.60/3.98  --res_passive_queues_freq               [15;5]
% 27.60/3.98  --res_forward_subs                      full
% 27.60/3.98  --res_backward_subs                     full
% 27.60/3.98  --res_forward_subs_resolution           true
% 27.60/3.98  --res_backward_subs_resolution          true
% 27.60/3.98  --res_orphan_elimination                true
% 27.60/3.98  --res_time_limit                        2.
% 27.60/3.98  --res_out_proof                         true
% 27.60/3.98  
% 27.60/3.98  ------ Superposition Options
% 27.60/3.98  
% 27.60/3.98  --superposition_flag                    true
% 27.60/3.98  --sup_passive_queue_type                priority_queues
% 27.60/3.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.60/3.98  --sup_passive_queues_freq               [8;1;4]
% 27.60/3.98  --demod_completeness_check              fast
% 27.60/3.98  --demod_use_ground                      true
% 27.60/3.98  --sup_to_prop_solver                    passive
% 27.60/3.98  --sup_prop_simpl_new                    true
% 27.60/3.98  --sup_prop_simpl_given                  true
% 27.60/3.98  --sup_fun_splitting                     true
% 27.60/3.98  --sup_smt_interval                      50000
% 27.60/3.98  
% 27.60/3.98  ------ Superposition Simplification Setup
% 27.60/3.98  
% 27.60/3.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.60/3.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.60/3.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.60/3.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.60/3.98  --sup_full_triv                         [TrivRules;PropSubs]
% 27.60/3.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.60/3.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.60/3.98  --sup_immed_triv                        [TrivRules]
% 27.60/3.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.60/3.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.60/3.98  --sup_immed_bw_main                     []
% 27.60/3.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.60/3.98  --sup_input_triv                        [Unflattening;TrivRules]
% 27.60/3.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.60/3.98  --sup_input_bw                          []
% 27.60/3.98  
% 27.60/3.98  ------ Combination Options
% 27.60/3.98  
% 27.60/3.98  --comb_res_mult                         3
% 27.60/3.98  --comb_sup_mult                         2
% 27.60/3.98  --comb_inst_mult                        10
% 27.60/3.98  
% 27.60/3.98  ------ Debug Options
% 27.60/3.98  
% 27.60/3.98  --dbg_backtrace                         false
% 27.60/3.98  --dbg_dump_prop_clauses                 false
% 27.60/3.98  --dbg_dump_prop_clauses_file            -
% 27.60/3.98  --dbg_out_stat                          false
% 27.60/3.98  ------ Parsing...
% 27.60/3.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.60/3.98  
% 27.60/3.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 27.60/3.98  
% 27.60/3.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.60/3.98  
% 27.60/3.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.60/3.98  ------ Proving...
% 27.60/3.98  ------ Problem Properties 
% 27.60/3.98  
% 27.60/3.98  
% 27.60/3.98  clauses                                 15
% 27.60/3.98  conjectures                             2
% 27.60/3.98  EPR                                     2
% 27.60/3.98  Horn                                    15
% 27.60/3.98  unary                                   4
% 27.60/3.98  binary                                  7
% 27.60/3.98  lits                                    30
% 27.60/3.98  lits eq                                 3
% 27.60/3.98  fd_pure                                 0
% 27.60/3.98  fd_pseudo                               0
% 27.60/3.98  fd_cond                                 0
% 27.60/3.98  fd_pseudo_cond                          0
% 27.60/3.98  AC symbols                              0
% 27.60/3.98  
% 27.60/3.98  ------ Schedule dynamic 5 is on 
% 27.60/3.98  
% 27.60/3.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.60/3.98  
% 27.60/3.98  
% 27.60/3.98  ------ 
% 27.60/3.98  Current options:
% 27.60/3.98  ------ 
% 27.60/3.98  
% 27.60/3.98  ------ Input Options
% 27.60/3.98  
% 27.60/3.98  --out_options                           all
% 27.60/3.98  --tptp_safe_out                         true
% 27.60/3.98  --problem_path                          ""
% 27.60/3.98  --include_path                          ""
% 27.60/3.98  --clausifier                            res/vclausify_rel
% 27.60/3.98  --clausifier_options                    ""
% 27.60/3.98  --stdin                                 false
% 27.60/3.98  --stats_out                             all
% 27.60/3.98  
% 27.60/3.98  ------ General Options
% 27.60/3.98  
% 27.60/3.98  --fof                                   false
% 27.60/3.98  --time_out_real                         305.
% 27.60/3.98  --time_out_virtual                      -1.
% 27.60/3.98  --symbol_type_check                     false
% 27.60/3.98  --clausify_out                          false
% 27.60/3.98  --sig_cnt_out                           false
% 27.60/3.98  --trig_cnt_out                          false
% 27.60/3.98  --trig_cnt_out_tolerance                1.
% 27.60/3.98  --trig_cnt_out_sk_spl                   false
% 27.60/3.98  --abstr_cl_out                          false
% 27.60/3.98  
% 27.60/3.98  ------ Global Options
% 27.60/3.98  
% 27.60/3.98  --schedule                              default
% 27.60/3.98  --add_important_lit                     false
% 27.60/3.98  --prop_solver_per_cl                    1000
% 27.60/3.98  --min_unsat_core                        false
% 27.60/3.98  --soft_assumptions                      false
% 27.60/3.98  --soft_lemma_size                       3
% 27.60/3.98  --prop_impl_unit_size                   0
% 27.60/3.98  --prop_impl_unit                        []
% 27.60/3.98  --share_sel_clauses                     true
% 27.60/3.98  --reset_solvers                         false
% 27.60/3.98  --bc_imp_inh                            [conj_cone]
% 27.60/3.98  --conj_cone_tolerance                   3.
% 27.60/3.98  --extra_neg_conj                        none
% 27.60/3.98  --large_theory_mode                     true
% 27.60/3.98  --prolific_symb_bound                   200
% 27.60/3.98  --lt_threshold                          2000
% 27.60/3.98  --clause_weak_htbl                      true
% 27.60/3.98  --gc_record_bc_elim                     false
% 27.60/3.98  
% 27.60/3.98  ------ Preprocessing Options
% 27.60/3.98  
% 27.60/3.98  --preprocessing_flag                    true
% 27.60/3.98  --time_out_prep_mult                    0.1
% 27.60/3.98  --splitting_mode                        input
% 27.60/3.98  --splitting_grd                         true
% 27.60/3.98  --splitting_cvd                         false
% 27.60/3.98  --splitting_cvd_svl                     false
% 27.60/3.98  --splitting_nvd                         32
% 27.60/3.98  --sub_typing                            true
% 27.60/3.98  --prep_gs_sim                           true
% 27.60/3.98  --prep_unflatten                        true
% 27.60/3.98  --prep_res_sim                          true
% 27.60/3.98  --prep_upred                            true
% 27.60/3.98  --prep_sem_filter                       exhaustive
% 27.60/3.98  --prep_sem_filter_out                   false
% 27.60/3.98  --pred_elim                             true
% 27.60/3.98  --res_sim_input                         true
% 27.60/3.98  --eq_ax_congr_red                       true
% 27.60/3.98  --pure_diseq_elim                       true
% 27.60/3.98  --brand_transform                       false
% 27.60/3.98  --non_eq_to_eq                          false
% 27.60/3.98  --prep_def_merge                        true
% 27.60/3.98  --prep_def_merge_prop_impl              false
% 27.60/3.98  --prep_def_merge_mbd                    true
% 27.60/3.98  --prep_def_merge_tr_red                 false
% 27.60/3.98  --prep_def_merge_tr_cl                  false
% 27.60/3.98  --smt_preprocessing                     true
% 27.60/3.98  --smt_ac_axioms                         fast
% 27.60/3.98  --preprocessed_out                      false
% 27.60/3.98  --preprocessed_stats                    false
% 27.60/3.98  
% 27.60/3.98  ------ Abstraction refinement Options
% 27.60/3.98  
% 27.60/3.98  --abstr_ref                             []
% 27.60/3.98  --abstr_ref_prep                        false
% 27.60/3.98  --abstr_ref_until_sat                   false
% 27.60/3.98  --abstr_ref_sig_restrict                funpre
% 27.60/3.98  --abstr_ref_af_restrict_to_split_sk     false
% 27.60/3.98  --abstr_ref_under                       []
% 27.60/3.98  
% 27.60/3.98  ------ SAT Options
% 27.60/3.98  
% 27.60/3.98  --sat_mode                              false
% 27.60/3.98  --sat_fm_restart_options                ""
% 27.60/3.98  --sat_gr_def                            false
% 27.60/3.98  --sat_epr_types                         true
% 27.60/3.98  --sat_non_cyclic_types                  false
% 27.60/3.98  --sat_finite_models                     false
% 27.60/3.98  --sat_fm_lemmas                         false
% 27.60/3.98  --sat_fm_prep                           false
% 27.60/3.98  --sat_fm_uc_incr                        true
% 27.60/3.98  --sat_out_model                         small
% 27.60/3.98  --sat_out_clauses                       false
% 27.60/3.98  
% 27.60/3.98  ------ QBF Options
% 27.60/3.98  
% 27.60/3.98  --qbf_mode                              false
% 27.60/3.98  --qbf_elim_univ                         false
% 27.60/3.98  --qbf_dom_inst                          none
% 27.60/3.98  --qbf_dom_pre_inst                      false
% 27.60/3.98  --qbf_sk_in                             false
% 27.60/3.98  --qbf_pred_elim                         true
% 27.60/3.98  --qbf_split                             512
% 27.60/3.98  
% 27.60/3.98  ------ BMC1 Options
% 27.60/3.98  
% 27.60/3.98  --bmc1_incremental                      false
% 27.60/3.98  --bmc1_axioms                           reachable_all
% 27.60/3.98  --bmc1_min_bound                        0
% 27.60/3.98  --bmc1_max_bound                        -1
% 27.60/3.98  --bmc1_max_bound_default                -1
% 27.60/3.98  --bmc1_symbol_reachability              true
% 27.60/3.98  --bmc1_property_lemmas                  false
% 27.60/3.98  --bmc1_k_induction                      false
% 27.60/3.98  --bmc1_non_equiv_states                 false
% 27.60/3.98  --bmc1_deadlock                         false
% 27.60/3.98  --bmc1_ucm                              false
% 27.60/3.98  --bmc1_add_unsat_core                   none
% 27.60/3.98  --bmc1_unsat_core_children              false
% 27.60/3.98  --bmc1_unsat_core_extrapolate_axioms    false
% 27.60/3.98  --bmc1_out_stat                         full
% 27.60/3.98  --bmc1_ground_init                      false
% 27.60/3.98  --bmc1_pre_inst_next_state              false
% 27.60/3.98  --bmc1_pre_inst_state                   false
% 27.60/3.98  --bmc1_pre_inst_reach_state             false
% 27.60/3.98  --bmc1_out_unsat_core                   false
% 27.60/3.98  --bmc1_aig_witness_out                  false
% 27.60/3.98  --bmc1_verbose                          false
% 27.60/3.98  --bmc1_dump_clauses_tptp                false
% 27.60/3.98  --bmc1_dump_unsat_core_tptp             false
% 27.60/3.98  --bmc1_dump_file                        -
% 27.60/3.98  --bmc1_ucm_expand_uc_limit              128
% 27.60/3.98  --bmc1_ucm_n_expand_iterations          6
% 27.60/3.98  --bmc1_ucm_extend_mode                  1
% 27.60/3.98  --bmc1_ucm_init_mode                    2
% 27.60/3.98  --bmc1_ucm_cone_mode                    none
% 27.60/3.98  --bmc1_ucm_reduced_relation_type        0
% 27.60/3.98  --bmc1_ucm_relax_model                  4
% 27.60/3.98  --bmc1_ucm_full_tr_after_sat            true
% 27.60/3.98  --bmc1_ucm_expand_neg_assumptions       false
% 27.60/3.98  --bmc1_ucm_layered_model                none
% 27.60/3.98  --bmc1_ucm_max_lemma_size               10
% 27.60/3.98  
% 27.60/3.98  ------ AIG Options
% 27.60/3.98  
% 27.60/3.98  --aig_mode                              false
% 27.60/3.98  
% 27.60/3.98  ------ Instantiation Options
% 27.60/3.98  
% 27.60/3.98  --instantiation_flag                    true
% 27.60/3.98  --inst_sos_flag                         true
% 27.60/3.98  --inst_sos_phase                        true
% 27.60/3.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.60/3.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.60/3.98  --inst_lit_sel_side                     none
% 27.60/3.98  --inst_solver_per_active                1400
% 27.60/3.98  --inst_solver_calls_frac                1.
% 27.60/3.98  --inst_passive_queue_type               priority_queues
% 27.60/3.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.60/3.98  --inst_passive_queues_freq              [25;2]
% 27.60/3.98  --inst_dismatching                      true
% 27.60/3.98  --inst_eager_unprocessed_to_passive     true
% 27.60/3.98  --inst_prop_sim_given                   true
% 27.60/3.98  --inst_prop_sim_new                     false
% 27.60/3.98  --inst_subs_new                         false
% 27.60/3.98  --inst_eq_res_simp                      false
% 27.60/3.98  --inst_subs_given                       false
% 27.60/3.98  --inst_orphan_elimination               true
% 27.60/3.98  --inst_learning_loop_flag               true
% 27.60/3.98  --inst_learning_start                   3000
% 27.60/3.98  --inst_learning_factor                  2
% 27.60/3.98  --inst_start_prop_sim_after_learn       3
% 27.60/3.98  --inst_sel_renew                        solver
% 27.60/3.98  --inst_lit_activity_flag                true
% 27.60/3.98  --inst_restr_to_given                   false
% 27.60/3.98  --inst_activity_threshold               500
% 27.60/3.98  --inst_out_proof                        true
% 27.60/3.98  
% 27.60/3.98  ------ Resolution Options
% 27.60/3.98  
% 27.60/3.98  --resolution_flag                       false
% 27.60/3.98  --res_lit_sel                           adaptive
% 27.60/3.98  --res_lit_sel_side                      none
% 27.60/3.98  --res_ordering                          kbo
% 27.60/3.98  --res_to_prop_solver                    active
% 27.60/3.98  --res_prop_simpl_new                    false
% 27.60/3.98  --res_prop_simpl_given                  true
% 27.60/3.98  --res_passive_queue_type                priority_queues
% 27.60/3.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.60/3.98  --res_passive_queues_freq               [15;5]
% 27.60/3.98  --res_forward_subs                      full
% 27.60/3.98  --res_backward_subs                     full
% 27.60/3.98  --res_forward_subs_resolution           true
% 27.60/3.98  --res_backward_subs_resolution          true
% 27.60/3.98  --res_orphan_elimination                true
% 27.60/3.98  --res_time_limit                        2.
% 27.60/3.98  --res_out_proof                         true
% 27.60/3.98  
% 27.60/3.98  ------ Superposition Options
% 27.60/3.98  
% 27.60/3.98  --superposition_flag                    true
% 27.60/3.98  --sup_passive_queue_type                priority_queues
% 27.60/3.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.60/3.98  --sup_passive_queues_freq               [8;1;4]
% 27.60/3.98  --demod_completeness_check              fast
% 27.60/3.98  --demod_use_ground                      true
% 27.60/3.98  --sup_to_prop_solver                    passive
% 27.60/3.98  --sup_prop_simpl_new                    true
% 27.60/3.98  --sup_prop_simpl_given                  true
% 27.60/3.98  --sup_fun_splitting                     true
% 27.60/3.98  --sup_smt_interval                      50000
% 27.60/3.98  
% 27.60/3.98  ------ Superposition Simplification Setup
% 27.60/3.98  
% 27.60/3.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.60/3.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.60/3.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.60/3.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.60/3.98  --sup_full_triv                         [TrivRules;PropSubs]
% 27.60/3.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.60/3.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.60/3.98  --sup_immed_triv                        [TrivRules]
% 27.60/3.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.60/3.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.60/3.98  --sup_immed_bw_main                     []
% 27.60/3.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.60/3.98  --sup_input_triv                        [Unflattening;TrivRules]
% 27.60/3.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.60/3.98  --sup_input_bw                          []
% 27.60/3.98  
% 27.60/3.98  ------ Combination Options
% 27.60/3.98  
% 27.60/3.98  --comb_res_mult                         3
% 27.60/3.98  --comb_sup_mult                         2
% 27.60/3.98  --comb_inst_mult                        10
% 27.60/3.98  
% 27.60/3.98  ------ Debug Options
% 27.60/3.98  
% 27.60/3.98  --dbg_backtrace                         false
% 27.60/3.98  --dbg_dump_prop_clauses                 false
% 27.60/3.98  --dbg_dump_prop_clauses_file            -
% 27.60/3.98  --dbg_out_stat                          false
% 27.60/3.98  
% 27.60/3.98  
% 27.60/3.98  
% 27.60/3.98  
% 27.60/3.98  ------ Proving...
% 27.60/3.98  
% 27.60/3.98  
% 27.60/3.98  % SZS status Theorem for theBenchmark.p
% 27.60/3.98  
% 27.60/3.98  % SZS output start CNFRefutation for theBenchmark.p
% 27.60/3.98  
% 27.60/3.98  fof(f2,axiom,(
% 27.60/3.98    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 27.60/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.60/3.98  
% 27.60/3.98  fof(f19,plain,(
% 27.60/3.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 27.60/3.98    inference(ennf_transformation,[],[f2])).
% 27.60/3.98  
% 27.60/3.98  fof(f20,plain,(
% 27.60/3.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 27.60/3.98    inference(flattening,[],[f19])).
% 27.60/3.98  
% 27.60/3.98  fof(f36,plain,(
% 27.60/3.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 27.60/3.98    inference(cnf_transformation,[],[f20])).
% 27.60/3.98  
% 27.60/3.98  fof(f1,axiom,(
% 27.60/3.98    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 27.60/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.60/3.98  
% 27.60/3.98  fof(f18,plain,(
% 27.60/3.98    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 27.60/3.98    inference(ennf_transformation,[],[f1])).
% 27.60/3.98  
% 27.60/3.98  fof(f35,plain,(
% 27.60/3.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 27.60/3.98    inference(cnf_transformation,[],[f18])).
% 27.60/3.98  
% 27.60/3.98  fof(f5,axiom,(
% 27.60/3.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 27.60/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.60/3.98  
% 27.60/3.98  fof(f39,plain,(
% 27.60/3.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 27.60/3.98    inference(cnf_transformation,[],[f5])).
% 27.60/3.98  
% 27.60/3.98  fof(f52,plain,(
% 27.60/3.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_xboole_0(X2,k4_xboole_0(X1,X2))) | ~r1_tarski(X0,X1)) )),
% 27.60/3.98    inference(definition_unfolding,[],[f35,f39])).
% 27.60/3.98  
% 27.60/3.98  fof(f4,axiom,(
% 27.60/3.98    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 27.60/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.60/3.98  
% 27.60/3.98  fof(f21,plain,(
% 27.60/3.98    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 27.60/3.98    inference(ennf_transformation,[],[f4])).
% 27.60/3.98  
% 27.60/3.98  fof(f22,plain,(
% 27.60/3.98    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 27.60/3.98    inference(flattening,[],[f21])).
% 27.60/3.98  
% 27.60/3.98  fof(f38,plain,(
% 27.60/3.98    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 27.60/3.98    inference(cnf_transformation,[],[f22])).
% 27.60/3.98  
% 27.60/3.98  fof(f54,plain,(
% 27.60/3.98    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 27.60/3.98    inference(definition_unfolding,[],[f38,f39])).
% 27.60/3.98  
% 27.60/3.98  fof(f3,axiom,(
% 27.60/3.98    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 27.60/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.60/3.98  
% 27.60/3.98  fof(f37,plain,(
% 27.60/3.98    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 27.60/3.98    inference(cnf_transformation,[],[f3])).
% 27.60/3.98  
% 27.60/3.98  fof(f53,plain,(
% 27.60/3.98    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 27.60/3.98    inference(definition_unfolding,[],[f37,f39])).
% 27.60/3.98  
% 27.60/3.98  fof(f15,conjecture,(
% 27.60/3.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 27.60/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.60/3.98  
% 27.60/3.98  fof(f16,negated_conjecture,(
% 27.60/3.98    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)))),
% 27.60/3.98    inference(negated_conjecture,[],[f15])).
% 27.60/3.98  
% 27.60/3.98  fof(f31,plain,(
% 27.60/3.98    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.60/3.98    inference(ennf_transformation,[],[f16])).
% 27.60/3.98  
% 27.60/3.98  fof(f33,plain,(
% 27.60/3.98    ? [X0,X1,X2] : (~r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 27.60/3.98    introduced(choice_axiom,[])).
% 27.60/3.98  
% 27.60/3.98  fof(f34,plain,(
% 27.60/3.98    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 27.60/3.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f31,f33])).
% 27.60/3.98  
% 27.60/3.98  fof(f50,plain,(
% 27.60/3.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 27.60/3.98    inference(cnf_transformation,[],[f34])).
% 27.60/3.98  
% 27.60/3.98  fof(f14,axiom,(
% 27.60/3.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 27.60/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.60/3.98  
% 27.60/3.98  fof(f30,plain,(
% 27.60/3.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.60/3.98    inference(ennf_transformation,[],[f14])).
% 27.60/3.98  
% 27.60/3.98  fof(f49,plain,(
% 27.60/3.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.60/3.98    inference(cnf_transformation,[],[f30])).
% 27.60/3.98  
% 27.60/3.98  fof(f13,axiom,(
% 27.60/3.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 27.60/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.60/3.98  
% 27.60/3.98  fof(f29,plain,(
% 27.60/3.98    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.60/3.98    inference(ennf_transformation,[],[f13])).
% 27.60/3.98  
% 27.60/3.98  fof(f48,plain,(
% 27.60/3.98    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.60/3.98    inference(cnf_transformation,[],[f29])).
% 27.60/3.98  
% 27.60/3.98  fof(f6,axiom,(
% 27.60/3.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 27.60/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.60/3.98  
% 27.60/3.98  fof(f32,plain,(
% 27.60/3.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 27.60/3.98    inference(nnf_transformation,[],[f6])).
% 27.60/3.98  
% 27.60/3.98  fof(f40,plain,(
% 27.60/3.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 27.60/3.98    inference(cnf_transformation,[],[f32])).
% 27.60/3.98  
% 27.60/3.98  fof(f9,axiom,(
% 27.60/3.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 27.60/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.60/3.98  
% 27.60/3.98  fof(f44,plain,(
% 27.60/3.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 27.60/3.98    inference(cnf_transformation,[],[f9])).
% 27.60/3.98  
% 27.60/3.98  fof(f7,axiom,(
% 27.60/3.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 27.60/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.60/3.98  
% 27.60/3.98  fof(f23,plain,(
% 27.60/3.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 27.60/3.98    inference(ennf_transformation,[],[f7])).
% 27.60/3.98  
% 27.60/3.98  fof(f42,plain,(
% 27.60/3.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 27.60/3.98    inference(cnf_transformation,[],[f23])).
% 27.60/3.98  
% 27.60/3.98  fof(f41,plain,(
% 27.60/3.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 27.60/3.98    inference(cnf_transformation,[],[f32])).
% 27.60/3.98  
% 27.60/3.98  fof(f12,axiom,(
% 27.60/3.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 27.60/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.60/3.98  
% 27.60/3.98  fof(f17,plain,(
% 27.60/3.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 27.60/3.98    inference(pure_predicate_removal,[],[f12])).
% 27.60/3.98  
% 27.60/3.98  fof(f28,plain,(
% 27.60/3.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.60/3.98    inference(ennf_transformation,[],[f17])).
% 27.60/3.98  
% 27.60/3.98  fof(f47,plain,(
% 27.60/3.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.60/3.98    inference(cnf_transformation,[],[f28])).
% 27.60/3.98  
% 27.60/3.98  fof(f10,axiom,(
% 27.60/3.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 27.60/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.60/3.98  
% 27.60/3.98  fof(f25,plain,(
% 27.60/3.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 27.60/3.98    inference(ennf_transformation,[],[f10])).
% 27.60/3.98  
% 27.60/3.98  fof(f26,plain,(
% 27.60/3.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 27.60/3.98    inference(flattening,[],[f25])).
% 27.60/3.98  
% 27.60/3.98  fof(f45,plain,(
% 27.60/3.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 27.60/3.98    inference(cnf_transformation,[],[f26])).
% 27.60/3.98  
% 27.60/3.98  fof(f11,axiom,(
% 27.60/3.98    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 27.60/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.60/3.98  
% 27.60/3.98  fof(f27,plain,(
% 27.60/3.98    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 27.60/3.98    inference(ennf_transformation,[],[f11])).
% 27.60/3.98  
% 27.60/3.98  fof(f46,plain,(
% 27.60/3.98    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 27.60/3.98    inference(cnf_transformation,[],[f27])).
% 27.60/3.98  
% 27.60/3.98  fof(f8,axiom,(
% 27.60/3.98    ! [X0] : (v1_relat_1(X0) => k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0))),
% 27.60/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 27.60/3.98  
% 27.60/3.98  fof(f24,plain,(
% 27.60/3.98    ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0))),
% 27.60/3.98    inference(ennf_transformation,[],[f8])).
% 27.60/3.98  
% 27.60/3.98  fof(f43,plain,(
% 27.60/3.98    ( ! [X0] : (k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 27.60/3.98    inference(cnf_transformation,[],[f24])).
% 27.60/3.98  
% 27.60/3.98  fof(f55,plain,(
% 27.60/3.98    ( ! [X0] : (k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) = k3_relat_1(X0) | ~v1_relat_1(X0)) )),
% 27.60/3.98    inference(definition_unfolding,[],[f43,f39])).
% 27.60/3.98  
% 27.60/3.98  fof(f51,plain,(
% 27.60/3.98    ~r1_tarski(k3_relat_1(sK2),k2_xboole_0(sK0,sK1))),
% 27.60/3.98    inference(cnf_transformation,[],[f34])).
% 27.60/3.98  
% 27.60/3.98  fof(f56,plain,(
% 27.60/3.98    ~r1_tarski(k3_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))),
% 27.60/3.98    inference(definition_unfolding,[],[f51,f39])).
% 27.60/3.98  
% 27.60/3.98  cnf(c_1,plain,
% 27.60/3.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X2) | r1_tarski(X0,X2) ),
% 27.60/3.98      inference(cnf_transformation,[],[f36]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_1596,plain,
% 27.60/3.98      ( ~ r1_tarski(X0,X1)
% 27.60/3.98      | ~ r1_tarski(X1,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
% 27.60/3.98      | r1_tarski(X0,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
% 27.60/3.98      inference(instantiation,[status(thm)],[c_1]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_82235,plain,
% 27.60/3.98      ( ~ r1_tarski(X0,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
% 27.60/3.98      | ~ r1_tarski(k1_relat_1(sK2),X0)
% 27.60/3.98      | r1_tarski(k1_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
% 27.60/3.98      inference(instantiation,[status(thm)],[c_1596]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_82237,plain,
% 27.60/3.98      ( r1_tarski(k1_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
% 27.60/3.98      | ~ r1_tarski(k1_relat_1(sK2),sK0)
% 27.60/3.98      | ~ r1_tarski(sK0,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
% 27.60/3.98      inference(instantiation,[status(thm)],[c_82235]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_0,plain,
% 27.60/3.98      ( ~ r1_tarski(X0,X1)
% 27.60/3.98      | r1_tarski(X0,k5_xboole_0(X2,k4_xboole_0(X1,X2))) ),
% 27.60/3.98      inference(cnf_transformation,[],[f52]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_1604,plain,
% 27.60/3.98      ( r1_tarski(X0,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
% 27.60/3.98      | ~ r1_tarski(X0,sK1) ),
% 27.60/3.98      inference(instantiation,[status(thm)],[c_0]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_26587,plain,
% 27.60/3.98      ( r1_tarski(k2_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
% 27.60/3.98      | ~ r1_tarski(k2_relat_1(sK2),sK1) ),
% 27.60/3.98      inference(instantiation,[status(thm)],[c_1604]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_3,plain,
% 27.60/3.98      ( ~ r1_tarski(X0,X1)
% 27.60/3.98      | ~ r1_tarski(X2,X1)
% 27.60/3.98      | r1_tarski(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1) ),
% 27.60/3.98      inference(cnf_transformation,[],[f54]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_2868,plain,
% 27.60/3.98      ( ~ r1_tarski(X0,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
% 27.60/3.98      | ~ r1_tarski(X1,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
% 27.60/3.98      | r1_tarski(k5_xboole_0(X0,k4_xboole_0(X1,X0)),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
% 27.60/3.98      inference(instantiation,[status(thm)],[c_3]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_9763,plain,
% 27.60/3.98      ( r1_tarski(k5_xboole_0(k1_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),k1_relat_1(sK2))),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
% 27.60/3.98      | ~ r1_tarski(k2_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
% 27.60/3.98      | ~ r1_tarski(k1_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
% 27.60/3.98      inference(instantiation,[status(thm)],[c_2868]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_377,plain,
% 27.60/3.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 27.60/3.98      theory(equality) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_778,plain,
% 27.60/3.98      ( ~ r1_tarski(X0,X1)
% 27.60/3.98      | r1_tarski(k3_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
% 27.60/3.98      | k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != X1
% 27.60/3.98      | k3_relat_1(sK2) != X0 ),
% 27.60/3.98      inference(instantiation,[status(thm)],[c_377]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_5512,plain,
% 27.60/3.98      ( ~ r1_tarski(k5_xboole_0(k1_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),k1_relat_1(sK2))),X0)
% 27.60/3.98      | r1_tarski(k3_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
% 27.60/3.98      | k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != X0
% 27.60/3.98      | k3_relat_1(sK2) != k5_xboole_0(k1_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),k1_relat_1(sK2))) ),
% 27.60/3.98      inference(instantiation,[status(thm)],[c_778]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_8849,plain,
% 27.60/3.98      ( ~ r1_tarski(k5_xboole_0(k1_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),k1_relat_1(sK2))),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
% 27.60/3.98      | r1_tarski(k3_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
% 27.60/3.98      | k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))
% 27.60/3.98      | k3_relat_1(sK2) != k5_xboole_0(k1_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),k1_relat_1(sK2))) ),
% 27.60/3.98      inference(instantiation,[status(thm)],[c_5512]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_373,plain,( X0 = X0 ),theory(equality) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_2679,plain,
% 27.60/3.98      ( k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) = k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
% 27.60/3.98      inference(instantiation,[status(thm)],[c_373]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_2,plain,
% 27.60/3.98      ( r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
% 27.60/3.98      inference(cnf_transformation,[],[f53]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_2276,plain,
% 27.60/3.98      ( r1_tarski(sK0,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
% 27.60/3.98      inference(instantiation,[status(thm)],[c_2]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_15,negated_conjecture,
% 27.60/3.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 27.60/3.98      inference(cnf_transformation,[],[f50]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_737,plain,
% 27.60/3.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 27.60/3.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_13,plain,
% 27.60/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.60/3.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 27.60/3.98      inference(cnf_transformation,[],[f49]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_739,plain,
% 27.60/3.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 27.60/3.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 27.60/3.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_1284,plain,
% 27.60/3.98      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 27.60/3.98      inference(superposition,[status(thm)],[c_737,c_739]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_12,plain,
% 27.60/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.60/3.98      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 27.60/3.98      inference(cnf_transformation,[],[f48]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_740,plain,
% 27.60/3.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 27.60/3.98      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 27.60/3.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_1785,plain,
% 27.60/3.98      ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top
% 27.60/3.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 27.60/3.98      inference(superposition,[status(thm)],[c_1284,c_740]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_16,plain,
% 27.60/3.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 27.60/3.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_2182,plain,
% 27.60/3.98      ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK1)) = iProver_top ),
% 27.60/3.98      inference(global_propositional_subsumption,
% 27.60/3.98                [status(thm)],
% 27.60/3.98                [c_1785,c_16]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_5,plain,
% 27.60/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 27.60/3.98      inference(cnf_transformation,[],[f40]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_744,plain,
% 27.60/3.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 27.60/3.98      | r1_tarski(X0,X1) = iProver_top ),
% 27.60/3.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_2186,plain,
% 27.60/3.98      ( r1_tarski(k2_relat_1(sK2),sK1) = iProver_top ),
% 27.60/3.98      inference(superposition,[status(thm)],[c_2182,c_744]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_2187,plain,
% 27.60/3.98      ( r1_tarski(k2_relat_1(sK2),sK1) ),
% 27.60/3.98      inference(predicate_to_equality_rev,[status(thm)],[c_2186]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_8,plain,
% 27.60/3.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 27.60/3.98      inference(cnf_transformation,[],[f44]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_742,plain,
% 27.60/3.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 27.60/3.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_1057,plain,
% 27.60/3.98      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 27.60/3.98      inference(superposition,[status(thm)],[c_737,c_744]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_6,plain,
% 27.60/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 27.60/3.98      | ~ v1_relat_1(X1)
% 27.60/3.98      | v1_relat_1(X0) ),
% 27.60/3.98      inference(cnf_transformation,[],[f42]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_4,plain,
% 27.60/3.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 27.60/3.98      inference(cnf_transformation,[],[f41]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_128,plain,
% 27.60/3.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 27.60/3.98      inference(prop_impl,[status(thm)],[c_4]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_129,plain,
% 27.60/3.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 27.60/3.98      inference(renaming,[status(thm)],[c_128]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_156,plain,
% 27.60/3.98      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 27.60/3.98      inference(bin_hyper_res,[status(thm)],[c_6,c_129]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_736,plain,
% 27.60/3.98      ( r1_tarski(X0,X1) != iProver_top
% 27.60/3.98      | v1_relat_1(X1) != iProver_top
% 27.60/3.98      | v1_relat_1(X0) = iProver_top ),
% 27.60/3.98      inference(predicate_to_equality,[status(thm)],[c_156]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_1539,plain,
% 27.60/3.98      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 27.60/3.98      | v1_relat_1(sK2) = iProver_top ),
% 27.60/3.98      inference(superposition,[status(thm)],[c_1057,c_736]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_1551,plain,
% 27.60/3.98      ( v1_relat_1(sK2) = iProver_top ),
% 27.60/3.98      inference(superposition,[status(thm)],[c_742,c_1539]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_11,plain,
% 27.60/3.98      ( v4_relat_1(X0,X1)
% 27.60/3.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 27.60/3.98      inference(cnf_transformation,[],[f47]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_9,plain,
% 27.60/3.98      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 27.60/3.98      inference(cnf_transformation,[],[f45]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_217,plain,
% 27.60/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.60/3.98      | ~ v1_relat_1(X0)
% 27.60/3.98      | k7_relat_1(X0,X1) = X0 ),
% 27.60/3.98      inference(resolution,[status(thm)],[c_11,c_9]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_735,plain,
% 27.60/3.98      ( k7_relat_1(X0,X1) = X0
% 27.60/3.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 27.60/3.98      | v1_relat_1(X0) != iProver_top ),
% 27.60/3.98      inference(predicate_to_equality,[status(thm)],[c_217]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_1137,plain,
% 27.60/3.98      ( k7_relat_1(sK2,sK0) = sK2 | v1_relat_1(sK2) != iProver_top ),
% 27.60/3.98      inference(superposition,[status(thm)],[c_737,c_735]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_1657,plain,
% 27.60/3.98      ( k7_relat_1(sK2,sK0) = sK2 ),
% 27.60/3.98      inference(superposition,[status(thm)],[c_1551,c_1137]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_10,plain,
% 27.60/3.98      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 27.60/3.98      inference(cnf_transformation,[],[f46]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_741,plain,
% 27.60/3.98      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 27.60/3.98      | v1_relat_1(X0) != iProver_top ),
% 27.60/3.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_1658,plain,
% 27.60/3.98      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top
% 27.60/3.98      | v1_relat_1(sK2) != iProver_top ),
% 27.60/3.98      inference(superposition,[status(thm)],[c_1657,c_741]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_1659,plain,
% 27.60/3.98      ( r1_tarski(k1_relat_1(sK2),sK0) | ~ v1_relat_1(sK2) ),
% 27.60/3.98      inference(predicate_to_equality_rev,[status(thm)],[c_1658]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_1552,plain,
% 27.60/3.98      ( v1_relat_1(sK2) ),
% 27.60/3.98      inference(predicate_to_equality_rev,[status(thm)],[c_1551]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_7,plain,
% 27.60/3.98      ( ~ v1_relat_1(X0)
% 27.60/3.98      | k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) = k3_relat_1(X0) ),
% 27.60/3.98      inference(cnf_transformation,[],[f55]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_1180,plain,
% 27.60/3.98      ( ~ v1_relat_1(sK2)
% 27.60/3.98      | k5_xboole_0(k1_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),k1_relat_1(sK2))) = k3_relat_1(sK2) ),
% 27.60/3.98      inference(instantiation,[status(thm)],[c_7]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_1181,plain,
% 27.60/3.98      ( k5_xboole_0(k1_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),k1_relat_1(sK2))) = k3_relat_1(sK2)
% 27.60/3.98      | v1_relat_1(sK2) != iProver_top ),
% 27.60/3.98      inference(predicate_to_equality,[status(thm)],[c_1180]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_374,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_838,plain,
% 27.60/3.98      ( X0 != X1 | k3_relat_1(sK2) != X1 | k3_relat_1(sK2) = X0 ),
% 27.60/3.98      inference(instantiation,[status(thm)],[c_374]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_930,plain,
% 27.60/3.98      ( X0 != k3_relat_1(sK2)
% 27.60/3.98      | k3_relat_1(sK2) = X0
% 27.60/3.98      | k3_relat_1(sK2) != k3_relat_1(sK2) ),
% 27.60/3.98      inference(instantiation,[status(thm)],[c_838]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_1088,plain,
% 27.60/3.98      ( k5_xboole_0(k1_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),k1_relat_1(sK2))) != k3_relat_1(sK2)
% 27.60/3.98      | k3_relat_1(sK2) = k5_xboole_0(k1_relat_1(sK2),k4_xboole_0(k2_relat_1(sK2),k1_relat_1(sK2)))
% 27.60/3.98      | k3_relat_1(sK2) != k3_relat_1(sK2) ),
% 27.60/3.98      inference(instantiation,[status(thm)],[c_930]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_918,plain,
% 27.60/3.98      ( k3_relat_1(sK2) = k3_relat_1(sK2) ),
% 27.60/3.98      inference(instantiation,[status(thm)],[c_373]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(c_14,negated_conjecture,
% 27.60/3.98      ( ~ r1_tarski(k3_relat_1(sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
% 27.60/3.98      inference(cnf_transformation,[],[f56]) ).
% 27.60/3.98  
% 27.60/3.98  cnf(contradiction,plain,
% 27.60/3.98      ( $false ),
% 27.60/3.98      inference(minisat,
% 27.60/3.98                [status(thm)],
% 27.60/3.98                [c_82237,c_26587,c_9763,c_8849,c_2679,c_2276,c_2187,
% 27.60/3.98                 c_1659,c_1552,c_1551,c_1181,c_1088,c_918,c_14]) ).
% 27.60/3.98  
% 27.60/3.98  
% 27.60/3.98  % SZS output end CNFRefutation for theBenchmark.p
% 27.60/3.98  
% 27.60/3.98  ------                               Statistics
% 27.60/3.98  
% 27.60/3.98  ------ General
% 27.60/3.98  
% 27.60/3.98  abstr_ref_over_cycles:                  0
% 27.60/3.98  abstr_ref_under_cycles:                 0
% 27.60/3.98  gc_basic_clause_elim:                   0
% 27.60/3.98  forced_gc_time:                         0
% 27.60/3.98  parsing_time:                           0.01
% 27.60/3.98  unif_index_cands_time:                  0.
% 27.60/3.98  unif_index_add_time:                    0.
% 27.60/3.98  orderings_time:                         0.
% 27.60/3.98  out_proof_time:                         0.012
% 27.60/3.98  total_time:                             3.116
% 27.60/3.98  num_of_symbols:                         47
% 27.60/3.98  num_of_terms:                           103359
% 27.60/3.98  
% 27.60/3.98  ------ Preprocessing
% 27.60/3.98  
% 27.60/3.98  num_of_splits:                          0
% 27.60/3.98  num_of_split_atoms:                     0
% 27.60/3.98  num_of_reused_defs:                     0
% 27.60/3.98  num_eq_ax_congr_red:                    20
% 27.60/3.98  num_of_sem_filtered_clauses:            1
% 27.60/3.98  num_of_subtypes:                        0
% 27.60/3.98  monotx_restored_types:                  0
% 27.60/3.98  sat_num_of_epr_types:                   0
% 27.60/3.98  sat_num_of_non_cyclic_types:            0
% 27.60/3.98  sat_guarded_non_collapsed_types:        0
% 27.60/3.98  num_pure_diseq_elim:                    0
% 27.60/3.98  simp_replaced_by:                       0
% 27.60/3.98  res_preprocessed:                       84
% 27.60/3.98  prep_upred:                             0
% 27.60/3.98  prep_unflattend:                        0
% 27.60/3.98  smt_new_axioms:                         0
% 27.60/3.98  pred_elim_cands:                        3
% 27.60/3.98  pred_elim:                              1
% 27.60/3.98  pred_elim_cl:                           1
% 27.60/3.98  pred_elim_cycles:                       3
% 27.60/3.98  merged_defs:                            8
% 27.60/3.98  merged_defs_ncl:                        0
% 27.60/3.98  bin_hyper_res:                          9
% 27.60/3.98  prep_cycles:                            4
% 27.60/3.98  pred_elim_time:                         0.
% 27.60/3.98  splitting_time:                         0.
% 27.60/3.98  sem_filter_time:                        0.
% 27.60/3.98  monotx_time:                            0.
% 27.60/3.98  subtype_inf_time:                       0.
% 27.60/3.98  
% 27.60/3.98  ------ Problem properties
% 27.60/3.98  
% 27.60/3.98  clauses:                                15
% 27.60/3.98  conjectures:                            2
% 27.60/3.98  epr:                                    2
% 27.60/3.98  horn:                                   15
% 27.60/3.98  ground:                                 2
% 27.60/3.98  unary:                                  4
% 27.60/3.98  binary:                                 7
% 27.60/3.98  lits:                                   30
% 27.60/3.98  lits_eq:                                3
% 27.60/3.98  fd_pure:                                0
% 27.60/3.98  fd_pseudo:                              0
% 27.60/3.98  fd_cond:                                0
% 27.60/3.98  fd_pseudo_cond:                         0
% 27.60/3.98  ac_symbols:                             0
% 27.60/3.98  
% 27.60/3.98  ------ Propositional Solver
% 27.60/3.98  
% 27.60/3.98  prop_solver_calls:                      39
% 27.60/3.98  prop_fast_solver_calls:                 1662
% 27.60/3.98  smt_solver_calls:                       0
% 27.60/3.98  smt_fast_solver_calls:                  0
% 27.60/3.98  prop_num_of_clauses:                    34655
% 27.60/3.98  prop_preprocess_simplified:             45036
% 27.60/3.98  prop_fo_subsumed:                       30
% 27.60/3.98  prop_solver_time:                       0.
% 27.60/3.98  smt_solver_time:                        0.
% 27.60/3.98  smt_fast_solver_time:                   0.
% 27.60/3.98  prop_fast_solver_time:                  0.
% 27.60/3.98  prop_unsat_core_time:                   0.003
% 27.60/3.98  
% 27.60/3.98  ------ QBF
% 27.60/3.98  
% 27.60/3.98  qbf_q_res:                              0
% 27.60/3.98  qbf_num_tautologies:                    0
% 27.60/3.98  qbf_prep_cycles:                        0
% 27.60/3.98  
% 27.60/3.98  ------ BMC1
% 27.60/3.98  
% 27.60/3.98  bmc1_current_bound:                     -1
% 27.60/3.98  bmc1_last_solved_bound:                 -1
% 27.60/3.98  bmc1_unsat_core_size:                   -1
% 27.60/3.98  bmc1_unsat_core_parents_size:           -1
% 27.60/3.98  bmc1_merge_next_fun:                    0
% 27.60/3.98  bmc1_unsat_core_clauses_time:           0.
% 27.60/3.98  
% 27.60/3.98  ------ Instantiation
% 27.60/3.98  
% 27.60/3.98  inst_num_of_clauses:                    6238
% 27.60/3.98  inst_num_in_passive:                    2069
% 27.60/3.98  inst_num_in_active:                     2140
% 27.60/3.98  inst_num_in_unprocessed:                2032
% 27.60/3.98  inst_num_of_loops:                      2380
% 27.60/3.98  inst_num_of_learning_restarts:          0
% 27.60/3.98  inst_num_moves_active_passive:          235
% 27.60/3.98  inst_lit_activity:                      0
% 27.60/3.98  inst_lit_activity_moves:                3
% 27.60/3.98  inst_num_tautologies:                   0
% 27.60/3.98  inst_num_prop_implied:                  0
% 27.60/3.98  inst_num_existing_simplified:           0
% 27.60/3.98  inst_num_eq_res_simplified:             0
% 27.60/3.98  inst_num_child_elim:                    0
% 27.60/3.98  inst_num_of_dismatching_blockings:      19737
% 27.60/3.98  inst_num_of_non_proper_insts:           9101
% 27.60/3.98  inst_num_of_duplicates:                 0
% 27.60/3.98  inst_inst_num_from_inst_to_res:         0
% 27.60/3.98  inst_dismatching_checking_time:         0.
% 27.60/3.98  
% 27.60/3.98  ------ Resolution
% 27.60/3.98  
% 27.60/3.98  res_num_of_clauses:                     0
% 27.60/3.98  res_num_in_passive:                     0
% 27.60/3.98  res_num_in_active:                      0
% 27.60/3.98  res_num_of_loops:                       88
% 27.60/3.98  res_forward_subset_subsumed:            571
% 27.60/3.98  res_backward_subset_subsumed:           12
% 27.60/3.98  res_forward_subsumed:                   0
% 27.60/3.98  res_backward_subsumed:                  0
% 27.60/3.98  res_forward_subsumption_resolution:     0
% 27.60/3.98  res_backward_subsumption_resolution:    0
% 27.60/3.98  res_clause_to_clause_subsumption:       40003
% 27.60/3.98  res_orphan_elimination:                 0
% 27.60/3.98  res_tautology_del:                      646
% 27.60/3.98  res_num_eq_res_simplified:              0
% 27.60/3.98  res_num_sel_changes:                    0
% 27.60/3.98  res_moves_from_active_to_pass:          0
% 27.60/3.98  
% 27.60/3.98  ------ Superposition
% 27.60/3.98  
% 27.60/3.98  sup_time_total:                         0.
% 27.60/3.98  sup_time_generating:                    0.
% 27.60/3.98  sup_time_sim_full:                      0.
% 27.60/3.98  sup_time_sim_immed:                     0.
% 27.60/3.98  
% 27.60/3.98  sup_num_of_clauses:                     3827
% 27.60/3.98  sup_num_in_active:                      443
% 27.60/3.98  sup_num_in_passive:                     3384
% 27.60/3.98  sup_num_of_loops:                       474
% 27.60/3.98  sup_fw_superposition:                   2836
% 27.60/3.98  sup_bw_superposition:                   2519
% 27.60/3.98  sup_immediate_simplified:               1063
% 27.60/3.98  sup_given_eliminated:                   3
% 27.60/3.98  comparisons_done:                       0
% 27.60/3.98  comparisons_avoided:                    0
% 27.60/3.98  
% 27.60/3.98  ------ Simplifications
% 27.60/3.98  
% 27.60/3.98  
% 27.60/3.98  sim_fw_subset_subsumed:                 404
% 27.60/3.98  sim_bw_subset_subsumed:                 67
% 27.60/3.98  sim_fw_subsumed:                        560
% 27.60/3.98  sim_bw_subsumed:                        139
% 27.60/3.98  sim_fw_subsumption_res:                 0
% 27.60/3.98  sim_bw_subsumption_res:                 0
% 27.60/3.98  sim_tautology_del:                      4
% 27.60/3.98  sim_eq_tautology_del:                   0
% 27.60/3.98  sim_eq_res_simp:                        0
% 27.60/3.98  sim_fw_demodulated:                     11
% 27.60/3.98  sim_bw_demodulated:                     2
% 27.60/3.98  sim_light_normalised:                   13
% 27.60/3.98  sim_joinable_taut:                      0
% 27.60/3.98  sim_joinable_simp:                      0
% 27.60/3.98  sim_ac_normalised:                      0
% 27.60/3.98  sim_smt_subsumption:                    0
% 27.60/3.98  
%------------------------------------------------------------------------------
