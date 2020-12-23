%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:43:21 EST 2020

% Result     : Theorem 10.73s
% Output     : CNFRefutation 10.73s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 202 expanded)
%              Number of clauses        :   69 (  86 expanded)
%              Number of leaves         :   19 (  43 expanded)
%              Depth                    :   17
%              Number of atoms          :  265 ( 495 expanded)
%              Number of equality atoms :   77 (  94 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f34])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f78,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f100,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f26,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,sK2)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(sK2)))
        & v1_relat_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK1,X1)),k3_xboole_0(k3_relat_1(sK1),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k3_relat_1(sK1),k3_relat_1(sK2)))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f48,f60,f59])).

fof(f98,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f24,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f95,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f99,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k3_relat_1(sK1),k3_relat_1(sK2))) ),
    inference(cnf_transformation,[],[f61])).

fof(f97,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

cnf(c_12,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1847,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_8,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1851,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4519,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1847,c_1851])).

cnf(c_17,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_tarski(X0,X2)
    | ~ r1_tarski(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1844,plain,
    ( r1_xboole_0(X0,X1) != iProver_top
    | r1_tarski(X0,X2) = iProver_top
    | r1_tarski(X0,k2_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7762,plain,
    ( r1_xboole_0(k3_xboole_0(X0,X1),X2) != iProver_top
    | r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4519,c_1844])).

cnf(c_1065,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1064,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_6675,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_1065,c_1064])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_11032,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | X0 = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6675,c_16])).

cnf(c_1067,plain,
    ( ~ r1_xboole_0(X0,X1)
    | r1_xboole_0(X0,X2)
    | X2 != X1 ),
    theory(equality)).

cnf(c_11064,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_xboole_0(X0,k1_xboole_0)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_11032,c_1067])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1857,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4518,plain,
    ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1857,c_1851])).

cnf(c_36,negated_conjecture,
    ( v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1831,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_33,plain,
    ( ~ v1_relat_1(X0)
    | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1833,plain,
    ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_6125,plain,
    ( k3_xboole_0(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) = sK2 ),
    inference(superposition,[status(thm)],[c_1831,c_1833])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1856,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3599,plain,
    ( k4_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1847,c_1856])).

cnf(c_6614,plain,
    ( k4_xboole_0(k2_xboole_0(k3_xboole_0(sK2,X0),sK2),k2_xboole_0(X0,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6125,c_3599])).

cnf(c_18,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2))
    | ~ r1_tarski(X0,X2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1843,plain,
    ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7214,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top
    | r1_tarski(X0,k2_xboole_0(X1,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6614,c_1843])).

cnf(c_14223,plain,
    ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4518,c_7214])).

cnf(c_14249,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_14223])).

cnf(c_33724,plain,
    ( r1_xboole_0(X0,X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11064,c_14249])).

cnf(c_3811,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2)) ),
    inference(resolution,[status(thm)],[c_12,c_8])).

cnf(c_5473,plain,
    ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X2)
    | r1_tarski(k3_xboole_0(X0,X1),X1) ),
    inference(resolution,[status(thm)],[c_17,c_3811])).

cnf(c_34083,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(resolution,[status(thm)],[c_33724,c_5473])).

cnf(c_34726,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) ),
    inference(resolution,[status(thm)],[c_34083,c_1])).

cnf(c_34727,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34726])).

cnf(c_44706,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7762,c_34727])).

cnf(c_34,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_25,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_208,plain,
    ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_34,c_29,c_25])).

cnf(c_209,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_208])).

cnf(c_1829,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_209])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X0,X2)
    | r1_tarski(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1849,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,k3_xboole_0(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_35,negated_conjecture,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k3_relat_1(sK1),k3_relat_1(sK2))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1832,plain,
    ( r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k3_relat_1(sK1),k3_relat_1(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_7871,plain,
    ( r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_relat_1(sK2)) != iProver_top
    | r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_relat_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1849,c_1832])).

cnf(c_37,negated_conjecture,
    ( v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_40,plain,
    ( r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k3_relat_1(sK1),k3_relat_1(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_2278,plain,
    ( r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k3_relat_1(sK1),k3_relat_1(sK2)))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_relat_1(sK2))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_relat_1(sK1)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2279,plain,
    ( r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k3_relat_1(sK1),k3_relat_1(sK2))) = iProver_top
    | r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_relat_1(sK2)) != iProver_top
    | r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_relat_1(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2278])).

cnf(c_15,plain,
    ( r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2476,plain,
    ( r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_relat_1(sK1))
    | k4_xboole_0(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_relat_1(sK1)) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2477,plain,
    ( k4_xboole_0(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_relat_1(sK1)) != k1_xboole_0
    | r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_relat_1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2476])).

cnf(c_3135,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_relat_1(sK1))
    | k4_xboole_0(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_relat_1(sK1)) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2248,plain,
    ( ~ r1_tarski(X0,sK1)
    | r1_tarski(k3_relat_1(X0),k3_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_209])).

cnf(c_2917,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,X0),sK1)
    | r1_tarski(k3_relat_1(k3_xboole_0(sK1,X0)),k3_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_2248])).

cnf(c_3461,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
    | r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_2917])).

cnf(c_9,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2918,plain,
    ( r1_tarski(k3_xboole_0(sK1,X0),sK1) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_5286,plain,
    ( r1_tarski(k3_xboole_0(sK1,sK2),sK1) ),
    inference(instantiation,[status(thm)],[c_2918])).

cnf(c_8440,plain,
    ( r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_relat_1(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7871,c_37,c_40,c_2279,c_2477,c_3135,c_3461,c_5286])).

cnf(c_8445,plain,
    ( r1_tarski(k3_xboole_0(sK1,sK2),sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1829,c_8440])).

cnf(c_39,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_8448,plain,
    ( r1_tarski(k3_xboole_0(sK1,sK2),sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8445,c_39])).

cnf(c_44736,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_44706,c_8448])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:45:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 10.73/1.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.73/1.98  
% 10.73/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 10.73/1.98  
% 10.73/1.98  ------  iProver source info
% 10.73/1.98  
% 10.73/1.98  git: date: 2020-06-30 10:37:57 +0100
% 10.73/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 10.73/1.98  git: non_committed_changes: false
% 10.73/1.98  git: last_make_outside_of_git: false
% 10.73/1.98  
% 10.73/1.98  ------ 
% 10.73/1.98  ------ Parsing...
% 10.73/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 10.73/1.98  
% 10.73/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 10.73/1.98  
% 10.73/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 10.73/1.98  
% 10.73/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 10.73/1.98  ------ Proving...
% 10.73/1.98  ------ Problem Properties 
% 10.73/1.98  
% 10.73/1.98  
% 10.73/1.98  clauses                                 33
% 10.73/1.98  conjectures                             3
% 10.73/1.98  EPR                                     7
% 10.73/1.98  Horn                                    32
% 10.73/1.98  unary                                   8
% 10.73/1.98  binary                                  15
% 10.73/1.98  lits                                    68
% 10.73/1.98  lits eq                                 9
% 10.73/1.98  fd_pure                                 0
% 10.73/1.98  fd_pseudo                               0
% 10.73/1.98  fd_cond                                 1
% 10.73/1.98  fd_pseudo_cond                          4
% 10.73/1.98  AC symbols                              0
% 10.73/1.98  
% 10.73/1.98  ------ Input Options Time Limit: Unbounded
% 10.73/1.98  
% 10.73/1.98  
% 10.73/1.98  ------ 
% 10.73/1.98  Current options:
% 10.73/1.98  ------ 
% 10.73/1.98  
% 10.73/1.98  
% 10.73/1.98  
% 10.73/1.98  
% 10.73/1.98  ------ Proving...
% 10.73/1.98  
% 10.73/1.98  
% 10.73/1.98  % SZS status Theorem for theBenchmark.p
% 10.73/1.98  
% 10.73/1.98   Resolution empty clause
% 10.73/1.98  
% 10.73/1.98  % SZS output start CNFRefutation for theBenchmark.p
% 10.73/1.98  
% 10.73/1.98  fof(f9,axiom,(
% 10.73/1.98    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 10.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.73/1.98  
% 10.73/1.98  fof(f74,plain,(
% 10.73/1.98    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 10.73/1.98    inference(cnf_transformation,[],[f9])).
% 10.73/1.98  
% 10.73/1.98  fof(f5,axiom,(
% 10.73/1.98    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 10.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.73/1.98  
% 10.73/1.98  fof(f30,plain,(
% 10.73/1.98    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 10.73/1.98    inference(ennf_transformation,[],[f5])).
% 10.73/1.98  
% 10.73/1.98  fof(f70,plain,(
% 10.73/1.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 10.73/1.98    inference(cnf_transformation,[],[f30])).
% 10.73/1.98  
% 10.73/1.98  fof(f13,axiom,(
% 10.73/1.98    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 10.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.73/1.98  
% 10.73/1.98  fof(f34,plain,(
% 10.73/1.98    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 10.73/1.98    inference(ennf_transformation,[],[f13])).
% 10.73/1.98  
% 10.73/1.98  fof(f35,plain,(
% 10.73/1.98    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 10.73/1.98    inference(flattening,[],[f34])).
% 10.73/1.98  
% 10.73/1.98  fof(f79,plain,(
% 10.73/1.98    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 10.73/1.98    inference(cnf_transformation,[],[f35])).
% 10.73/1.98  
% 10.73/1.98  fof(f12,axiom,(
% 10.73/1.98    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 10.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.73/1.98  
% 10.73/1.98  fof(f33,plain,(
% 10.73/1.98    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 10.73/1.98    inference(ennf_transformation,[],[f12])).
% 10.73/1.98  
% 10.73/1.98  fof(f78,plain,(
% 10.73/1.98    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 10.73/1.98    inference(cnf_transformation,[],[f33])).
% 10.73/1.98  
% 10.73/1.98  fof(f1,axiom,(
% 10.73/1.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 10.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.73/1.98  
% 10.73/1.98  fof(f49,plain,(
% 10.73/1.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 10.73/1.98    inference(nnf_transformation,[],[f1])).
% 10.73/1.98  
% 10.73/1.98  fof(f50,plain,(
% 10.73/1.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 10.73/1.98    inference(flattening,[],[f49])).
% 10.73/1.98  
% 10.73/1.98  fof(f63,plain,(
% 10.73/1.98    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 10.73/1.98    inference(cnf_transformation,[],[f50])).
% 10.73/1.98  
% 10.73/1.98  fof(f100,plain,(
% 10.73/1.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 10.73/1.98    inference(equality_resolution,[],[f63])).
% 10.73/1.98  
% 10.73/1.98  fof(f26,conjecture,(
% 10.73/1.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 10.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.73/1.98  
% 10.73/1.98  fof(f27,negated_conjecture,(
% 10.73/1.98    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 10.73/1.98    inference(negated_conjecture,[],[f26])).
% 10.73/1.98  
% 10.73/1.98  fof(f48,plain,(
% 10.73/1.98    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 10.73/1.98    inference(ennf_transformation,[],[f27])).
% 10.73/1.98  
% 10.73/1.98  fof(f60,plain,(
% 10.73/1.98    ( ! [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(k3_xboole_0(X0,sK2)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(sK2))) & v1_relat_1(sK2))) )),
% 10.73/1.98    introduced(choice_axiom,[])).
% 10.73/1.98  
% 10.73/1.98  fof(f59,plain,(
% 10.73/1.98    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(sK1,X1)),k3_xboole_0(k3_relat_1(sK1),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK1))),
% 10.73/1.98    introduced(choice_axiom,[])).
% 10.73/1.98  
% 10.73/1.98  fof(f61,plain,(
% 10.73/1.98    (~r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k3_relat_1(sK1),k3_relat_1(sK2))) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 10.73/1.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f48,f60,f59])).
% 10.73/1.98  
% 10.73/1.98  fof(f98,plain,(
% 10.73/1.98    v1_relat_1(sK2)),
% 10.73/1.98    inference(cnf_transformation,[],[f61])).
% 10.73/1.98  
% 10.73/1.98  fof(f24,axiom,(
% 10.73/1.98    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 10.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.73/1.98  
% 10.73/1.98  fof(f45,plain,(
% 10.73/1.98    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 10.73/1.98    inference(ennf_transformation,[],[f24])).
% 10.73/1.98  
% 10.73/1.98  fof(f95,plain,(
% 10.73/1.98    ( ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 10.73/1.98    inference(cnf_transformation,[],[f45])).
% 10.73/1.98  
% 10.73/1.98  fof(f11,axiom,(
% 10.73/1.98    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 10.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.73/1.98  
% 10.73/1.98  fof(f52,plain,(
% 10.73/1.98    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 10.73/1.98    inference(nnf_transformation,[],[f11])).
% 10.73/1.98  
% 10.73/1.98  fof(f77,plain,(
% 10.73/1.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 10.73/1.98    inference(cnf_transformation,[],[f52])).
% 10.73/1.98  
% 10.73/1.98  fof(f14,axiom,(
% 10.73/1.98    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 10.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.73/1.98  
% 10.73/1.98  fof(f36,plain,(
% 10.73/1.98    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 10.73/1.98    inference(ennf_transformation,[],[f14])).
% 10.73/1.98  
% 10.73/1.98  fof(f80,plain,(
% 10.73/1.98    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 10.73/1.98    inference(cnf_transformation,[],[f36])).
% 10.73/1.98  
% 10.73/1.98  fof(f25,axiom,(
% 10.73/1.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 10.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.73/1.98  
% 10.73/1.98  fof(f46,plain,(
% 10.73/1.98    ! [X0] : (! [X1] : ((r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 10.73/1.98    inference(ennf_transformation,[],[f25])).
% 10.73/1.98  
% 10.73/1.98  fof(f47,plain,(
% 10.73/1.98    ! [X0] : (! [X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 10.73/1.98    inference(flattening,[],[f46])).
% 10.73/1.98  
% 10.73/1.98  fof(f96,plain,(
% 10.73/1.98    ( ! [X0,X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 10.73/1.98    inference(cnf_transformation,[],[f47])).
% 10.73/1.98  
% 10.73/1.98  fof(f20,axiom,(
% 10.73/1.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 10.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.73/1.98  
% 10.73/1.98  fof(f41,plain,(
% 10.73/1.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 10.73/1.98    inference(ennf_transformation,[],[f20])).
% 10.73/1.98  
% 10.73/1.98  fof(f91,plain,(
% 10.73/1.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 10.73/1.98    inference(cnf_transformation,[],[f41])).
% 10.73/1.98  
% 10.73/1.98  fof(f17,axiom,(
% 10.73/1.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 10.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.73/1.98  
% 10.73/1.98  fof(f58,plain,(
% 10.73/1.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 10.73/1.98    inference(nnf_transformation,[],[f17])).
% 10.73/1.98  
% 10.73/1.98  fof(f88,plain,(
% 10.73/1.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 10.73/1.98    inference(cnf_transformation,[],[f58])).
% 10.73/1.98  
% 10.73/1.98  fof(f7,axiom,(
% 10.73/1.98    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 10.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.73/1.98  
% 10.73/1.98  fof(f31,plain,(
% 10.73/1.98    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 10.73/1.98    inference(ennf_transformation,[],[f7])).
% 10.73/1.98  
% 10.73/1.98  fof(f32,plain,(
% 10.73/1.98    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 10.73/1.98    inference(flattening,[],[f31])).
% 10.73/1.98  
% 10.73/1.98  fof(f72,plain,(
% 10.73/1.98    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 10.73/1.98    inference(cnf_transformation,[],[f32])).
% 10.73/1.98  
% 10.73/1.98  fof(f99,plain,(
% 10.73/1.98    ~r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k3_relat_1(sK1),k3_relat_1(sK2)))),
% 10.73/1.98    inference(cnf_transformation,[],[f61])).
% 10.73/1.98  
% 10.73/1.98  fof(f97,plain,(
% 10.73/1.98    v1_relat_1(sK1)),
% 10.73/1.98    inference(cnf_transformation,[],[f61])).
% 10.73/1.98  
% 10.73/1.98  fof(f76,plain,(
% 10.73/1.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 10.73/1.98    inference(cnf_transformation,[],[f52])).
% 10.73/1.98  
% 10.73/1.98  fof(f6,axiom,(
% 10.73/1.98    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 10.73/1.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 10.73/1.98  
% 10.73/1.98  fof(f71,plain,(
% 10.73/1.98    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 10.73/1.98    inference(cnf_transformation,[],[f6])).
% 10.73/1.98  
% 10.73/1.98  cnf(c_12,plain,
% 10.73/1.98      ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
% 10.73/1.98      inference(cnf_transformation,[],[f74]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_1847,plain,
% 10.73/1.98      ( r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) = iProver_top ),
% 10.73/1.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_8,plain,
% 10.73/1.98      ( r1_tarski(X0,X1) | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ),
% 10.73/1.98      inference(cnf_transformation,[],[f70]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_1851,plain,
% 10.73/1.98      ( r1_tarski(X0,X1) = iProver_top
% 10.73/1.98      | r1_tarski(k2_xboole_0(X0,X2),X1) != iProver_top ),
% 10.73/1.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_4519,plain,
% 10.73/1.98      ( r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2)) = iProver_top ),
% 10.73/1.98      inference(superposition,[status(thm)],[c_1847,c_1851]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_17,plain,
% 10.73/1.98      ( ~ r1_xboole_0(X0,X1)
% 10.73/1.98      | r1_tarski(X0,X2)
% 10.73/1.98      | ~ r1_tarski(X0,k2_xboole_0(X2,X1)) ),
% 10.73/1.98      inference(cnf_transformation,[],[f79]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_1844,plain,
% 10.73/1.98      ( r1_xboole_0(X0,X1) != iProver_top
% 10.73/1.98      | r1_tarski(X0,X2) = iProver_top
% 10.73/1.98      | r1_tarski(X0,k2_xboole_0(X2,X1)) != iProver_top ),
% 10.73/1.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_7762,plain,
% 10.73/1.98      ( r1_xboole_0(k3_xboole_0(X0,X1),X2) != iProver_top
% 10.73/1.98      | r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 10.73/1.98      inference(superposition,[status(thm)],[c_4519,c_1844]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_1065,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_1064,plain,( X0 = X0 ),theory(equality) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_6675,plain,
% 10.73/1.98      ( X0 != X1 | X1 = X0 ),
% 10.73/1.98      inference(resolution,[status(thm)],[c_1065,c_1064]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_16,plain,
% 10.73/1.98      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 10.73/1.98      inference(cnf_transformation,[],[f78]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_11032,plain,
% 10.73/1.98      ( ~ r1_tarski(X0,k1_xboole_0) | X0 = k1_xboole_0 ),
% 10.73/1.98      inference(resolution,[status(thm)],[c_6675,c_16]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_1067,plain,
% 10.73/1.98      ( ~ r1_xboole_0(X0,X1) | r1_xboole_0(X0,X2) | X2 != X1 ),
% 10.73/1.98      theory(equality) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_11064,plain,
% 10.73/1.98      ( r1_xboole_0(X0,X1)
% 10.73/1.98      | ~ r1_xboole_0(X0,k1_xboole_0)
% 10.73/1.98      | ~ r1_tarski(X1,k1_xboole_0) ),
% 10.73/1.98      inference(resolution,[status(thm)],[c_11032,c_1067]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f100]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_1857,plain,
% 10.73/1.98      ( r1_tarski(X0,X0) = iProver_top ),
% 10.73/1.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_4518,plain,
% 10.73/1.98      ( r1_tarski(X0,k2_xboole_0(X0,X1)) = iProver_top ),
% 10.73/1.98      inference(superposition,[status(thm)],[c_1857,c_1851]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_36,negated_conjecture,
% 10.73/1.98      ( v1_relat_1(sK2) ),
% 10.73/1.98      inference(cnf_transformation,[],[f98]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_1831,plain,
% 10.73/1.98      ( v1_relat_1(sK2) = iProver_top ),
% 10.73/1.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_33,plain,
% 10.73/1.98      ( ~ v1_relat_1(X0)
% 10.73/1.98      | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ),
% 10.73/1.98      inference(cnf_transformation,[],[f95]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_1833,plain,
% 10.73/1.98      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
% 10.73/1.98      | v1_relat_1(X0) != iProver_top ),
% 10.73/1.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_6125,plain,
% 10.73/1.98      ( k3_xboole_0(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) = sK2 ),
% 10.73/1.98      inference(superposition,[status(thm)],[c_1831,c_1833]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_14,plain,
% 10.73/1.98      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 10.73/1.98      inference(cnf_transformation,[],[f77]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_1856,plain,
% 10.73/1.98      ( k4_xboole_0(X0,X1) = k1_xboole_0 | r1_tarski(X0,X1) != iProver_top ),
% 10.73/1.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_3599,plain,
% 10.73/1.98      ( k4_xboole_0(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) = k1_xboole_0 ),
% 10.73/1.98      inference(superposition,[status(thm)],[c_1847,c_1856]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_6614,plain,
% 10.73/1.98      ( k4_xboole_0(k2_xboole_0(k3_xboole_0(sK2,X0),sK2),k2_xboole_0(X0,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = k1_xboole_0 ),
% 10.73/1.98      inference(superposition,[status(thm)],[c_6125,c_3599]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_18,plain,
% 10.73/1.98      ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) | ~ r1_tarski(X0,X2) ),
% 10.73/1.98      inference(cnf_transformation,[],[f80]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_1843,plain,
% 10.73/1.98      ( r1_xboole_0(X0,k4_xboole_0(X1,X2)) = iProver_top
% 10.73/1.98      | r1_tarski(X0,X2) != iProver_top ),
% 10.73/1.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_7214,plain,
% 10.73/1.98      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top
% 10.73/1.98      | r1_tarski(X0,k2_xboole_0(X1,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top ),
% 10.73/1.98      inference(superposition,[status(thm)],[c_6614,c_1843]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_14223,plain,
% 10.73/1.98      ( r1_xboole_0(X0,k1_xboole_0) = iProver_top ),
% 10.73/1.98      inference(superposition,[status(thm)],[c_4518,c_7214]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_14249,plain,
% 10.73/1.98      ( r1_xboole_0(X0,k1_xboole_0) ),
% 10.73/1.98      inference(predicate_to_equality_rev,[status(thm)],[c_14223]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_33724,plain,
% 10.73/1.98      ( r1_xboole_0(X0,X1) | ~ r1_tarski(X1,k1_xboole_0) ),
% 10.73/1.98      inference(global_propositional_subsumption,
% 10.73/1.98                [status(thm)],
% 10.73/1.98                [c_11064,c_14249]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_3811,plain,
% 10.73/1.98      ( r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X1,X2)) ),
% 10.73/1.98      inference(resolution,[status(thm)],[c_12,c_8]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_5473,plain,
% 10.73/1.98      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X2)
% 10.73/1.98      | r1_tarski(k3_xboole_0(X0,X1),X1) ),
% 10.73/1.98      inference(resolution,[status(thm)],[c_17,c_3811]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_34083,plain,
% 10.73/1.98      ( ~ r1_tarski(X0,k1_xboole_0) | r1_tarski(k3_xboole_0(X1,X2),X2) ),
% 10.73/1.98      inference(resolution,[status(thm)],[c_33724,c_5473]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_34726,plain,
% 10.73/1.98      ( r1_tarski(k3_xboole_0(X0,X1),X1) ),
% 10.73/1.98      inference(resolution,[status(thm)],[c_34083,c_1]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_34727,plain,
% 10.73/1.98      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 10.73/1.98      inference(predicate_to_equality,[status(thm)],[c_34726]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_44706,plain,
% 10.73/1.98      ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
% 10.73/1.98      inference(global_propositional_subsumption,
% 10.73/1.98                [status(thm)],
% 10.73/1.98                [c_7762,c_34727]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_34,plain,
% 10.73/1.98      ( ~ r1_tarski(X0,X1)
% 10.73/1.98      | r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
% 10.73/1.98      | ~ v1_relat_1(X0)
% 10.73/1.98      | ~ v1_relat_1(X1) ),
% 10.73/1.98      inference(cnf_transformation,[],[f96]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_29,plain,
% 10.73/1.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 10.73/1.98      inference(cnf_transformation,[],[f91]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_25,plain,
% 10.73/1.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 10.73/1.98      inference(cnf_transformation,[],[f88]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_208,plain,
% 10.73/1.98      ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
% 10.73/1.98      | ~ r1_tarski(X0,X1)
% 10.73/1.98      | ~ v1_relat_1(X1) ),
% 10.73/1.98      inference(global_propositional_subsumption,
% 10.73/1.98                [status(thm)],
% 10.73/1.98                [c_34,c_29,c_25]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_209,plain,
% 10.73/1.98      ( ~ r1_tarski(X0,X1)
% 10.73/1.98      | r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
% 10.73/1.98      | ~ v1_relat_1(X1) ),
% 10.73/1.98      inference(renaming,[status(thm)],[c_208]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_1829,plain,
% 10.73/1.98      ( r1_tarski(X0,X1) != iProver_top
% 10.73/1.98      | r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) = iProver_top
% 10.73/1.98      | v1_relat_1(X1) != iProver_top ),
% 10.73/1.98      inference(predicate_to_equality,[status(thm)],[c_209]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_10,plain,
% 10.73/1.98      ( ~ r1_tarski(X0,X1)
% 10.73/1.98      | ~ r1_tarski(X0,X2)
% 10.73/1.98      | r1_tarski(X0,k3_xboole_0(X1,X2)) ),
% 10.73/1.98      inference(cnf_transformation,[],[f72]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_1849,plain,
% 10.73/1.98      ( r1_tarski(X0,X1) != iProver_top
% 10.73/1.98      | r1_tarski(X0,X2) != iProver_top
% 10.73/1.98      | r1_tarski(X0,k3_xboole_0(X1,X2)) = iProver_top ),
% 10.73/1.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_35,negated_conjecture,
% 10.73/1.98      ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k3_relat_1(sK1),k3_relat_1(sK2))) ),
% 10.73/1.98      inference(cnf_transformation,[],[f99]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_1832,plain,
% 10.73/1.98      ( r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k3_relat_1(sK1),k3_relat_1(sK2))) != iProver_top ),
% 10.73/1.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_7871,plain,
% 10.73/1.98      ( r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_relat_1(sK2)) != iProver_top
% 10.73/1.98      | r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_relat_1(sK1)) != iProver_top ),
% 10.73/1.98      inference(superposition,[status(thm)],[c_1849,c_1832]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_37,negated_conjecture,
% 10.73/1.98      ( v1_relat_1(sK1) ),
% 10.73/1.98      inference(cnf_transformation,[],[f97]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_40,plain,
% 10.73/1.98      ( r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k3_relat_1(sK1),k3_relat_1(sK2))) != iProver_top ),
% 10.73/1.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_2278,plain,
% 10.73/1.98      ( r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k3_relat_1(sK1),k3_relat_1(sK2)))
% 10.73/1.98      | ~ r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_relat_1(sK2))
% 10.73/1.98      | ~ r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_relat_1(sK1)) ),
% 10.73/1.98      inference(instantiation,[status(thm)],[c_10]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_2279,plain,
% 10.73/1.98      ( r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_xboole_0(k3_relat_1(sK1),k3_relat_1(sK2))) = iProver_top
% 10.73/1.98      | r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_relat_1(sK2)) != iProver_top
% 10.73/1.98      | r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_relat_1(sK1)) != iProver_top ),
% 10.73/1.98      inference(predicate_to_equality,[status(thm)],[c_2278]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_15,plain,
% 10.73/1.98      ( r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0 ),
% 10.73/1.98      inference(cnf_transformation,[],[f76]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_2476,plain,
% 10.73/1.98      ( r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_relat_1(sK1))
% 10.73/1.98      | k4_xboole_0(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_relat_1(sK1)) != k1_xboole_0 ),
% 10.73/1.98      inference(instantiation,[status(thm)],[c_15]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_2477,plain,
% 10.73/1.98      ( k4_xboole_0(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_relat_1(sK1)) != k1_xboole_0
% 10.73/1.98      | r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_relat_1(sK1)) = iProver_top ),
% 10.73/1.98      inference(predicate_to_equality,[status(thm)],[c_2476]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_3135,plain,
% 10.73/1.98      ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_relat_1(sK1))
% 10.73/1.98      | k4_xboole_0(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_relat_1(sK1)) = k1_xboole_0 ),
% 10.73/1.98      inference(instantiation,[status(thm)],[c_14]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_2248,plain,
% 10.73/1.98      ( ~ r1_tarski(X0,sK1)
% 10.73/1.98      | r1_tarski(k3_relat_1(X0),k3_relat_1(sK1))
% 10.73/1.98      | ~ v1_relat_1(sK1) ),
% 10.73/1.98      inference(instantiation,[status(thm)],[c_209]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_2917,plain,
% 10.73/1.98      ( ~ r1_tarski(k3_xboole_0(sK1,X0),sK1)
% 10.73/1.98      | r1_tarski(k3_relat_1(k3_xboole_0(sK1,X0)),k3_relat_1(sK1))
% 10.73/1.98      | ~ v1_relat_1(sK1) ),
% 10.73/1.98      inference(instantiation,[status(thm)],[c_2248]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_3461,plain,
% 10.73/1.98      ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
% 10.73/1.98      | r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_relat_1(sK1))
% 10.73/1.98      | ~ v1_relat_1(sK1) ),
% 10.73/1.98      inference(instantiation,[status(thm)],[c_2917]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_9,plain,
% 10.73/1.98      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 10.73/1.98      inference(cnf_transformation,[],[f71]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_2918,plain,
% 10.73/1.98      ( r1_tarski(k3_xboole_0(sK1,X0),sK1) ),
% 10.73/1.98      inference(instantiation,[status(thm)],[c_9]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_5286,plain,
% 10.73/1.98      ( r1_tarski(k3_xboole_0(sK1,sK2),sK1) ),
% 10.73/1.98      inference(instantiation,[status(thm)],[c_2918]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_8440,plain,
% 10.73/1.98      ( r1_tarski(k3_relat_1(k3_xboole_0(sK1,sK2)),k3_relat_1(sK2)) != iProver_top ),
% 10.73/1.98      inference(global_propositional_subsumption,
% 10.73/1.98                [status(thm)],
% 10.73/1.98                [c_7871,c_37,c_40,c_2279,c_2477,c_3135,c_3461,c_5286]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_8445,plain,
% 10.73/1.98      ( r1_tarski(k3_xboole_0(sK1,sK2),sK2) != iProver_top
% 10.73/1.98      | v1_relat_1(sK2) != iProver_top ),
% 10.73/1.98      inference(superposition,[status(thm)],[c_1829,c_8440]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_39,plain,
% 10.73/1.98      ( v1_relat_1(sK2) = iProver_top ),
% 10.73/1.98      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_8448,plain,
% 10.73/1.98      ( r1_tarski(k3_xboole_0(sK1,sK2),sK2) != iProver_top ),
% 10.73/1.98      inference(global_propositional_subsumption,[status(thm)],[c_8445,c_39]) ).
% 10.73/1.98  
% 10.73/1.98  cnf(c_44736,plain,
% 10.73/1.98      ( $false ),
% 10.73/1.98      inference(superposition,[status(thm)],[c_44706,c_8448]) ).
% 10.73/1.98  
% 10.73/1.98  
% 10.73/1.98  % SZS output end CNFRefutation for theBenchmark.p
% 10.73/1.98  
% 10.73/1.98  ------                               Statistics
% 10.73/1.98  
% 10.73/1.98  ------ Selected
% 10.73/1.98  
% 10.73/1.98  total_time:                             1.008
% 10.73/1.98  
%------------------------------------------------------------------------------
