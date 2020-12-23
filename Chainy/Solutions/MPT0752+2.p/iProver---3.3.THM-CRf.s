%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0752+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:51 EST 2020

% Result     : Theorem 19.77s
% Output     : CNFRefutation 19.77s
% Verified   : 
% Statistics : Number of formulae       :   40 (  50 expanded)
%              Number of clauses        :   13 (  13 expanded)
%              Number of leaves         :    9 (  14 expanded)
%              Depth                    :    9
%              Number of atoms          :   84 (  94 expanded)
%              Number of equality atoms :    7 (  17 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1103,conjecture,(
    ! [X0] :
      ( v5_ordinal1(k1_xboole_0)
      & v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1104,negated_conjecture,(
    ~ ! [X0] :
        ( v5_ordinal1(k1_xboole_0)
        & v1_funct_1(k1_xboole_0)
        & v5_relat_1(k1_xboole_0,X0)
        & v1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f1103])).

fof(f2174,plain,(
    ? [X0] :
      ( ~ v5_ordinal1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v5_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1104])).

fof(f2875,plain,
    ( ? [X0] :
        ( ~ v5_ordinal1(k1_xboole_0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v5_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(k1_xboole_0) )
   => ( ~ v5_ordinal1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v5_relat_1(k1_xboole_0,sK253)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    introduced(choice_axiom,[])).

fof(f2876,plain,
    ( ~ v5_ordinal1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,sK253)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK253])],[f2174,f2875])).

fof(f4683,plain,
    ( ~ v5_ordinal1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,sK253)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2876])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2884,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f5354,plain,
    ( ~ v5_ordinal1(o_0_0_xboole_0)
    | ~ v1_funct_1(o_0_0_xboole_0)
    | ~ v5_relat_1(o_0_0_xboole_0,sK253)
    | ~ v1_relat_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f4683,f2884,f2884,f2884,f2884])).

fof(f1057,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v5_ordinal1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2127,plain,(
    ! [X0] :
      ( v5_ordinal1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1057])).

fof(f4596,plain,(
    ! [X0] :
      ( v5_ordinal1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2127])).

fof(f890,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1846,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f890])).

fof(f4231,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1846])).

fof(f638,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1549,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f638])).

fof(f3883,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1549])).

fof(f476,axiom,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3635,plain,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f476])).

fof(f458,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3572,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f458])).

fof(f4698,plain,(
    ! [X0] : o_0_0_xboole_0 = k1_subset_1(X0) ),
    inference(definition_unfolding,[],[f3572,f2884])).

fof(f5116,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f3635,f4698])).

fof(f810,axiom,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f4130,plain,(
    ! [X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(cnf_transformation,[],[f810])).

fof(f5245,plain,(
    ! [X1] : v5_relat_1(o_0_0_xboole_0,X1) ),
    inference(definition_unfolding,[],[f4130,f2884])).

cnf(c_1791,negated_conjecture,
    ( ~ v5_relat_1(o_0_0_xboole_0,sK253)
    | ~ v5_ordinal1(o_0_0_xboole_0)
    | ~ v1_funct_1(o_0_0_xboole_0)
    | ~ v1_relat_1(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f5354])).

cnf(c_1705,plain,
    ( v5_ordinal1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f4596])).

cnf(c_2011,plain,
    ( v5_ordinal1(o_0_0_xboole_0)
    | ~ v1_xboole_0(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1705])).

cnf(c_1340,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f4231])).

cnf(c_2940,plain,
    ( v1_funct_1(o_0_0_xboole_0)
    | ~ v1_xboole_0(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1340])).

cnf(c_992,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f3883])).

cnf(c_3777,plain,
    ( v1_relat_1(o_0_0_xboole_0)
    | ~ v1_xboole_0(o_0_0_xboole_0) ),
    inference(instantiation,[status(thm)],[c_992])).

cnf(c_745,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f5116])).

cnf(c_13904,negated_conjecture,
    ( ~ v5_relat_1(o_0_0_xboole_0,sK253) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1791,c_2011,c_2940,c_3777,c_745])).

cnf(c_49563,plain,
    ( v5_relat_1(o_0_0_xboole_0,sK253) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13904])).

cnf(c_1238,plain,
    ( v5_relat_1(o_0_0_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5245])).

cnf(c_50175,plain,
    ( v5_relat_1(o_0_0_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1238])).

cnf(c_51083,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_49563,c_50175])).

%------------------------------------------------------------------------------
