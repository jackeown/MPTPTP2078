%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0548+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:45 EST 2020

% Result     : Theorem 18.73s
% Output     : CNFRefutation 18.73s
% Verified   : 
% Statistics : Number of formulae       :   36 (  50 expanded)
%              Number of clauses        :   13 (  13 expanded)
%              Number of leaves         :    8 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :   43 (  57 expanded)
%              Number of equality atoms :   35 (  49 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal clause size      :    2 (   1 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f784,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3089,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f784])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1881,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f3656,plain,(
    o_0_0_xboole_0 = k6_relat_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f3089,f1881,f1881])).

fof(f657,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2935,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f657])).

fof(f727,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1332,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f727])).

fof(f3016,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1332])).

fof(f693,axiom,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2977,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f693])).

fof(f3619,plain,(
    ! [X0] : o_0_0_xboole_0 = k7_relat_1(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f2977,f1881,f1881])).

fof(f767,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3062,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f767])).

fof(f3645,plain,(
    o_0_0_xboole_0 = k2_relat_1(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f3062,f1881,f1881])).

fof(f730,conjecture,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f731,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f730])).

fof(f1335,plain,(
    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f731])).

fof(f1856,plain,
    ( ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK155) ),
    introduced(choice_axiom,[])).

fof(f1857,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK155) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK155])],[f1335,f1856])).

fof(f3019,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK155) ),
    inference(cnf_transformation,[],[f1857])).

fof(f3631,plain,(
    o_0_0_xboole_0 != k9_relat_1(o_0_0_xboole_0,sK155) ),
    inference(definition_unfolding,[],[f3019,f1881,f1881])).

cnf(c_1201,plain,
    ( k6_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3656])).

cnf(c_1047,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2935])).

cnf(c_50329,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1047])).

cnf(c_59410,plain,
    ( v1_relat_1(o_0_0_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1201,c_50329])).

cnf(c_1128,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f3016])).

cnf(c_50257,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1128])).

cnf(c_59424,plain,
    ( k2_relat_1(k7_relat_1(o_0_0_xboole_0,X0)) = k9_relat_1(o_0_0_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_59410,c_50257])).

cnf(c_1089,plain,
    ( k7_relat_1(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3619])).

cnf(c_1173,plain,
    ( k2_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3645])).

cnf(c_59429,plain,
    ( k9_relat_1(o_0_0_xboole_0,X0) = o_0_0_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_59424,c_1089,c_1173])).

cnf(c_1131,negated_conjecture,
    ( o_0_0_xboole_0 != k9_relat_1(o_0_0_xboole_0,sK155) ),
    inference(cnf_transformation,[],[f3631])).

cnf(c_60343,plain,
    ( o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(demodulation,[status(thm)],[c_59429,c_1131])).

cnf(c_60344,plain,
    ( $false ),
    inference(theory_normalisation,[status(thm)],[c_60343])).

%------------------------------------------------------------------------------
