%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0513+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:43 EST 2020

% Result     : Theorem 15.54s
% Output     : CNFRefutation 15.54s
% Verified   : 
% Statistics : Number of formulae       :   35 (  41 expanded)
%              Number of clauses        :    9 (   9 expanded)
%              Number of leaves         :    8 (  11 expanded)
%              Depth                    :    9
%              Number of atoms          :   59 (  65 expanded)
%              Number of equality atoms :   19 (  25 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f136,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f852,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f136])).

fof(f1951,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f852])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1776,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f3070,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f1951,f1776])).

fof(f686,conjecture,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f687,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f686])).

fof(f1245,plain,(
    ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f687])).

fof(f1751,plain,
    ( ? [X0] : k1_xboole_0 != k7_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k7_relat_1(k1_xboole_0,sK149) ),
    introduced(choice_axiom,[])).

fof(f1752,plain,(
    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK149) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK149])],[f1245,f1751])).

fof(f2855,plain,(
    k1_xboole_0 != k7_relat_1(k1_xboole_0,sK149) ),
    inference(cnf_transformation,[],[f1752])).

fof(f3455,plain,(
    o_0_0_xboole_0 != k7_relat_1(o_0_0_xboole_0,sK149) ),
    inference(definition_unfolding,[],[f2855,f1776,f1776])).

fof(f664,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X0)
        & v1_xboole_0(X0) )
     => ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1218,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f664])).

fof(f1219,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1218])).

fof(f2831,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1219])).

fof(f638,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1194,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f638])).

fof(f2773,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1194])).

fof(f476,axiom,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2525,plain,(
    ! [X0] : v1_xboole_0(k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f476])).

fof(f458,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2462,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f458])).

fof(f2956,plain,(
    ! [X0] : o_0_0_xboole_0 = k1_subset_1(X0) ),
    inference(definition_unfolding,[],[f2462,f1776])).

fof(f3373,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(definition_unfolding,[],[f2525,f2956])).

cnf(c_181,plain,
    ( ~ v1_xboole_0(X0)
    | o_0_0_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f3070])).

cnf(c_1072,negated_conjecture,
    ( o_0_0_xboole_0 != k7_relat_1(o_0_0_xboole_0,sK149) ),
    inference(cnf_transformation,[],[f3455])).

cnf(c_51922,plain,
    ( ~ v1_xboole_0(k7_relat_1(o_0_0_xboole_0,sK149)) ),
    inference(resolution,[status(thm)],[c_181,c_1072])).

cnf(c_1049,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2831])).

cnf(c_990,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f2773])).

cnf(c_5453,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k7_relat_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1049,c_990])).

cnf(c_52046,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0) ),
    inference(resolution,[status(thm)],[c_51922,c_5453])).

cnf(c_743,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3373])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_52046,c_743])).

%------------------------------------------------------------------------------
