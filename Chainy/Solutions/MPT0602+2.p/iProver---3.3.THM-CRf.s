%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0602+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:47 EST 2020

% Result     : Theorem 7.07s
% Output     : CNFRefutation 7.07s
% Verified   : 
% Statistics : Number of formulae       :   20 (  27 expanded)
%              Number of clauses        :    6 (   6 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :    9
%              Number of atoms          :   33 (  41 expanded)
%              Number of equality atoms :    4 (  10 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f696,axiom,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f3164,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f696])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2057,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f3889,plain,(
    ! [X0] : v4_relat_1(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f3164,f2057])).

fof(f804,conjecture,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f805,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v5_relat_1(k1_xboole_0,X1)
        & v4_relat_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f804])).

fof(f1494,plain,(
    ? [X0,X1] :
      ( ~ v5_relat_1(k1_xboole_0,X1)
      | ~ v4_relat_1(k1_xboole_0,X0) ) ),
    inference(ennf_transformation,[],[f805])).

fof(f2036,plain,
    ( ? [X0,X1] :
        ( ~ v5_relat_1(k1_xboole_0,X1)
        | ~ v4_relat_1(k1_xboole_0,X0) )
   => ( ~ v5_relat_1(k1_xboole_0,sK164)
      | ~ v4_relat_1(k1_xboole_0,sK163) ) ),
    introduced(choice_axiom,[])).

fof(f2037,plain,
    ( ~ v5_relat_1(k1_xboole_0,sK164)
    | ~ v4_relat_1(k1_xboole_0,sK163) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK163,sK164])],[f1494,f2036])).

fof(f3291,plain,
    ( ~ v5_relat_1(k1_xboole_0,sK164)
    | ~ v4_relat_1(k1_xboole_0,sK163) ),
    inference(cnf_transformation,[],[f2037])).

fof(f3933,plain,
    ( ~ v5_relat_1(o_0_0_xboole_0,sK164)
    | ~ v4_relat_1(o_0_0_xboole_0,sK163) ),
    inference(definition_unfolding,[],[f3291,f2057,f2057])).

fof(f3165,plain,(
    ! [X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(cnf_transformation,[],[f696])).

fof(f3888,plain,(
    ! [X1] : v5_relat_1(o_0_0_xboole_0,X1) ),
    inference(definition_unfolding,[],[f3165,f2057])).

cnf(c_1101,plain,
    ( v4_relat_1(o_0_0_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3889])).

cnf(c_1227,negated_conjecture,
    ( ~ v4_relat_1(o_0_0_xboole_0,sK163)
    | ~ v5_relat_1(o_0_0_xboole_0,sK164) ),
    inference(cnf_transformation,[],[f3933])).

cnf(c_13551,plain,
    ( ~ v5_relat_1(o_0_0_xboole_0,sK164)
    | sK163 != X0
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_1101,c_1227])).

cnf(c_13552,plain,
    ( ~ v5_relat_1(o_0_0_xboole_0,sK164) ),
    inference(unflattening,[status(thm)],[c_13551])).

cnf(c_1100,plain,
    ( v5_relat_1(o_0_0_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3888])).

cnf(c_13556,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_13552,c_1100])).

%------------------------------------------------------------------------------
