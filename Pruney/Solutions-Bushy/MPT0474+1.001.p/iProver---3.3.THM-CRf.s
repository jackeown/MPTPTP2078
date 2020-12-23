%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0474+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:23 EST 2020

% Result     : Theorem 0.63s
% Output     : CNFRefutation 0.63s
% Verified   : 
% Statistics : Number of formulae       :   26 (  30 expanded)
%              Number of clauses        :   13 (  14 expanded)
%              Number of leaves         :    6 (   7 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 (  55 expanded)
%              Number of equality atoms :   24 (  28 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal clause size      :    3 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ( v1_relat_1(k4_relat_1(X0))
        & v1_xboole_0(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k4_relat_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f8,plain,(
    ! [X0] :
      ( v1_xboole_0(k4_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f10,plain,(
    ! [X0] :
      ( v1_xboole_0(k4_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f4,conjecture,(
    k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(negated_conjecture,[],[f4])).

fof(f6,plain,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(flattening,[],[f5])).

fof(f13,plain,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f12])).

cnf(c_138,plain,
    ( ~ v1_xboole_0(k4_relat_1(k1_xboole_0))
    | k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_41,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_129,plain,
    ( k4_relat_1(k1_xboole_0) != X0
    | k4_relat_1(k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_130,plain,
    ( k4_relat_1(k1_xboole_0) != k4_relat_1(k1_xboole_0)
    | k4_relat_1(k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != k4_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_129])).

cnf(c_42,plain,
    ( X0 != X1
    | k4_relat_1(X0) = k4_relat_1(X1) ),
    theory(equality)).

cnf(c_44,plain,
    ( k4_relat_1(k1_xboole_0) = k4_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_9,plain,
    ( v1_xboole_0(k4_relat_1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3,negated_conjecture,
    ( k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_138,c_130,c_44,c_9,c_1,c_5,c_3])).


%------------------------------------------------------------------------------
