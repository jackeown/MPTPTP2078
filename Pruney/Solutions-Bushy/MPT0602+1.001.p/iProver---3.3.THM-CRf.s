%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0602+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:42 EST 2020

% Result     : Theorem 0.59s
% Output     : CNFRefutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   17 (  18 expanded)
%              Number of clauses        :    8 (   8 expanded)
%              Number of leaves         :    3 (   4 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  29 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   1 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v5_relat_1(k1_xboole_0,X1)
        & v4_relat_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f4,plain,(
    ? [X0,X1] :
      ( ~ v5_relat_1(k1_xboole_0,X1)
      | ~ v4_relat_1(k1_xboole_0,X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f5,plain,
    ( ? [X0,X1] :
        ( ~ v5_relat_1(k1_xboole_0,X1)
        | ~ v4_relat_1(k1_xboole_0,X0) )
   => ( ~ v5_relat_1(k1_xboole_0,sK1)
      | ~ v4_relat_1(k1_xboole_0,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,
    ( ~ v5_relat_1(k1_xboole_0,sK1)
    | ~ v4_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f4,f5])).

fof(f9,plain,
    ( ~ v5_relat_1(k1_xboole_0,sK1)
    | ~ v4_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f6])).

cnf(c_1,plain,
    ( v4_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

cnf(c_24,plain,
    ( v4_relat_1(k1_xboole_0,X0_34) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_30,plain,
    ( v4_relat_1(k1_xboole_0,sK0) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_0,plain,
    ( v5_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

cnf(c_25,plain,
    ( v5_relat_1(k1_xboole_0,X0_35) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_27,plain,
    ( v5_relat_1(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2,negated_conjecture,
    ( ~ v4_relat_1(k1_xboole_0,sK0)
    | ~ v5_relat_1(k1_xboole_0,sK1) ),
    inference(cnf_transformation,[],[f9])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_30,c_27,c_2])).


%------------------------------------------------------------------------------
