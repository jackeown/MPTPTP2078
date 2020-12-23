%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0513+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:43:28 EST 2020

% Result     : Theorem 0.71s
% Output     : CNFRefutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :   38 (  38 expanded)
%              Number of clauses        :   20 (  20 expanded)
%              Number of leaves         :    9 (   9 expanded)
%              Depth                    :    9
%              Number of atoms          :   74 (  74 expanded)
%              Number of equality atoms :   30 (  30 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal clause size      :    4 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X0)
        & v1_xboole_0(X0) )
     => ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f5,conjecture,(
    ! [X0] : k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] : k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(negated_conjecture,[],[f5])).

fof(f11,plain,(
    ? [X0] : k7_relat_1(k1_xboole_0,X0) != k1_xboole_0 ),
    inference(ennf_transformation,[],[f6])).

fof(f12,plain,
    ( ? [X0] : k7_relat_1(k1_xboole_0,X0) != k1_xboole_0
   => k7_relat_1(k1_xboole_0,sK0) != k1_xboole_0 ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    k7_relat_1(k1_xboole_0,sK0) != k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f12])).

fof(f19,plain,(
    k7_relat_1(k1_xboole_0,sK0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f18])).

cnf(c_101,plain,
    ( ~ v1_xboole_0(X0_33)
    | k1_xboole_0 = X0_33 ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_204,plain,
    ( ~ v1_xboole_0(k7_relat_1(k1_xboole_0,sK0))
    | k1_xboole_0 = k7_relat_1(k1_xboole_0,sK0) ),
    inference(instantiation,[status(thm)],[c_101])).

cnf(c_105,plain,
    ( X0_33 != X1_33
    | X2_33 != X1_33
    | X2_33 = X0_33 ),
    theory(equality)).

cnf(c_195,plain,
    ( k7_relat_1(k1_xboole_0,sK0) != X0_33
    | k7_relat_1(k1_xboole_0,sK0) = k1_xboole_0
    | k1_xboole_0 != X0_33 ),
    inference(instantiation,[status(thm)],[c_105])).

cnf(c_196,plain,
    ( k7_relat_1(k1_xboole_0,sK0) != k7_relat_1(k1_xboole_0,sK0)
    | k7_relat_1(k1_xboole_0,sK0) = k1_xboole_0
    | k1_xboole_0 != k7_relat_1(k1_xboole_0,sK0) ),
    inference(instantiation,[status(thm)],[c_195])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k7_relat_1(X0,X1))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_32,plain,
    ( v1_xboole_0(k7_relat_1(X0,X1))
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2,c_0])).

cnf(c_33,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k7_relat_1(X0,X1)) ),
    inference(renaming,[status(thm)],[c_32])).

cnf(c_99,plain,
    ( ~ v1_xboole_0(X0_33)
    | v1_xboole_0(k7_relat_1(X0_33,X0_34)) ),
    inference(subtyping,[status(esa)],[c_33])).

cnf(c_115,plain,
    ( v1_xboole_0(k7_relat_1(k1_xboole_0,sK0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_99])).

cnf(c_5,negated_conjecture,
    ( k7_relat_1(k1_xboole_0,sK0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f19])).

cnf(c_100,negated_conjecture,
    ( k7_relat_1(k1_xboole_0,sK0) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_104,plain,
    ( X0_33 = X0_33 ),
    theory(equality)).

cnf(c_111,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_104])).

cnf(c_107,plain,
    ( X0_33 != X1_33
    | k7_relat_1(X0_33,X0_34) = k7_relat_1(X1_33,X0_34) ),
    theory(equality)).

cnf(c_109,plain,
    ( k7_relat_1(k1_xboole_0,sK0) = k7_relat_1(k1_xboole_0,sK0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_107])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_204,c_196,c_115,c_100,c_111,c_109,c_3])).


%------------------------------------------------------------------------------
