%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0709+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:50 EST 2020

% Result     : Theorem 23.18s
% Output     : CNFRefutation 23.18s
% Verified   : 
% Statistics : Number of formulae       :   35 (  59 expanded)
%              Number of clauses        :   12 (  12 expanded)
%              Number of leaves         :    5 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :  112 ( 252 expanded)
%              Number of equality atoms :   17 (  45 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f948,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1845,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f948])).

fof(f1846,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1845])).

fof(f4108,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1846])).

fof(f955,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1858,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f955])).

fof(f1859,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1858])).

fof(f4115,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1859])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2060,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f2061,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f2060])).

fof(f2679,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2061])).

fof(f968,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f969,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( ( v2_funct_1(X1)
            & r1_tarski(X0,k1_relat_1(X1)) )
         => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f968])).

fof(f1882,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f969])).

fof(f1883,plain,(
    ? [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
      & v2_funct_1(X1)
      & r1_tarski(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1882])).

fof(f2552,plain,
    ( ? [X0,X1] :
        ( k10_relat_1(X1,k9_relat_1(X1,X0)) != X0
        & v2_funct_1(X1)
        & r1_tarski(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k10_relat_1(sK210,k9_relat_1(sK210,sK209)) != sK209
      & v2_funct_1(sK210)
      & r1_tarski(sK209,k1_relat_1(sK210))
      & v1_funct_1(sK210)
      & v1_relat_1(sK210) ) ),
    introduced(choice_axiom,[])).

fof(f2553,plain,
    ( k10_relat_1(sK210,k9_relat_1(sK210,sK209)) != sK209
    & v2_funct_1(sK210)
    & r1_tarski(sK209,k1_relat_1(sK210))
    & v1_funct_1(sK210)
    & v1_relat_1(sK210) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK209,sK210])],[f1883,f2552])).

fof(f4136,plain,(
    k10_relat_1(sK210,k9_relat_1(sK210,sK209)) != sK209 ),
    inference(cnf_transformation,[],[f2553])).

fof(f4135,plain,(
    v2_funct_1(sK210) ),
    inference(cnf_transformation,[],[f2553])).

fof(f4134,plain,(
    r1_tarski(sK209,k1_relat_1(sK210)) ),
    inference(cnf_transformation,[],[f2553])).

fof(f4133,plain,(
    v1_funct_1(sK210) ),
    inference(cnf_transformation,[],[f2553])).

fof(f4132,plain,(
    v1_relat_1(sK210) ),
    inference(cnf_transformation,[],[f2553])).

cnf(c_1483,plain,
    ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f4108])).

cnf(c_75378,plain,
    ( r1_tarski(sK209,k10_relat_1(sK210,k9_relat_1(sK210,sK209)))
    | ~ r1_tarski(sK209,k1_relat_1(sK210))
    | ~ v1_relat_1(sK210) ),
    inference(instantiation,[status(thm)],[c_1483])).

cnf(c_1490,plain,
    ( r1_tarski(k10_relat_1(X0,k9_relat_1(X0,X1)),X1)
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f4115])).

cnf(c_72334,plain,
    ( r1_tarski(k10_relat_1(sK210,k9_relat_1(sK210,sK209)),sK209)
    | ~ v2_funct_1(sK210)
    | ~ v1_funct_1(sK210)
    | ~ v1_relat_1(sK210) ),
    inference(instantiation,[status(thm)],[c_1490])).

cnf(c_67,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f2679])).

cnf(c_70971,plain,
    ( ~ r1_tarski(k10_relat_1(sK210,k9_relat_1(sK210,sK209)),sK209)
    | ~ r1_tarski(sK209,k10_relat_1(sK210,k9_relat_1(sK210,sK209)))
    | k10_relat_1(sK210,k9_relat_1(sK210,sK209)) = sK209 ),
    inference(instantiation,[status(thm)],[c_67])).

cnf(c_1507,negated_conjecture,
    ( k10_relat_1(sK210,k9_relat_1(sK210,sK209)) != sK209 ),
    inference(cnf_transformation,[],[f4136])).

cnf(c_1508,negated_conjecture,
    ( v2_funct_1(sK210) ),
    inference(cnf_transformation,[],[f4135])).

cnf(c_1509,negated_conjecture,
    ( r1_tarski(sK209,k1_relat_1(sK210)) ),
    inference(cnf_transformation,[],[f4134])).

cnf(c_1510,negated_conjecture,
    ( v1_funct_1(sK210) ),
    inference(cnf_transformation,[],[f4133])).

cnf(c_1511,negated_conjecture,
    ( v1_relat_1(sK210) ),
    inference(cnf_transformation,[],[f4132])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_75378,c_72334,c_70971,c_1507,c_1508,c_1509,c_1510,c_1511])).

%------------------------------------------------------------------------------
