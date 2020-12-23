%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0666+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:49 EST 2020

% Result     : Theorem 35.74s
% Output     : CNFRefutation 35.74s
% Verified   : 
% Statistics : Number of formulae       :   32 (  45 expanded)
%              Number of clauses        :   15 (  16 expanded)
%              Number of leaves         :    6 (  11 expanded)
%              Depth                    :    7
%              Number of atoms          :   97 ( 170 expanded)
%              Number of equality atoms :   47 (  78 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f708,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1479,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f708])).

fof(f1480,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1479])).

fof(f3554,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1480])).

fof(f707,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1477,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f707])).

fof(f1478,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1477])).

fof(f3553,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1478])).

fof(f969,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r1_tarski(X0,X1)
       => ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
          & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f970,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r1_tarski(X0,X1)
         => ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
            & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f969])).

fof(f1834,plain,(
    ? [X0,X1,X2] :
      ( ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
        | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1) )
      & r1_tarski(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f970])).

fof(f1835,plain,(
    ? [X0,X1,X2] :
      ( ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
        | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1) )
      & r1_tarski(X0,X1)
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f1834])).

fof(f2413,plain,
    ( ? [X0,X1,X2] :
        ( ( k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X1),X0)
          | k7_relat_1(X2,X0) != k7_relat_1(k7_relat_1(X2,X0),X1) )
        & r1_tarski(X0,X1)
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( k7_relat_1(sK210,sK208) != k7_relat_1(k7_relat_1(sK210,sK209),sK208)
        | k7_relat_1(sK210,sK208) != k7_relat_1(k7_relat_1(sK210,sK208),sK209) )
      & r1_tarski(sK208,sK209)
      & v1_funct_1(sK210)
      & v1_relat_1(sK210) ) ),
    introduced(choice_axiom,[])).

fof(f2414,plain,
    ( ( k7_relat_1(sK210,sK208) != k7_relat_1(k7_relat_1(sK210,sK209),sK208)
      | k7_relat_1(sK210,sK208) != k7_relat_1(k7_relat_1(sK210,sK208),sK209) )
    & r1_tarski(sK208,sK209)
    & v1_funct_1(sK210)
    & v1_relat_1(sK210) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK208,sK209,sK210])],[f1835,f2413])).

fof(f3991,plain,
    ( k7_relat_1(sK210,sK208) != k7_relat_1(k7_relat_1(sK210,sK209),sK208)
    | k7_relat_1(sK210,sK208) != k7_relat_1(k7_relat_1(sK210,sK208),sK209) ),
    inference(cnf_transformation,[],[f2414])).

fof(f3990,plain,(
    r1_tarski(sK208,sK209) ),
    inference(cnf_transformation,[],[f2414])).

fof(f3988,plain,(
    v1_relat_1(sK210) ),
    inference(cnf_transformation,[],[f2414])).

cnf(c_1121,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f3554])).

cnf(c_149769,plain,
    ( ~ r1_tarski(sK208,sK209)
    | ~ v1_relat_1(sK210)
    | k7_relat_1(k7_relat_1(sK210,sK209),sK208) = k7_relat_1(sK210,sK208) ),
    inference(instantiation,[status(thm)],[c_1121])).

cnf(c_1120,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,X0) ),
    inference(cnf_transformation,[],[f3553])).

cnf(c_148746,plain,
    ( ~ r1_tarski(sK208,sK209)
    | ~ v1_relat_1(sK210)
    | k7_relat_1(k7_relat_1(sK210,sK208),sK209) = k7_relat_1(sK210,sK208) ),
    inference(instantiation,[status(thm)],[c_1120])).

cnf(c_41715,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_86867,plain,
    ( k7_relat_1(k7_relat_1(sK210,sK208),sK209) != X0
    | k7_relat_1(sK210,sK208) != X0
    | k7_relat_1(sK210,sK208) = k7_relat_1(k7_relat_1(sK210,sK208),sK209) ),
    inference(instantiation,[status(thm)],[c_41715])).

cnf(c_148745,plain,
    ( k7_relat_1(k7_relat_1(sK210,sK208),sK209) != k7_relat_1(sK210,sK208)
    | k7_relat_1(sK210,sK208) = k7_relat_1(k7_relat_1(sK210,sK208),sK209)
    | k7_relat_1(sK210,sK208) != k7_relat_1(sK210,sK208) ),
    inference(instantiation,[status(thm)],[c_86867])).

cnf(c_41714,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_110321,plain,
    ( k7_relat_1(sK210,sK208) = k7_relat_1(sK210,sK208) ),
    inference(instantiation,[status(thm)],[c_41714])).

cnf(c_78792,plain,
    ( k7_relat_1(k7_relat_1(sK210,sK209),sK208) != X0
    | k7_relat_1(sK210,sK208) != X0
    | k7_relat_1(sK210,sK208) = k7_relat_1(k7_relat_1(sK210,sK209),sK208) ),
    inference(instantiation,[status(thm)],[c_41715])).

cnf(c_110320,plain,
    ( k7_relat_1(k7_relat_1(sK210,sK209),sK208) != k7_relat_1(sK210,sK208)
    | k7_relat_1(sK210,sK208) = k7_relat_1(k7_relat_1(sK210,sK209),sK208)
    | k7_relat_1(sK210,sK208) != k7_relat_1(sK210,sK208) ),
    inference(instantiation,[status(thm)],[c_78792])).

cnf(c_1555,negated_conjecture,
    ( k7_relat_1(sK210,sK208) != k7_relat_1(k7_relat_1(sK210,sK209),sK208)
    | k7_relat_1(sK210,sK208) != k7_relat_1(k7_relat_1(sK210,sK208),sK209) ),
    inference(cnf_transformation,[],[f3991])).

cnf(c_1556,negated_conjecture,
    ( r1_tarski(sK208,sK209) ),
    inference(cnf_transformation,[],[f3990])).

cnf(c_1558,negated_conjecture,
    ( v1_relat_1(sK210) ),
    inference(cnf_transformation,[],[f3988])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_149769,c_148746,c_148745,c_110321,c_110320,c_1555,c_1556,c_1558])).

%------------------------------------------------------------------------------
