%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0713+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:50 EST 2020

% Result     : Theorem 39.54s
% Output     : CNFRefutation 39.54s
% Verified   : 
% Statistics : Number of formulae       :   48 (  66 expanded)
%              Number of clauses        :   15 (  15 expanded)
%              Number of leaves         :    8 (  14 expanded)
%              Depth                    :    9
%              Number of atoms          :  170 ( 254 expanded)
%              Number of equality atoms :   44 (  65 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1022,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X0,X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
       => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1987,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1022])).

fof(f1988,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1987])).

fof(f4291,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1988])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2102,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f175])).

fof(f2103,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f2102])).

fof(f2104,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK33(X0,X1) != X0
          | ~ r2_hidden(sK33(X0,X1),X1) )
        & ( sK33(X0,X1) = X0
          | r2_hidden(sK33(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2105,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK33(X0,X1) != X0
            | ~ r2_hidden(sK33(X0,X1),X1) )
          & ( sK33(X0,X1) = X0
            | r2_hidden(sK33(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK33])],[f2103,f2104])).

fof(f2873,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2105])).

fof(f4982,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f2873])).

fof(f4983,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f4982])).

fof(f975,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1902,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f975])).

fof(f1903,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1902])).

fof(f4175,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1903])).

fof(f395,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2202,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f395])).

fof(f3207,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f2202])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f2082,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f2083,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f2082])).

fof(f2709,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2083])).

fof(f976,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f977,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r2_hidden(X0,k1_relat_1(X1))
         => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(k7_relat_1(X1,k1_tarski(X0))) ) ) ),
    inference(negated_conjecture,[],[f976])).

fof(f1904,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f977])).

fof(f1905,plain,(
    ? [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1904])).

fof(f2582,plain,
    ( ? [X0,X1] :
        ( k1_tarski(k1_funct_1(X1,X0)) != k2_relat_1(k7_relat_1(X1,k1_tarski(X0)))
        & r2_hidden(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k1_tarski(k1_funct_1(sK213,sK212)) != k2_relat_1(k7_relat_1(sK213,k1_tarski(sK212)))
      & r2_hidden(sK212,k1_relat_1(sK213))
      & v1_funct_1(sK213)
      & v1_relat_1(sK213) ) ),
    introduced(choice_axiom,[])).

fof(f2583,plain,
    ( k1_tarski(k1_funct_1(sK213,sK212)) != k2_relat_1(k7_relat_1(sK213,k1_tarski(sK212)))
    & r2_hidden(sK212,k1_relat_1(sK213))
    & v1_funct_1(sK213)
    & v1_relat_1(sK213) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK212,sK213])],[f1905,f2582])).

fof(f4179,plain,(
    k1_tarski(k1_funct_1(sK213,sK212)) != k2_relat_1(k7_relat_1(sK213,k1_tarski(sK212))) ),
    inference(cnf_transformation,[],[f2583])).

fof(f4178,plain,(
    r2_hidden(sK212,k1_relat_1(sK213)) ),
    inference(cnf_transformation,[],[f2583])).

fof(f4177,plain,(
    v1_funct_1(sK213) ),
    inference(cnf_transformation,[],[f2583])).

fof(f4176,plain,(
    v1_relat_1(sK213) ),
    inference(cnf_transformation,[],[f2583])).

cnf(c_1636,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f4291])).

cnf(c_103724,plain,
    ( r2_hidden(k1_funct_1(sK213,sK212),k2_relat_1(k7_relat_1(sK213,k1_tarski(sK212))))
    | ~ r2_hidden(sK212,k1_relat_1(sK213))
    | ~ r2_hidden(sK212,k1_tarski(sK212))
    | ~ v1_funct_1(sK213)
    | ~ v1_relat_1(sK213) ),
    inference(instantiation,[status(thm)],[c_1636])).

cnf(c_231,plain,
    ( r2_hidden(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4983])).

cnf(c_93127,plain,
    ( r2_hidden(sK212,k1_tarski(sK212)) ),
    inference(instantiation,[status(thm)],[c_231])).

cnf(c_1520,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0,k1_tarski(X1))),k1_tarski(k1_funct_1(X0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f4175])).

cnf(c_76341,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK213,k1_tarski(sK212))),k1_tarski(k1_funct_1(sK213,sK212)))
    | ~ v1_funct_1(sK213)
    | ~ v1_relat_1(sK213) ),
    inference(instantiation,[status(thm)],[c_1520])).

cnf(c_553,plain,
    ( r1_tarski(k1_tarski(X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f3207])).

cnf(c_73052,plain,
    ( r1_tarski(k1_tarski(k1_funct_1(sK213,sK212)),k2_relat_1(k7_relat_1(sK213,k1_tarski(sK212))))
    | ~ r2_hidden(k1_funct_1(sK213,sK212),k2_relat_1(k7_relat_1(sK213,k1_tarski(sK212)))) ),
    inference(instantiation,[status(thm)],[c_553])).

cnf(c_67,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f2709])).

cnf(c_71687,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK213,k1_tarski(sK212))),k1_tarski(k1_funct_1(sK213,sK212)))
    | ~ r1_tarski(k1_tarski(k1_funct_1(sK213,sK212)),k2_relat_1(k7_relat_1(sK213,k1_tarski(sK212))))
    | k1_tarski(k1_funct_1(sK213,sK212)) = k2_relat_1(k7_relat_1(sK213,k1_tarski(sK212))) ),
    inference(instantiation,[status(thm)],[c_67])).

cnf(c_1521,negated_conjecture,
    ( k1_tarski(k1_funct_1(sK213,sK212)) != k2_relat_1(k7_relat_1(sK213,k1_tarski(sK212))) ),
    inference(cnf_transformation,[],[f4179])).

cnf(c_1522,negated_conjecture,
    ( r2_hidden(sK212,k1_relat_1(sK213)) ),
    inference(cnf_transformation,[],[f4178])).

cnf(c_1523,negated_conjecture,
    ( v1_funct_1(sK213) ),
    inference(cnf_transformation,[],[f4177])).

cnf(c_1524,negated_conjecture,
    ( v1_relat_1(sK213) ),
    inference(cnf_transformation,[],[f4176])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_103724,c_93127,c_76341,c_73052,c_71687,c_1521,c_1522,c_1523,c_1524])).

%------------------------------------------------------------------------------
