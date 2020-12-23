%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0670+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:49 EST 2020

% Result     : Theorem 30.85s
% Output     : CNFRefutation 30.85s
% Verified   : 
% Statistics : Number of formulae       :   49 (  72 expanded)
%              Number of clauses        :   15 (  15 expanded)
%              Number of leaves         :    7 (  14 expanded)
%              Depth                    :   10
%              Number of atoms          :  233 ( 348 expanded)
%              Number of equality atoms :   31 (  59 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f646,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1428,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f646])).

fof(f2250,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1428])).

fof(f2251,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X3,X4] :
                  ( ( r2_hidden(k4_tarski(X3,X4),X2)
                    | ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f2250])).

fof(f2252,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ? [X3,X4] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
                    | ~ r2_hidden(X4,X0)
                    | ~ r2_hidden(k4_tarski(X3,X4),X2) )
                  & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                      & r2_hidden(X4,X0) )
                    | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f2251])).

fof(f2253,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X1)
              & r2_hidden(X4,X0) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK136(X0,X1,X2),sK137(X0,X1,X2)),X1)
          | ~ r2_hidden(sK137(X0,X1,X2),X0)
          | ~ r2_hidden(k4_tarski(sK136(X0,X1,X2),sK137(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK136(X0,X1,X2),sK137(X0,X1,X2)),X1)
            & r2_hidden(sK137(X0,X1,X2),X0) )
          | r2_hidden(k4_tarski(sK136(X0,X1,X2),sK137(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2254,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( k8_relat_1(X0,X1) = X2
              | ( ( ~ r2_hidden(k4_tarski(sK136(X0,X1,X2),sK137(X0,X1,X2)),X1)
                  | ~ r2_hidden(sK137(X0,X1,X2),X0)
                  | ~ r2_hidden(k4_tarski(sK136(X0,X1,X2),sK137(X0,X1,X2)),X2) )
                & ( ( r2_hidden(k4_tarski(sK136(X0,X1,X2),sK137(X0,X1,X2)),X1)
                    & r2_hidden(sK137(X0,X1,X2),X0) )
                  | r2_hidden(k4_tarski(sK136(X0,X1,X2),sK137(X0,X1,X2)),X2) ) ) )
            & ( ! [X5,X6] :
                  ( ( r2_hidden(k4_tarski(X5,X6),X2)
                    | ~ r2_hidden(k4_tarski(X5,X6),X1)
                    | ~ r2_hidden(X6,X0) )
                  & ( ( r2_hidden(k4_tarski(X5,X6),X1)
                      & r2_hidden(X6,X0) )
                    | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
              | k8_relat_1(X0,X1) != X2 ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK136,sK137])],[f2252,f2253])).

fof(f3474,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X2)
      | k8_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2254])).

fof(f4841,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,X6),X1)
      | ~ r2_hidden(k4_tarski(X5,X6),k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f3474])).

fof(f909,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1741,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f909])).

fof(f1742,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1741])).

fof(f3848,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k8_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1742])).

fof(f670,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1445,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f670])).

fof(f3531,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1445])).

fof(f976,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f1852,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f976])).

fof(f1853,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1852])).

fof(f2443,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f1853])).

fof(f2444,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f2443])).

fof(f4042,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2444])).

fof(f4043,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2444])).

fof(f4895,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f4043])).

fof(f974,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
       => k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f975,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
         => k1_funct_1(X2,X0) = k1_funct_1(k8_relat_1(X1,X2),X0) ) ) ),
    inference(negated_conjecture,[],[f974])).

fof(f1850,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k8_relat_1(X1,X2),X0)
      & r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f975])).

fof(f1851,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(X2,X0) != k1_funct_1(k8_relat_1(X1,X2),X0)
      & r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f1850])).

fof(f2441,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(X2,X0) != k1_funct_1(k8_relat_1(X1,X2),X0)
        & r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(sK214,sK212) != k1_funct_1(k8_relat_1(sK213,sK214),sK212)
      & r2_hidden(sK212,k1_relat_1(k8_relat_1(sK213,sK214)))
      & v1_funct_1(sK214)
      & v1_relat_1(sK214) ) ),
    introduced(choice_axiom,[])).

fof(f2442,plain,
    ( k1_funct_1(sK214,sK212) != k1_funct_1(k8_relat_1(sK213,sK214),sK212)
    & r2_hidden(sK212,k1_relat_1(k8_relat_1(sK213,sK214)))
    & v1_funct_1(sK214)
    & v1_relat_1(sK214) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK212,sK213,sK214])],[f1851,f2441])).

fof(f4040,plain,(
    k1_funct_1(sK214,sK212) != k1_funct_1(k8_relat_1(sK213,sK214),sK212) ),
    inference(cnf_transformation,[],[f2442])).

fof(f4039,plain,(
    r2_hidden(sK212,k1_relat_1(k8_relat_1(sK213,sK214))) ),
    inference(cnf_transformation,[],[f2442])).

fof(f4038,plain,(
    v1_funct_1(sK214) ),
    inference(cnf_transformation,[],[f2442])).

fof(f4037,plain,(
    v1_relat_1(sK214) ),
    inference(cnf_transformation,[],[f2442])).

cnf(c_1016,plain,
    ( r2_hidden(k4_tarski(X0,X1),X2)
    | ~ r2_hidden(k4_tarski(X0,X1),k8_relat_1(X3,X2))
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(k8_relat_1(X3,X2)) ),
    inference(cnf_transformation,[],[f4841])).

cnf(c_128196,plain,
    ( ~ r2_hidden(k4_tarski(sK212,k1_funct_1(k8_relat_1(sK213,sK214),sK212)),k8_relat_1(sK213,sK214))
    | r2_hidden(k4_tarski(sK212,k1_funct_1(k8_relat_1(sK213,sK214),sK212)),sK214)
    | ~ v1_relat_1(k8_relat_1(sK213,sK214))
    | ~ v1_relat_1(sK214) ),
    inference(instantiation,[status(thm)],[c_1016])).

cnf(c_1386,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k8_relat_1(X1,X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f3848])).

cnf(c_93486,plain,
    ( v1_funct_1(k8_relat_1(sK213,sK214))
    | ~ v1_funct_1(sK214)
    | ~ v1_relat_1(sK214) ),
    inference(instantiation,[status(thm)],[c_1386])).

cnf(c_1070,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k8_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f3531])).

cnf(c_92719,plain,
    ( v1_relat_1(k8_relat_1(sK213,sK214))
    | ~ v1_relat_1(sK214) ),
    inference(instantiation,[status(thm)],[c_1070])).

cnf(c_1581,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f4042])).

cnf(c_86682,plain,
    ( ~ r2_hidden(k4_tarski(sK212,k1_funct_1(k8_relat_1(sK213,sK214),sK212)),sK214)
    | ~ v1_funct_1(sK214)
    | ~ v1_relat_1(sK214)
    | k1_funct_1(sK214,sK212) = k1_funct_1(k8_relat_1(sK213,sK214),sK212) ),
    inference(instantiation,[status(thm)],[c_1581])).

cnf(c_1580,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f4895])).

cnf(c_86679,plain,
    ( r2_hidden(k4_tarski(sK212,k1_funct_1(k8_relat_1(sK213,sK214),sK212)),k8_relat_1(sK213,sK214))
    | ~ r2_hidden(sK212,k1_relat_1(k8_relat_1(sK213,sK214)))
    | ~ v1_funct_1(k8_relat_1(sK213,sK214))
    | ~ v1_relat_1(k8_relat_1(sK213,sK214)) ),
    inference(instantiation,[status(thm)],[c_1580])).

cnf(c_1576,negated_conjecture,
    ( k1_funct_1(sK214,sK212) != k1_funct_1(k8_relat_1(sK213,sK214),sK212) ),
    inference(cnf_transformation,[],[f4040])).

cnf(c_1577,negated_conjecture,
    ( r2_hidden(sK212,k1_relat_1(k8_relat_1(sK213,sK214))) ),
    inference(cnf_transformation,[],[f4039])).

cnf(c_1578,negated_conjecture,
    ( v1_funct_1(sK214) ),
    inference(cnf_transformation,[],[f4038])).

cnf(c_1579,negated_conjecture,
    ( v1_relat_1(sK214) ),
    inference(cnf_transformation,[],[f4037])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_128196,c_93486,c_92719,c_86682,c_86679,c_1576,c_1577,c_1578,c_1579])).

%------------------------------------------------------------------------------
