%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0618+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:48 EST 2020

% Result     : Theorem 18.39s
% Output     : CNFRefutation 18.39s
% Verified   : 
% Statistics : Number of formulae       :   29 (  47 expanded)
%              Number of clauses        :    7 (   7 expanded)
%              Number of leaves         :    6 (  12 expanded)
%              Depth                    :   11
%              Number of atoms          :  146 ( 230 expanded)
%              Number of equality atoms :   35 (  35 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f891,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1634,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f891])).

fof(f1635,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1634])).

fof(f2122,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1635])).

fof(f2123,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f2122])).

fof(f2126,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK169(X0,X5)) = X5
        & r2_hidden(sK169(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2125,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK168(X0,X1)) = X2
        & r2_hidden(sK168(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2124,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK167(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK167(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK167(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK167(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2127,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK167(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK167(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK168(X0,X1)) = sK167(X0,X1)
                  & r2_hidden(sK168(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK167(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK169(X0,X5)) = X5
                    & r2_hidden(sK169(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK167,sK168,sK169])],[f2123,f2126,f2125,f2124])).

fof(f3494,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2127])).

fof(f4294,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f3494])).

fof(f4295,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f4294])).

fof(f894,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f895,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r2_hidden(X0,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f894])).

fof(f1636,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f895])).

fof(f1637,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1636])).

fof(f2130,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
        & r2_hidden(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ~ r2_hidden(k1_funct_1(sK172,sK171),k2_relat_1(sK172))
      & r2_hidden(sK171,k1_relat_1(sK172))
      & v1_funct_1(sK172)
      & v1_relat_1(sK172) ) ),
    introduced(choice_axiom,[])).

fof(f2131,plain,
    ( ~ r2_hidden(k1_funct_1(sK172,sK171),k2_relat_1(sK172))
    & r2_hidden(sK171,k1_relat_1(sK172))
    & v1_funct_1(sK172)
    & v1_relat_1(sK172) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK171,sK172])],[f1637,f2130])).

fof(f3503,plain,(
    ~ r2_hidden(k1_funct_1(sK172,sK171),k2_relat_1(sK172)) ),
    inference(cnf_transformation,[],[f2131])).

fof(f3502,plain,(
    r2_hidden(sK171,k1_relat_1(sK172)) ),
    inference(cnf_transformation,[],[f2131])).

fof(f3501,plain,(
    v1_funct_1(sK172) ),
    inference(cnf_transformation,[],[f2131])).

fof(f3500,plain,(
    v1_relat_1(sK172) ),
    inference(cnf_transformation,[],[f2131])).

cnf(c_1345,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f4295])).

cnf(c_67769,plain,
    ( r2_hidden(k1_funct_1(sK172,sK171),k2_relat_1(sK172))
    | ~ r2_hidden(sK171,k1_relat_1(sK172))
    | ~ v1_funct_1(sK172)
    | ~ v1_relat_1(sK172) ),
    inference(instantiation,[status(thm)],[c_1345])).

cnf(c_1350,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK172,sK171),k2_relat_1(sK172)) ),
    inference(cnf_transformation,[],[f3503])).

cnf(c_1351,negated_conjecture,
    ( r2_hidden(sK171,k1_relat_1(sK172)) ),
    inference(cnf_transformation,[],[f3502])).

cnf(c_1352,negated_conjecture,
    ( v1_funct_1(sK172) ),
    inference(cnf_transformation,[],[f3501])).

cnf(c_1353,negated_conjecture,
    ( v1_relat_1(sK172) ),
    inference(cnf_transformation,[],[f3500])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_67769,c_1350,c_1351,c_1352,c_1353])).

%------------------------------------------------------------------------------
