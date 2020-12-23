%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0669+2 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 39.41s
% Output     : CNFRefutation 39.41s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 429 expanded)
%              Number of clauses        :   44 ( 120 expanded)
%              Number of leaves         :   10 (  84 expanded)
%              Depth                    :   18
%              Number of atoms          :  407 (2478 expanded)
%              Number of equality atoms :   90 ( 265 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f972,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) )
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X3),X0)
                    & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f991,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X1,X3) = k1_funct_1(X2,X3) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) ) ) ) ),
    inference(rectify,[],[f972])).

fof(f1845,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f991])).

fof(f1846,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1845])).

fof(f1879,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relat_1(X0,X2) = X1
      <=> sP15(X2,X1,X0) )
      | ~ sP16(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP16])])).

fof(f1878,plain,(
    ! [X2,X1,X0] :
      ( sP15(X2,X1,X0)
    <=> ( ! [X3] :
            ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
            | ~ r2_hidden(X3,k1_relat_1(X1)) )
        & ! [X4] :
            ( r2_hidden(X4,k1_relat_1(X1))
          <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
              & r2_hidden(X4,k1_relat_1(X2)) ) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP15])])).

fof(f1880,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( sP16(X0,X1,X2)
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f1846,f1879,f1878])).

fof(f4030,plain,(
    ! [X2,X0,X1] :
      ( sP16(X0,X1,X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1880])).

fof(f2429,plain,(
    ! [X0,X1,X2] :
      ( ( ( k8_relat_1(X0,X2) = X1
          | ~ sP15(X2,X1,X0) )
        & ( sP15(X2,X1,X0)
          | k8_relat_1(X0,X2) != X1 ) )
      | ~ sP16(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f1879])).

fof(f4018,plain,(
    ! [X2,X0,X1] :
      ( sP15(X2,X1,X0)
      | k8_relat_1(X0,X2) != X1
      | ~ sP16(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2429])).

fof(f4889,plain,(
    ! [X2,X0] :
      ( sP15(X2,k8_relat_1(X0,X2),X0)
      | ~ sP16(X0,k8_relat_1(X0,X2),X2) ) ),
    inference(equality_resolution,[],[f4018])).

fof(f909,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1740,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f909])).

fof(f1741,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1740])).

fof(f3845,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k8_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1741])).

fof(f670,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1444,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f670])).

fof(f3528,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1444])).

fof(f973,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f974,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
        <=> ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f973])).

fof(f1847,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <~> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f974])).

fof(f1848,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      <~> ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f1847])).

fof(f2436,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) )
      & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
        | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f1848])).

fof(f2437,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) )
      & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
        | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) )
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f2436])).

fof(f2438,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) )
        & ( ( r2_hidden(k1_funct_1(X2,X0),X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
          | r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) )
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ( ~ r2_hidden(k1_funct_1(sK214,sK212),sK213)
        | ~ r2_hidden(sK212,k1_relat_1(sK214))
        | ~ r2_hidden(sK212,k1_relat_1(k8_relat_1(sK213,sK214))) )
      & ( ( r2_hidden(k1_funct_1(sK214,sK212),sK213)
          & r2_hidden(sK212,k1_relat_1(sK214)) )
        | r2_hidden(sK212,k1_relat_1(k8_relat_1(sK213,sK214))) )
      & v1_funct_1(sK214)
      & v1_relat_1(sK214) ) ),
    introduced(choice_axiom,[])).

fof(f2439,plain,
    ( ( ~ r2_hidden(k1_funct_1(sK214,sK212),sK213)
      | ~ r2_hidden(sK212,k1_relat_1(sK214))
      | ~ r2_hidden(sK212,k1_relat_1(k8_relat_1(sK213,sK214))) )
    & ( ( r2_hidden(k1_funct_1(sK214,sK212),sK213)
        & r2_hidden(sK212,k1_relat_1(sK214)) )
      | r2_hidden(sK212,k1_relat_1(k8_relat_1(sK213,sK214))) )
    & v1_funct_1(sK214)
    & v1_relat_1(sK214) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK212,sK213,sK214])],[f2437,f2438])).

fof(f4034,plain,
    ( r2_hidden(k1_funct_1(sK214,sK212),sK213)
    | r2_hidden(sK212,k1_relat_1(k8_relat_1(sK213,sK214))) ),
    inference(cnf_transformation,[],[f2439])).

fof(f953,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1809,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f953])).

fof(f1810,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1809])).

fof(f3989,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1810])).

fof(f4031,plain,(
    v1_relat_1(sK214) ),
    inference(cnf_transformation,[],[f2439])).

fof(f4032,plain,(
    v1_funct_1(sK214) ),
    inference(cnf_transformation,[],[f2439])).

fof(f2430,plain,(
    ! [X2,X1,X0] :
      ( ( sP15(X2,X1,X0)
        | ? [X3] :
            ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
            & r2_hidden(X3,k1_relat_1(X1)) )
        | ? [X4] :
            ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
              | ~ r2_hidden(X4,k1_relat_1(X2))
              | ~ r2_hidden(X4,k1_relat_1(X1)) )
            & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                & r2_hidden(X4,k1_relat_1(X2)) )
              | r2_hidden(X4,k1_relat_1(X1)) ) ) )
      & ( ( ! [X3] :
              ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
              | ~ r2_hidden(X3,k1_relat_1(X1)) )
          & ! [X4] :
              ( ( r2_hidden(X4,k1_relat_1(X1))
                | ~ r2_hidden(k1_funct_1(X2,X4),X0)
                | ~ r2_hidden(X4,k1_relat_1(X2)) )
              & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                  & r2_hidden(X4,k1_relat_1(X2)) )
                | ~ r2_hidden(X4,k1_relat_1(X1)) ) ) )
        | ~ sP15(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f1878])).

fof(f2431,plain,(
    ! [X2,X1,X0] :
      ( ( sP15(X2,X1,X0)
        | ? [X3] :
            ( k1_funct_1(X1,X3) != k1_funct_1(X2,X3)
            & r2_hidden(X3,k1_relat_1(X1)) )
        | ? [X4] :
            ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
              | ~ r2_hidden(X4,k1_relat_1(X2))
              | ~ r2_hidden(X4,k1_relat_1(X1)) )
            & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                & r2_hidden(X4,k1_relat_1(X2)) )
              | r2_hidden(X4,k1_relat_1(X1)) ) ) )
      & ( ( ! [X3] :
              ( k1_funct_1(X1,X3) = k1_funct_1(X2,X3)
              | ~ r2_hidden(X3,k1_relat_1(X1)) )
          & ! [X4] :
              ( ( r2_hidden(X4,k1_relat_1(X1))
                | ~ r2_hidden(k1_funct_1(X2,X4),X0)
                | ~ r2_hidden(X4,k1_relat_1(X2)) )
              & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                  & r2_hidden(X4,k1_relat_1(X2)) )
                | ~ r2_hidden(X4,k1_relat_1(X1)) ) ) )
        | ~ sP15(X2,X1,X0) ) ) ),
    inference(flattening,[],[f2430])).

fof(f2432,plain,(
    ! [X0,X1,X2] :
      ( ( sP15(X0,X1,X2)
        | ? [X3] :
            ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
            & r2_hidden(X3,k1_relat_1(X1)) )
        | ? [X4] :
            ( ( ~ r2_hidden(k1_funct_1(X0,X4),X2)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X4,k1_relat_1(X1)) )
            & ( ( r2_hidden(k1_funct_1(X0,X4),X2)
                & r2_hidden(X4,k1_relat_1(X0)) )
              | r2_hidden(X4,k1_relat_1(X1)) ) ) )
      & ( ( ! [X5] :
              ( k1_funct_1(X0,X5) = k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,k1_relat_1(X1)) )
          & ! [X6] :
              ( ( r2_hidden(X6,k1_relat_1(X1))
                | ~ r2_hidden(k1_funct_1(X0,X6),X2)
                | ~ r2_hidden(X6,k1_relat_1(X0)) )
              & ( ( r2_hidden(k1_funct_1(X0,X6),X2)
                  & r2_hidden(X6,k1_relat_1(X0)) )
                | ~ r2_hidden(X6,k1_relat_1(X1)) ) ) )
        | ~ sP15(X0,X1,X2) ) ) ),
    inference(rectify,[],[f2431])).

fof(f2434,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ r2_hidden(k1_funct_1(X0,X4),X2)
            | ~ r2_hidden(X4,k1_relat_1(X0))
            | ~ r2_hidden(X4,k1_relat_1(X1)) )
          & ( ( r2_hidden(k1_funct_1(X0,X4),X2)
              & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X4,k1_relat_1(X1)) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X0,sK211(X0,X1,X2)),X2)
          | ~ r2_hidden(sK211(X0,X1,X2),k1_relat_1(X0))
          | ~ r2_hidden(sK211(X0,X1,X2),k1_relat_1(X1)) )
        & ( ( r2_hidden(k1_funct_1(X0,sK211(X0,X1,X2)),X2)
            & r2_hidden(sK211(X0,X1,X2),k1_relat_1(X0)) )
          | r2_hidden(sK211(X0,X1,X2),k1_relat_1(X1)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2433,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X0,X3) != k1_funct_1(X1,X3)
          & r2_hidden(X3,k1_relat_1(X1)) )
     => ( k1_funct_1(X0,sK210(X0,X1)) != k1_funct_1(X1,sK210(X0,X1))
        & r2_hidden(sK210(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2435,plain,(
    ! [X0,X1,X2] :
      ( ( sP15(X0,X1,X2)
        | ( k1_funct_1(X0,sK210(X0,X1)) != k1_funct_1(X1,sK210(X0,X1))
          & r2_hidden(sK210(X0,X1),k1_relat_1(X1)) )
        | ( ( ~ r2_hidden(k1_funct_1(X0,sK211(X0,X1,X2)),X2)
            | ~ r2_hidden(sK211(X0,X1,X2),k1_relat_1(X0))
            | ~ r2_hidden(sK211(X0,X1,X2),k1_relat_1(X1)) )
          & ( ( r2_hidden(k1_funct_1(X0,sK211(X0,X1,X2)),X2)
              & r2_hidden(sK211(X0,X1,X2),k1_relat_1(X0)) )
            | r2_hidden(sK211(X0,X1,X2),k1_relat_1(X1)) ) ) )
      & ( ( ! [X5] :
              ( k1_funct_1(X0,X5) = k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,k1_relat_1(X1)) )
          & ! [X6] :
              ( ( r2_hidden(X6,k1_relat_1(X1))
                | ~ r2_hidden(k1_funct_1(X0,X6),X2)
                | ~ r2_hidden(X6,k1_relat_1(X0)) )
              & ( ( r2_hidden(k1_funct_1(X0,X6),X2)
                  & r2_hidden(X6,k1_relat_1(X0)) )
                | ~ r2_hidden(X6,k1_relat_1(X1)) ) ) )
        | ~ sP15(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK210,sK211])],[f2432,f2434,f2433])).

fof(f4021,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X2)
      | ~ r2_hidden(X6,k1_relat_1(X1))
      | ~ sP15(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2435])).

fof(f4022,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,k1_relat_1(X1))
      | ~ r2_hidden(k1_funct_1(X0,X6),X2)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ sP15(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2435])).

fof(f4033,plain,
    ( r2_hidden(sK212,k1_relat_1(sK214))
    | r2_hidden(sK212,k1_relat_1(k8_relat_1(sK213,sK214))) ),
    inference(cnf_transformation,[],[f2439])).

fof(f4020,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(X6,k1_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X1))
      | ~ sP15(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2435])).

fof(f4035,plain,
    ( ~ r2_hidden(k1_funct_1(sK214,sK212),sK213)
    | ~ r2_hidden(sK212,k1_relat_1(sK214))
    | ~ r2_hidden(sK212,k1_relat_1(k8_relat_1(sK213,sK214))) ),
    inference(cnf_transformation,[],[f2439])).

cnf(c_1572,plain,
    ( sP16(X0,X1,X2)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f4030])).

cnf(c_1561,plain,
    ( ~ sP16(X0,k8_relat_1(X0,X1),X1)
    | sP15(X1,k8_relat_1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4889])).

cnf(c_16678,plain,
    ( sP15(X0,k8_relat_1(X1,X0),X1)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X2)
    | ~ v1_relat_1(X3)
    | X1 != X4
    | X0 != X3
    | k8_relat_1(X1,X0) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_1572,c_1561])).

cnf(c_16679,plain,
    ( sP15(X0,k8_relat_1(X1,X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k8_relat_1(X1,X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(k8_relat_1(X1,X0)) ),
    inference(unflattening,[status(thm)],[c_16678])).

cnf(c_1386,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k8_relat_1(X1,X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f3845])).

cnf(c_1070,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k8_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f3528])).

cnf(c_16683,plain,
    ( ~ v1_relat_1(X0)
    | sP15(X0,k8_relat_1(X1,X0),X1)
    | ~ v1_funct_1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16679,c_1386,c_1070])).

cnf(c_16684,plain,
    ( sP15(X0,k8_relat_1(X1,X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(renaming,[status(thm)],[c_16683])).

cnf(c_67926,plain,
    ( sP15(X0,k8_relat_1(X1,X0),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16684])).

cnf(c_1574,negated_conjecture,
    ( r2_hidden(k1_funct_1(sK214,sK212),sK213)
    | r2_hidden(sK212,k1_relat_1(k8_relat_1(sK213,sK214))) ),
    inference(cnf_transformation,[],[f4034])).

cnf(c_67991,plain,
    ( r2_hidden(k1_funct_1(sK214,sK212),sK213) = iProver_top
    | r2_hidden(sK212,k1_relat_1(k8_relat_1(sK213,sK214))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1574])).

cnf(c_1532,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f3989])).

cnf(c_68025,plain,
    ( k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X1)) = X1
    | r2_hidden(X1,k1_relat_1(X0)) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1532])).

cnf(c_136757,plain,
    ( k1_funct_1(k2_funct_1(k8_relat_1(sK213,sK214)),k1_funct_1(k8_relat_1(sK213,sK214),sK212)) = sK212
    | r2_hidden(k1_funct_1(sK214,sK212),sK213) = iProver_top
    | v2_funct_1(k8_relat_1(sK213,sK214)) != iProver_top
    | v1_funct_1(k8_relat_1(sK213,sK214)) != iProver_top
    | v1_relat_1(k8_relat_1(sK213,sK214)) != iProver_top ),
    inference(superposition,[status(thm)],[c_67991,c_68025])).

cnf(c_1577,negated_conjecture,
    ( v1_relat_1(sK214) ),
    inference(cnf_transformation,[],[f4031])).

cnf(c_1583,plain,
    ( v1_relat_1(sK214) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1577])).

cnf(c_1576,negated_conjecture,
    ( v1_funct_1(sK214) ),
    inference(cnf_transformation,[],[f4032])).

cnf(c_1584,plain,
    ( v1_funct_1(sK214) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1576])).

cnf(c_1586,plain,
    ( r2_hidden(k1_funct_1(sK214,sK212),sK213) = iProver_top
    | r2_hidden(sK212,k1_relat_1(k8_relat_1(sK213,sK214))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1574])).

cnf(c_131842,plain,
    ( sP15(sK214,k8_relat_1(sK213,sK214),sK213)
    | ~ v1_funct_1(sK214)
    | ~ v1_relat_1(sK214) ),
    inference(instantiation,[status(thm)],[c_16684])).

cnf(c_131845,plain,
    ( sP15(sK214,k8_relat_1(sK213,sK214),sK213) = iProver_top
    | v1_funct_1(sK214) != iProver_top
    | v1_relat_1(sK214) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_131842])).

cnf(c_1570,plain,
    ( ~ sP15(X0,X1,X2)
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X0,X3),X2) ),
    inference(cnf_transformation,[],[f4021])).

cnf(c_85375,plain,
    ( ~ sP15(X0,k8_relat_1(sK213,sK214),X1)
    | r2_hidden(k1_funct_1(X0,sK212),X1)
    | ~ r2_hidden(sK212,k1_relat_1(k8_relat_1(sK213,sK214))) ),
    inference(instantiation,[status(thm)],[c_1570])).

cnf(c_134591,plain,
    ( ~ sP15(sK214,k8_relat_1(sK213,sK214),sK213)
    | r2_hidden(k1_funct_1(sK214,sK212),sK213)
    | ~ r2_hidden(sK212,k1_relat_1(k8_relat_1(sK213,sK214))) ),
    inference(instantiation,[status(thm)],[c_85375])).

cnf(c_134592,plain,
    ( sP15(sK214,k8_relat_1(sK213,sK214),sK213) != iProver_top
    | r2_hidden(k1_funct_1(sK214,sK212),sK213) = iProver_top
    | r2_hidden(sK212,k1_relat_1(k8_relat_1(sK213,sK214))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_134591])).

cnf(c_139248,plain,
    ( r2_hidden(k1_funct_1(sK214,sK212),sK213) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_136757,c_1583,c_1584,c_1586,c_131845,c_134592])).

cnf(c_1569,plain,
    ( ~ sP15(X0,X1,X2)
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | r2_hidden(X3,k1_relat_1(X1))
    | ~ r2_hidden(k1_funct_1(X0,X3),X2) ),
    inference(cnf_transformation,[],[f4022])).

cnf(c_67995,plain,
    ( sP15(X0,X1,X2) != iProver_top
    | r2_hidden(X3,k1_relat_1(X0)) != iProver_top
    | r2_hidden(X3,k1_relat_1(X1)) = iProver_top
    | r2_hidden(k1_funct_1(X0,X3),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1569])).

cnf(c_139256,plain,
    ( sP15(sK214,X0,sK213) != iProver_top
    | r2_hidden(sK212,k1_relat_1(X0)) = iProver_top
    | r2_hidden(sK212,k1_relat_1(sK214)) != iProver_top ),
    inference(superposition,[status(thm)],[c_139248,c_67995])).

cnf(c_1575,negated_conjecture,
    ( r2_hidden(sK212,k1_relat_1(k8_relat_1(sK213,sK214)))
    | r2_hidden(sK212,k1_relat_1(sK214)) ),
    inference(cnf_transformation,[],[f4033])).

cnf(c_67990,plain,
    ( r2_hidden(sK212,k1_relat_1(k8_relat_1(sK213,sK214))) = iProver_top
    | r2_hidden(sK212,k1_relat_1(sK214)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1575])).

cnf(c_136758,plain,
    ( k1_funct_1(k2_funct_1(k8_relat_1(sK213,sK214)),k1_funct_1(k8_relat_1(sK213,sK214),sK212)) = sK212
    | r2_hidden(sK212,k1_relat_1(sK214)) = iProver_top
    | v2_funct_1(k8_relat_1(sK213,sK214)) != iProver_top
    | v1_funct_1(k8_relat_1(sK213,sK214)) != iProver_top
    | v1_relat_1(k8_relat_1(sK213,sK214)) != iProver_top ),
    inference(superposition,[status(thm)],[c_67990,c_68025])).

cnf(c_1585,plain,
    ( r2_hidden(sK212,k1_relat_1(k8_relat_1(sK213,sK214))) = iProver_top
    | r2_hidden(sK212,k1_relat_1(sK214)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1575])).

cnf(c_1571,plain,
    ( ~ sP15(X0,X1,X2)
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | r2_hidden(X3,k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4020])).

cnf(c_84528,plain,
    ( ~ sP15(X0,k8_relat_1(sK213,sK214),X1)
    | r2_hidden(sK212,k1_relat_1(X0))
    | ~ r2_hidden(sK212,k1_relat_1(k8_relat_1(sK213,sK214))) ),
    inference(instantiation,[status(thm)],[c_1571])).

cnf(c_131841,plain,
    ( ~ sP15(sK214,k8_relat_1(sK213,sK214),sK213)
    | ~ r2_hidden(sK212,k1_relat_1(k8_relat_1(sK213,sK214)))
    | r2_hidden(sK212,k1_relat_1(sK214)) ),
    inference(instantiation,[status(thm)],[c_84528])).

cnf(c_131843,plain,
    ( sP15(sK214,k8_relat_1(sK213,sK214),sK213) != iProver_top
    | r2_hidden(sK212,k1_relat_1(k8_relat_1(sK213,sK214))) != iProver_top
    | r2_hidden(sK212,k1_relat_1(sK214)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_131841])).

cnf(c_138492,plain,
    ( r2_hidden(sK212,k1_relat_1(sK214)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_136758,c_1583,c_1584,c_1585,c_131843,c_131845])).

cnf(c_140511,plain,
    ( r2_hidden(sK212,k1_relat_1(X0)) = iProver_top
    | sP15(sK214,X0,sK213) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_139256,c_1583,c_1584,c_1585,c_131843,c_131845])).

cnf(c_140512,plain,
    ( sP15(sK214,X0,sK213) != iProver_top
    | r2_hidden(sK212,k1_relat_1(X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_140511])).

cnf(c_140519,plain,
    ( r2_hidden(sK212,k1_relat_1(k8_relat_1(sK213,sK214))) = iProver_top
    | v1_funct_1(sK214) != iProver_top
    | v1_relat_1(sK214) != iProver_top ),
    inference(superposition,[status(thm)],[c_67926,c_140512])).

cnf(c_1573,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK214,sK212),sK213)
    | ~ r2_hidden(sK212,k1_relat_1(k8_relat_1(sK213,sK214)))
    | ~ r2_hidden(sK212,k1_relat_1(sK214)) ),
    inference(cnf_transformation,[],[f4035])).

cnf(c_1587,plain,
    ( r2_hidden(k1_funct_1(sK214,sK212),sK213) != iProver_top
    | r2_hidden(sK212,k1_relat_1(k8_relat_1(sK213,sK214))) != iProver_top
    | r2_hidden(sK212,k1_relat_1(sK214)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1573])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_140519,c_139248,c_138492,c_1587,c_1584,c_1583])).

%------------------------------------------------------------------------------
