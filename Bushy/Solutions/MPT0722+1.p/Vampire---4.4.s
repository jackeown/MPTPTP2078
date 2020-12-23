%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t177_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:21 EDT 2019

% Result     : Theorem 105.97s
% Output     : Refutation 105.97s
% Verified   : 
% Statistics : Number of formulae       :  139 (5652 expanded)
%              Number of leaves         :   14 (1734 expanded)
%              Depth                    :   30
%              Number of atoms          :  719 (32525 expanded)
%              Number of equality atoms :  192 (7647 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f48243,plain,(
    $false ),
    inference(subsumption_resolution,[],[f48208,f47790])).

fof(f47790,plain,(
    ~ r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),sK1) ),
    inference(subsumption_resolution,[],[f47789,f39680])).

fof(f39680,plain,(
    ! [X4] :
      ( r2_hidden(k1_funct_1(sK0,sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1)),k9_relat_1(sK0,X4))
      | ~ r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),X4) ) ),
    inference(subsumption_resolution,[],[f39679,f75])).

fof(f75,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,
    ( k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1)) != sK1
    & r1_tarski(sK1,k1_relat_1(sK0))
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f53,f52])).

fof(f52,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1
            & r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,X1)) != X1
          & r1_tarski(X1,k1_relat_1(sK0))
          & v2_funct_1(sK0) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1
          & r1_tarski(X1,k1_relat_1(X0))
          & v2_funct_1(X0) )
     => ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,sK1)) != sK1
        & r1_tarski(sK1,k1_relat_1(X0))
        & v2_funct_1(X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1
          & r1_tarski(X1,k1_relat_1(X0))
          & v2_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1
          & r1_tarski(X1,k1_relat_1(X0))
          & v2_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( r1_tarski(X1,k1_relat_1(X0))
              & v2_funct_1(X0) )
           => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
         => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t177_funct_1.p',t177_funct_1)).

fof(f39679,plain,(
    ! [X4] :
      ( r2_hidden(k1_funct_1(sK0,sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1)),k9_relat_1(sK0,X4))
      | ~ r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),X4)
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f39631,f76])).

fof(f76,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f39631,plain,(
    ! [X4] :
      ( r2_hidden(k1_funct_1(sK0,sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1)),k9_relat_1(sK0,X4))
      | ~ r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),X4)
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f39609,f124])).

fof(f124,plain,(
    ! [X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f123])).

fof(f123,plain,(
    ! [X2,X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | k1_funct_1(X0,X7) != X6
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK2(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK2(X0,X1,X2),X2) )
              & ( ( k1_funct_1(X0,sK3(X0,X1,X2)) = sK2(X0,X1,X2)
                  & r2_hidden(sK3(X0,X1,X2),X1)
                  & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK4(X0,X1,X6)) = X6
                    & r2_hidden(sK4(X0,X1,X6),X1)
                    & r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f56,f59,f58,f57])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK2(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK2(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1,X2)) = X3
        & r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1,X6)) = X6
        & r2_hidden(sK4(X0,X1,X6),X1)
        & r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( k1_funct_1(X0,X5) = X3
                      & r2_hidden(X5,X1)
                      & r2_hidden(X5,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ? [X8] :
                      ( k1_funct_1(X0,X8) = X6
                      & r2_hidden(X8,X1)
                      & r2_hidden(X8,k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t177_funct_1.p',d12_funct_1)).

fof(f39609,plain,(
    r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),k1_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f39608,f253])).

fof(f253,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,k1_relat_1(sK0)) ) ),
    inference(resolution,[],[f78,f93])).

fof(f93,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f63,f64])).

fof(f64,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t177_funct_1.p',d3_tarski)).

fof(f78,plain,(
    r1_tarski(sK1,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f54])).

fof(f39608,plain,
    ( r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),k1_relat_1(sK0))
    | r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),sK1) ),
    inference(subsumption_resolution,[],[f39607,f173])).

fof(f173,plain,(
    v1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f145,f76])).

fof(f145,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(resolution,[],[f75,f89])).

fof(f89,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t177_funct_1.p',dt_k2_funct_1)).

fof(f39607,plain,
    ( r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),k1_relat_1(sK0))
    | r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),sK1)
    | ~ v1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f39606,f174])).

fof(f174,plain,(
    v1_funct_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f146,f76])).

fof(f146,plain,
    ( v1_funct_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(resolution,[],[f75,f90])).

fof(f90,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f39606,plain,
    ( r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),k1_relat_1(sK0))
    | r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),sK1)
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f39575,f79])).

fof(f79,plain,(
    k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1)) != sK1 ),
    inference(cnf_transformation,[],[f54])).

fof(f39575,plain,
    ( r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),k1_relat_1(sK0))
    | r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),sK1)
    | k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1)) = sK1
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0)) ),
    inference(duplicate_literal_removal,[],[f39574])).

fof(f39574,plain,
    ( r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),k1_relat_1(sK0))
    | r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),sK1)
    | k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1)) = sK1
    | r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),sK1)
    | ~ v1_funct_1(k2_funct_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK0)) ),
    inference(superposition,[],[f4939,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | k1_funct_1(X0,sK3(X0,X1,X2)) = sK2(X0,X1,X2)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f4939,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(sK0),sK3(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1)),k1_relat_1(sK0))
    | r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),sK1) ),
    inference(resolution,[],[f2121,f210])).

fof(f210,plain,(
    ! [X31] :
      ( ~ r2_hidden(X31,k2_relat_1(sK0))
      | r2_hidden(k1_funct_1(k2_funct_1(sK0),X31),k1_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f209,f76])).

fof(f209,plain,(
    ! [X31] :
      ( r2_hidden(k1_funct_1(k2_funct_1(sK0),X31),k1_relat_1(sK0))
      | ~ r2_hidden(X31,k2_relat_1(sK0))
      | ~ v1_funct_1(sK0) ) ),
    inference(subsumption_resolution,[],[f208,f77])).

fof(f77,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f208,plain,(
    ! [X31] :
      ( r2_hidden(k1_funct_1(k2_funct_1(sK0),X31),k1_relat_1(sK0))
      | ~ r2_hidden(X31,k2_relat_1(sK0))
      | ~ v2_funct_1(sK0)
      | ~ v1_funct_1(sK0) ) ),
    inference(subsumption_resolution,[],[f207,f173])).

fof(f207,plain,(
    ! [X31] :
      ( r2_hidden(k1_funct_1(k2_funct_1(sK0),X31),k1_relat_1(sK0))
      | ~ r2_hidden(X31,k2_relat_1(sK0))
      | ~ v1_relat_1(k2_funct_1(sK0))
      | ~ v2_funct_1(sK0)
      | ~ v1_funct_1(sK0) ) ),
    inference(subsumption_resolution,[],[f167,f174])).

fof(f167,plain,(
    ! [X31] :
      ( r2_hidden(k1_funct_1(k2_funct_1(sK0),X31),k1_relat_1(sK0))
      | ~ r2_hidden(X31,k2_relat_1(sK0))
      | ~ v1_funct_1(k2_funct_1(sK0))
      | ~ v1_relat_1(k2_funct_1(sK0))
      | ~ v2_funct_1(sK0)
      | ~ v1_funct_1(sK0) ) ),
    inference(resolution,[],[f75,f137])).

fof(f137,plain,(
    ! [X4,X0] :
      ( r2_hidden(k1_funct_1(k2_funct_1(X0),X4),k1_relat_1(X0))
      | ~ r2_hidden(X4,k2_relat_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f136])).

fof(f136,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X4),k1_relat_1(X0))
      | ~ r2_hidden(X4,k2_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,k1_relat_1(X0))
      | k1_funct_1(X1,X4) != X5
      | ~ r2_hidden(X4,k2_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ( ( k1_funct_1(X1,sK6(X0,X1)) != sK7(X0,X1)
                  | ~ r2_hidden(sK6(X0,X1),k2_relat_1(X0)) )
                & k1_funct_1(X0,sK7(X0,X1)) = sK6(X0,X1)
                & r2_hidden(sK7(X0,X1),k1_relat_1(X0)) )
              | ( ( k1_funct_1(X0,sK7(X0,X1)) != sK6(X0,X1)
                  | ~ r2_hidden(sK7(X0,X1),k1_relat_1(X0)) )
                & k1_funct_1(X1,sK6(X0,X1)) = sK7(X0,X1)
                & r2_hidden(sK6(X0,X1),k2_relat_1(X0)) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X1,X4) = X5
                        & r2_hidden(X4,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X5) != X4
                      | ~ r2_hidden(X5,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X5) = X4
                        & r2_hidden(X5,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X4) != X5
                      | ~ r2_hidden(X4,k2_relat_1(X0)) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f70,f71])).

fof(f71,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ( k1_funct_1(X1,X2) != X3
              | ~ r2_hidden(X2,k2_relat_1(X0)) )
            & k1_funct_1(X0,X3) = X2
            & r2_hidden(X3,k1_relat_1(X0)) )
          | ( ( k1_funct_1(X0,X3) != X2
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
            & k1_funct_1(X1,X2) = X3
            & r2_hidden(X2,k2_relat_1(X0)) ) )
     => ( ( ( k1_funct_1(X1,sK6(X0,X1)) != sK7(X0,X1)
            | ~ r2_hidden(sK6(X0,X1),k2_relat_1(X0)) )
          & k1_funct_1(X0,sK7(X0,X1)) = sK6(X0,X1)
          & r2_hidden(sK7(X0,X1),k1_relat_1(X0)) )
        | ( ( k1_funct_1(X0,sK7(X0,X1)) != sK6(X0,X1)
            | ~ r2_hidden(sK7(X0,X1),k1_relat_1(X0)) )
          & k1_funct_1(X1,sK6(X0,X1)) = sK7(X0,X1)
          & r2_hidden(sK6(X0,X1),k2_relat_1(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ( ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & k1_funct_1(X1,X2) = X3
                    & r2_hidden(X2,k2_relat_1(X0)) ) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X1,X4) = X5
                        & r2_hidden(X4,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X5) != X4
                      | ~ r2_hidden(X5,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X5) = X4
                        & r2_hidden(X5,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X4) != X5
                      | ~ r2_hidden(X4,k2_relat_1(X0)) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ( ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & k1_funct_1(X1,X2) = X3
                    & r2_hidden(X2,k2_relat_1(X0)) ) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_funct_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) )
                    & k1_funct_1(X0,X3) = X2
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ( ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & k1_funct_1(X1,X2) = X3
                    & r2_hidden(X2,k2_relat_1(X0)) ) )
              | k1_relat_1(X1) != k2_relat_1(X0) )
            & ( ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                      | k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                    & ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                      | k1_funct_1(X1,X2) != X3
                      | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) )
              | k2_funct_1(X0) != X1 ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k1_relat_1(X1) = k2_relat_1(X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( k2_funct_1(X0) = X1
            <=> ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                     => ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) ) )
                    & ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                     => ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) ) ) )
                & k1_relat_1(X1) = k2_relat_1(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t177_funct_1.p',t54_funct_1)).

fof(f2121,plain,
    ( r2_hidden(sK3(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),k2_relat_1(sK0))
    | r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),sK1) ),
    inference(equality_resolution,[],[f401])).

fof(f401,plain,(
    ! [X0] :
      ( sK1 != X0
      | r2_hidden(sK3(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X0),k2_relat_1(sK0))
      | r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X0),X0) ) ),
    inference(forward_demodulation,[],[f400,f191])).

fof(f191,plain,(
    k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f190,f76])).

fof(f190,plain,
    ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0)
    | ~ v1_funct_1(sK0) ),
    inference(subsumption_resolution,[],[f157,f77])).

fof(f157,plain,
    ( k1_relat_1(k2_funct_1(sK0)) = k2_relat_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0) ),
    inference(resolution,[],[f75,f113])).

fof(f113,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t177_funct_1.p',t55_funct_1)).

fof(f400,plain,(
    ! [X0] :
      ( sK1 != X0
      | r2_hidden(sK3(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X0),k1_relat_1(k2_funct_1(sK0)))
      | r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X0),X0) ) ),
    inference(subsumption_resolution,[],[f399,f173])).

fof(f399,plain,(
    ! [X0] :
      ( sK1 != X0
      | r2_hidden(sK3(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X0),k1_relat_1(k2_funct_1(sK0)))
      | r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X0),X0)
      | ~ v1_relat_1(k2_funct_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f371,f174])).

fof(f371,plain,(
    ! [X0] :
      ( sK1 != X0
      | r2_hidden(sK3(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X0),k1_relat_1(k2_funct_1(sK0)))
      | r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X0),X0)
      | ~ v1_funct_1(k2_funct_1(sK0))
      | ~ v1_relat_1(k2_funct_1(sK0)) ) ),
    inference(superposition,[],[f79,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))
      | r2_hidden(sK2(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f47789,plain,
    ( ~ r2_hidden(k1_funct_1(sK0,sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1)),k9_relat_1(sK0,sK1))
    | ~ r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),sK1) ),
    inference(subsumption_resolution,[],[f47730,f39619])).

fof(f39619,plain,(
    k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1))) = sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f39609,f202])).

fof(f202,plain,(
    ! [X28] :
      ( ~ r2_hidden(X28,k1_relat_1(sK0))
      | k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,X28)) = X28 ) ),
    inference(subsumption_resolution,[],[f201,f76])).

fof(f201,plain,(
    ! [X28] :
      ( k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,X28)) = X28
      | ~ r2_hidden(X28,k1_relat_1(sK0))
      | ~ v1_funct_1(sK0) ) ),
    inference(subsumption_resolution,[],[f200,f77])).

fof(f200,plain,(
    ! [X28] :
      ( k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,X28)) = X28
      | ~ r2_hidden(X28,k1_relat_1(sK0))
      | ~ v2_funct_1(sK0)
      | ~ v1_funct_1(sK0) ) ),
    inference(subsumption_resolution,[],[f199,f173])).

fof(f199,plain,(
    ! [X28] :
      ( k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,X28)) = X28
      | ~ r2_hidden(X28,k1_relat_1(sK0))
      | ~ v1_relat_1(k2_funct_1(sK0))
      | ~ v2_funct_1(sK0)
      | ~ v1_funct_1(sK0) ) ),
    inference(subsumption_resolution,[],[f164,f174])).

fof(f164,plain,(
    ! [X28] :
      ( k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,X28)) = X28
      | ~ r2_hidden(X28,k1_relat_1(sK0))
      | ~ v1_funct_1(k2_funct_1(sK0))
      | ~ v1_relat_1(k2_funct_1(sK0))
      | ~ v2_funct_1(sK0)
      | ~ v1_funct_1(sK0) ) ),
    inference(resolution,[],[f75,f131])).

fof(f131,plain,(
    ! [X0,X5] :
      ( k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X5)) = X5
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f130])).

fof(f130,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X1,k1_funct_1(X0,X5)) = X5
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X4,X0,X5,X1] :
      ( k1_funct_1(X1,X4) = X5
      | k1_funct_1(X0,X5) != X4
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | k2_funct_1(X0) != X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f47730,plain,
    ( k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1))) != sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1)
    | ~ r2_hidden(k1_funct_1(sK0,sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1)),k9_relat_1(sK0,sK1))
    | ~ r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),sK1) ),
    inference(resolution,[],[f39618,f2705])).

fof(f2705,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK0))
      | k1_funct_1(k2_funct_1(sK0),X0) != sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1)
      | ~ r2_hidden(X0,k9_relat_1(sK0,sK1))
      | ~ r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),sK1) ) ),
    inference(equality_resolution,[],[f408])).

fof(f408,plain,(
    ! [X4,X3] :
      ( sK1 != X3
      | ~ r2_hidden(X4,k2_relat_1(sK0))
      | k1_funct_1(k2_funct_1(sK0),X4) != sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X3)
      | ~ r2_hidden(X4,k9_relat_1(sK0,sK1))
      | ~ r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X3),X3) ) ),
    inference(forward_demodulation,[],[f407,f191])).

fof(f407,plain,(
    ! [X4,X3] :
      ( sK1 != X3
      | k1_funct_1(k2_funct_1(sK0),X4) != sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X3)
      | ~ r2_hidden(X4,k9_relat_1(sK0,sK1))
      | ~ r2_hidden(X4,k1_relat_1(k2_funct_1(sK0)))
      | ~ r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X3),X3) ) ),
    inference(subsumption_resolution,[],[f406,f173])).

fof(f406,plain,(
    ! [X4,X3] :
      ( sK1 != X3
      | k1_funct_1(k2_funct_1(sK0),X4) != sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X3)
      | ~ r2_hidden(X4,k9_relat_1(sK0,sK1))
      | ~ r2_hidden(X4,k1_relat_1(k2_funct_1(sK0)))
      | ~ r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X3),X3)
      | ~ v1_relat_1(k2_funct_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f374,f174])).

fof(f374,plain,(
    ! [X4,X3] :
      ( sK1 != X3
      | k1_funct_1(k2_funct_1(sK0),X4) != sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X3)
      | ~ r2_hidden(X4,k9_relat_1(sK0,sK1))
      | ~ r2_hidden(X4,k1_relat_1(k2_funct_1(sK0)))
      | ~ r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X3),X3)
      | ~ v1_funct_1(k2_funct_1(sK0))
      | ~ v1_relat_1(k2_funct_1(sK0)) ) ),
    inference(superposition,[],[f79,f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | k1_funct_1(X0,X4) != sK2(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f39618,plain,(
    r2_hidden(k1_funct_1(sK0,sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1)),k2_relat_1(sK0)) ),
    inference(resolution,[],[f39609,f194])).

fof(f194,plain,(
    ! [X19] :
      ( ~ r2_hidden(X19,k1_relat_1(sK0))
      | r2_hidden(k1_funct_1(sK0,X19),k2_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f159,f76])).

fof(f159,plain,(
    ! [X19] :
      ( r2_hidden(k1_funct_1(sK0,X19),k2_relat_1(sK0))
      | ~ r2_hidden(X19,k1_relat_1(sK0))
      | ~ v1_funct_1(sK0) ) ),
    inference(resolution,[],[f75,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t177_funct_1.p',t12_funct_1)).

fof(f48208,plain,(
    r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),sK1) ),
    inference(backward_demodulation,[],[f47793,f48113])).

fof(f48113,plain,(
    r2_hidden(k1_funct_1(k2_funct_1(sK0),sK3(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1)),sK1) ),
    inference(backward_demodulation,[],[f48110,f47830])).

fof(f47830,plain,(
    r2_hidden(sK4(sK0,sK1,sK3(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1)),sK1) ),
    inference(subsumption_resolution,[],[f5362,f47790])).

fof(f5362,plain,
    ( r2_hidden(sK4(sK0,sK1,sK3(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1)),sK1)
    | r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),sK1) ),
    inference(resolution,[],[f2187,f197])).

fof(f197,plain,(
    ! [X24,X25] :
      ( ~ r2_hidden(X25,k9_relat_1(sK0,X24))
      | r2_hidden(sK4(sK0,X24,X25),X24) ) ),
    inference(subsumption_resolution,[],[f162,f76])).

fof(f162,plain,(
    ! [X24,X25] :
      ( r2_hidden(sK4(sK0,X24,X25),X24)
      | ~ r2_hidden(X25,k9_relat_1(sK0,X24))
      | ~ v1_funct_1(sK0) ) ),
    inference(resolution,[],[f75,f126])).

fof(f126,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f2187,plain,
    ( r2_hidden(sK3(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),k9_relat_1(sK0,sK1))
    | r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),sK1) ),
    inference(equality_resolution,[],[f403])).

fof(f403,plain,(
    ! [X1] :
      ( sK1 != X1
      | r2_hidden(sK3(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X1),k9_relat_1(sK0,sK1))
      | r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X1),X1) ) ),
    inference(subsumption_resolution,[],[f402,f173])).

fof(f402,plain,(
    ! [X1] :
      ( sK1 != X1
      | r2_hidden(sK3(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X1),k9_relat_1(sK0,sK1))
      | r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X1),X1)
      | ~ v1_relat_1(k2_funct_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f372,f174])).

fof(f372,plain,(
    ! [X1] :
      ( sK1 != X1
      | r2_hidden(sK3(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X1),k9_relat_1(sK0,sK1))
      | r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X1),X1)
      | ~ v1_funct_1(k2_funct_1(sK0))
      | ~ v1_relat_1(k2_funct_1(sK0)) ) ),
    inference(superposition,[],[f79,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f48110,plain,(
    k1_funct_1(k2_funct_1(sK0),sK3(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1)) = sK4(sK0,sK1,sK3(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1)) ),
    inference(forward_demodulation,[],[f47826,f47828])).

fof(f47828,plain,(
    k1_funct_1(sK0,sK4(sK0,sK1,sK3(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1))) = sK3(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f5360,f47790])).

fof(f5360,plain,
    ( r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),sK1)
    | k1_funct_1(sK0,sK4(sK0,sK1,sK3(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1))) = sK3(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f2187,f196])).

fof(f196,plain,(
    ! [X23,X22] :
      ( ~ r2_hidden(X23,k9_relat_1(sK0,X22))
      | k1_funct_1(sK0,sK4(sK0,X22,X23)) = X23 ) ),
    inference(subsumption_resolution,[],[f161,f76])).

fof(f161,plain,(
    ! [X23,X22] :
      ( k1_funct_1(sK0,sK4(sK0,X22,X23)) = X23
      | ~ r2_hidden(X23,k9_relat_1(sK0,X22))
      | ~ v1_funct_1(sK0) ) ),
    inference(resolution,[],[f75,f125])).

fof(f125,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f47826,plain,(
    k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,sK4(sK0,sK1,sK3(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1)))) = sK4(sK0,sK1,sK3(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1)) ),
    inference(subsumption_resolution,[],[f5358,f47790])).

fof(f5358,plain,
    ( r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),sK1)
    | k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,sK4(sK0,sK1,sK3(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1)))) = sK4(sK0,sK1,sK3(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1)) ),
    inference(resolution,[],[f2187,f1277])).

fof(f1277,plain,(
    ! [X14,X15] :
      ( ~ r2_hidden(X15,k9_relat_1(sK0,X14))
      | k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,sK4(sK0,X14,X15))) = sK4(sK0,X14,X15) ) ),
    inference(subsumption_resolution,[],[f1276,f75])).

fof(f1276,plain,(
    ! [X14,X15] :
      ( k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,sK4(sK0,X14,X15))) = sK4(sK0,X14,X15)
      | ~ r2_hidden(X15,k9_relat_1(sK0,X14))
      | ~ v1_relat_1(sK0) ) ),
    inference(subsumption_resolution,[],[f1264,f76])).

fof(f1264,plain,(
    ! [X14,X15] :
      ( k1_funct_1(k2_funct_1(sK0),k1_funct_1(sK0,sK4(sK0,X14,X15))) = sK4(sK0,X14,X15)
      | ~ r2_hidden(X15,k9_relat_1(sK0,X14))
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f202,f127])).

fof(f127,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f47793,plain,(
    k1_funct_1(k2_funct_1(sK0),sK3(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1)) = sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f2335,f47790])).

fof(f2335,plain,
    ( r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1),sK1)
    | k1_funct_1(k2_funct_1(sK0),sK3(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1)) = sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),sK1) ),
    inference(equality_resolution,[],[f405])).

fof(f405,plain,(
    ! [X2] :
      ( sK1 != X2
      | k1_funct_1(k2_funct_1(sK0),sK3(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X2)) = sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X2)
      | r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X2),X2) ) ),
    inference(subsumption_resolution,[],[f404,f173])).

fof(f404,plain,(
    ! [X2] :
      ( sK1 != X2
      | k1_funct_1(k2_funct_1(sK0),sK3(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X2)) = sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X2)
      | r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X2),X2)
      | ~ v1_relat_1(k2_funct_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f373,f174])).

fof(f373,plain,(
    ! [X2] :
      ( sK1 != X2
      | k1_funct_1(k2_funct_1(sK0),sK3(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X2)) = sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X2)
      | r2_hidden(sK2(k2_funct_1(sK0),k9_relat_1(sK0,sK1),X2),X2)
      | ~ v1_funct_1(k2_funct_1(sK0))
      | ~ v1_relat_1(k2_funct_1(sK0)) ) ),
    inference(superposition,[],[f79,f87])).
%------------------------------------------------------------------------------
