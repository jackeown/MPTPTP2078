%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t117_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:13 EDT 2019

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 342 expanded)
%              Number of leaves         :    9 (  90 expanded)
%              Depth                    :   21
%              Number of atoms          :  314 (1844 expanded)
%              Number of equality atoms :  115 ( 700 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7289,plain,(
    $false ),
    inference(subsumption_resolution,[],[f7288,f7248])).

fof(f7248,plain,(
    k1_funct_1(sK1,sK0) != sK3(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f7244,f65])).

fof(f65,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK3(X0,X1) != X0
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( sK3(X0,X1) = X0
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK3(X0,X1) != X0
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( sK3(X0,X1) = X0
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t117_funct_1.p',d1_tarski)).

fof(f7244,plain,
    ( k1_funct_1(sK1,sK0) != sK3(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0))
    | ~ r2_hidden(sK0,k1_tarski(sK0)) ),
    inference(resolution,[],[f7242,f146])).

fof(f146,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK1,sK0),k11_relat_1(sK1,X0))
      | ~ r2_hidden(sK0,k1_tarski(X0)) ) ),
    inference(superposition,[],[f104,f76])).

fof(f76,plain,(
    ! [X9] : k11_relat_1(sK1,X9) = k9_relat_1(sK1,k1_tarski(X9)) ),
    inference(resolution,[],[f44,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t117_funct_1.p',d16_relat_1)).

fof(f44,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( k11_relat_1(sK1,sK0) != k1_tarski(k1_funct_1(sK1,sK0))
    & r2_hidden(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f29])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0))
        & r2_hidden(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k11_relat_1(sK1,sK0) != k1_tarski(k1_funct_1(sK1,sK0))
      & r2_hidden(sK0,k1_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r2_hidden(X0,k1_relat_1(X1))
         => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t117_funct_1.p',t117_funct_1)).

fof(f104,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK1,sK0),k9_relat_1(sK1,X0))
      | ~ r2_hidden(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f103,f44])).

fof(f103,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK1,sK0),k9_relat_1(sK1,X0))
      | ~ r2_hidden(sK0,X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f97,f45])).

fof(f45,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f97,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK1,sK0),k9_relat_1(sK1,X0))
      | ~ r2_hidden(sK0,X0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f46,f68])).

fof(f68,plain,(
    ! [X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | k1_funct_1(X0,X7) != X6
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK4(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK4(X0,X1,X2),X2) )
              & ( ( k1_funct_1(X0,sK5(X0,X1,X2)) = sK4(X0,X1,X2)
                  & r2_hidden(sK5(X0,X1,X2),X1)
                  & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK6(X0,X1,X6)) = X6
                    & r2_hidden(sK6(X0,X1,X6),X1)
                    & r2_hidden(sK6(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f39,f42,f41,f40])).

fof(f40,plain,(
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
              ( k1_funct_1(X0,X4) != sK4(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK4(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X1,X2)) = X3
        & r2_hidden(sK5(X0,X1,X2),X1)
        & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK6(X0,X1,X6)) = X6
        & r2_hidden(sK6(X0,X1,X6),X1)
        & r2_hidden(sK6(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/funct_1__t117_funct_1.p',d12_funct_1)).

fof(f46,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f7242,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0))
    | k1_funct_1(sK1,sK0) != sK3(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f7215,f47])).

fof(f47,plain,(
    k11_relat_1(sK1,sK0) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f7215,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0))
    | k11_relat_1(sK1,sK0) = k1_tarski(k1_funct_1(sK1,sK0))
    | k1_funct_1(sK1,sK0) != sK3(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f7213,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK3(X0,X1) != X0
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7213,plain,
    ( r2_hidden(sK3(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)),k11_relat_1(sK1,sK0))
    | ~ r2_hidden(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f7212,f47])).

fof(f7212,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0))
    | k11_relat_1(sK1,sK0) = k1_tarski(k1_funct_1(sK1,sK0))
    | r2_hidden(sK3(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)),k11_relat_1(sK1,sK0)) ),
    inference(equality_resolution,[],[f1236])).

fof(f1236,plain,(
    ! [X0] :
      ( k11_relat_1(sK1,sK0) != X0
      | ~ r2_hidden(k1_funct_1(sK1,sK0),X0)
      | k1_tarski(k1_funct_1(sK1,sK0)) = X0
      | r2_hidden(sK3(k1_funct_1(sK1,sK0),X0),X0) ) ),
    inference(subsumption_resolution,[],[f1235,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK3(X0,X1) = X0
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1235,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_funct_1(sK1,sK0),X0)
      | k1_funct_1(sK1,sK0) != sK3(k1_funct_1(sK1,sK0),X0)
      | k11_relat_1(sK1,sK0) != X0
      | k1_tarski(k1_funct_1(sK1,sK0)) = X0
      | r2_hidden(sK3(k1_funct_1(sK1,sK0),X0),X0) ) ),
    inference(superposition,[],[f108,f52])).

fof(f108,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK3(k1_funct_1(sK1,sK0),X1),X1)
      | k1_funct_1(sK1,sK0) != sK3(k1_funct_1(sK1,sK0),X1)
      | k11_relat_1(sK1,sK0) != X1 ) ),
    inference(superposition,[],[f47,f53])).

fof(f7288,plain,(
    k1_funct_1(sK1,sK0) = sK3(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)) ),
    inference(duplicate_literal_removal,[],[f7282])).

fof(f7282,plain,
    ( k1_funct_1(sK1,sK0) = sK3(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0))
    | k1_funct_1(sK1,sK0) = sK3(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)) ),
    inference(backward_demodulation,[],[f7256,f4150])).

fof(f4150,plain,
    ( k1_funct_1(sK1,sK0) = sK3(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0))
    | k1_funct_1(sK1,sK6(sK1,k1_tarski(sK0),sK3(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)))) = sK3(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f1004,f134])).

fof(f134,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(X13,k11_relat_1(sK1,X12))
      | k1_funct_1(sK1,sK6(sK1,k1_tarski(X12),X13)) = X13 ) ),
    inference(subsumption_resolution,[],[f133,f44])).

fof(f133,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(X13,k11_relat_1(sK1,X12))
      | k1_funct_1(sK1,sK6(sK1,k1_tarski(X12),X13)) = X13
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f120,f45])).

fof(f120,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(X13,k11_relat_1(sK1,X12))
      | k1_funct_1(sK1,sK6(sK1,k1_tarski(X12),X13)) = X13
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f69,f76])).

fof(f69,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK6(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK6(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1004,plain,
    ( r2_hidden(sK3(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)),k11_relat_1(sK1,sK0))
    | k1_funct_1(sK1,sK0) = sK3(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)) ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,(
    ! [X0] :
      ( k11_relat_1(sK1,sK0) != X0
      | k1_funct_1(sK1,sK0) = sK3(k1_funct_1(sK1,sK0),X0)
      | r2_hidden(sK3(k1_funct_1(sK1,sK0),X0),X0) ) ),
    inference(superposition,[],[f47,f52])).

fof(f7256,plain,(
    sK0 = sK6(sK1,k1_tarski(sK0),sK3(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0))) ),
    inference(resolution,[],[f7251,f190])).

fof(f190,plain,(
    ! [X19,X18] :
      ( ~ r2_hidden(X18,k11_relat_1(sK1,X19))
      | sK6(sK1,k1_tarski(X19),X18) = X19 ) ),
    inference(forward_demodulation,[],[f186,f76])).

fof(f186,plain,(
    ! [X19,X18] :
      ( ~ r2_hidden(X18,k9_relat_1(sK1,k1_tarski(X19)))
      | sK6(sK1,k1_tarski(X19),X18) = X19 ) ),
    inference(resolution,[],[f87,f66])).

fof(f66,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f87,plain,(
    ! [X14,X15] :
      ( r2_hidden(sK6(sK1,X14,X15),X14)
      | ~ r2_hidden(X15,k9_relat_1(sK1,X14)) ) ),
    inference(subsumption_resolution,[],[f79,f45])).

fof(f79,plain,(
    ! [X14,X15] :
      ( r2_hidden(sK6(sK1,X14,X15),X14)
      | ~ r2_hidden(X15,k9_relat_1(sK1,X14))
      | ~ v1_funct_1(sK1) ) ),
    inference(resolution,[],[f44,f70])).

fof(f70,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f7251,plain,(
    r2_hidden(sK3(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)),k11_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f7250,f47])).

fof(f7250,plain,
    ( k11_relat_1(sK1,sK0) = k1_tarski(k1_funct_1(sK1,sK0))
    | r2_hidden(sK3(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)),k11_relat_1(sK1,sK0)) ),
    inference(trivial_inequality_removal,[],[f7249])).

fof(f7249,plain,
    ( k1_funct_1(sK1,sK0) != k1_funct_1(sK1,sK0)
    | k11_relat_1(sK1,sK0) = k1_tarski(k1_funct_1(sK1,sK0))
    | r2_hidden(sK3(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)),k11_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f7248,f52])).
%------------------------------------------------------------------------------
