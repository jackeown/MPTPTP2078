%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 344 expanded)
%              Number of leaves         :    9 (  89 expanded)
%              Depth                    :   23
%              Number of atoms          :  288 (1818 expanded)
%              Number of equality atoms :  101 ( 630 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f372,plain,(
    $false ),
    inference(subsumption_resolution,[],[f371,f324])).

fof(f324,plain,(
    r2_hidden(sK2(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)),k11_relat_1(sK1,sK0)) ),
    inference(subsumption_resolution,[],[f323,f29])).

fof(f29,plain,(
    k11_relat_1(sK1,sK0) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k11_relat_1(sK1,sK0) != k1_tarski(k1_funct_1(sK1,sK0))
    & r2_hidden(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f14])).

fof(f14,plain,
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

fof(f10,plain,(
    ? [X0,X1] :
      ( k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r2_hidden(X0,k1_relat_1(X1))
         => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

fof(f323,plain,
    ( k11_relat_1(sK1,sK0) = k1_tarski(k1_funct_1(sK1,sK0))
    | r2_hidden(sK2(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)),k11_relat_1(sK1,sK0)) ),
    inference(trivial_inequality_removal,[],[f322])).

fof(f322,plain,
    ( k1_funct_1(sK1,sK0) != k1_funct_1(sK1,sK0)
    | k11_relat_1(sK1,sK0) = k1_tarski(k1_funct_1(sK1,sK0))
    | r2_hidden(sK2(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)),k11_relat_1(sK1,sK0)) ),
    inference(superposition,[],[f303,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK2(X0,X1) = X0
      | r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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
    inference(rectify,[],[f16])).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f303,plain,(
    k1_funct_1(sK1,sK0) != sK2(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)) ),
    inference(trivial_inequality_removal,[],[f301])).

fof(f301,plain,
    ( k1_funct_1(sK1,sK0) != sK2(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0))
    | k11_relat_1(sK1,sK0) != k11_relat_1(sK1,sK0) ),
    inference(resolution,[],[f88,f122])).

fof(f122,plain,(
    r2_hidden(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f121,f55])).

fof(f55,plain,(
    ! [X9] : k11_relat_1(sK1,X9) = k9_relat_1(sK1,k1_tarski(X9)) ),
    inference(resolution,[],[f26,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f26,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f121,plain,(
    r2_hidden(k1_funct_1(sK1,sK0),k9_relat_1(sK1,k1_tarski(sK0))) ),
    inference(resolution,[],[f81,f44])).

fof(f44,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f81,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,X0)
      | r2_hidden(k1_funct_1(sK1,sK0),k9_relat_1(sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f80,f26])).

fof(f80,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK1,sK0),k9_relat_1(sK1,X0))
      | ~ r2_hidden(sK0,X0)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f76,f27])).

fof(f27,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f76,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK1,sK0),k9_relat_1(sK1,X0))
      | ~ r2_hidden(sK0,X0)
      | ~ v1_funct_1(sK1)
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f28,f47])).

fof(f47,plain,(
    ! [X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | k1_funct_1(X0,X7) != X6
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK3(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK3(X0,X1,X2),X2) )
              & ( ( sK3(X0,X1,X2) = k1_funct_1(X0,sK4(X0,X1,X2))
                  & r2_hidden(sK4(X0,X1,X2),X1)
                  & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK5(X0,X1,X6)) = X6
                    & r2_hidden(sK5(X0,X1,X6),X1)
                    & r2_hidden(sK5(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f21,f24,f23,f22])).

fof(f22,plain,(
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
              ( k1_funct_1(X0,X4) != sK3(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK3(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = sK3(X0,X1,X2)
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( sK3(X0,X1,X2) = k1_funct_1(X0,sK4(X0,X1,X2))
        & r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK5(X0,X1,X6)) = X6
        & r2_hidden(sK5(X0,X1,X6),X1)
        & r2_hidden(sK5(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

fof(f28,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f88,plain,(
    ! [X1] :
      ( ~ r2_hidden(k1_funct_1(sK1,sK0),X1)
      | k1_funct_1(sK1,sK0) != sK2(k1_funct_1(sK1,sK0),X1)
      | k11_relat_1(sK1,sK0) != X1 ) ),
    inference(inner_rewriting,[],[f87])).

fof(f87,plain,(
    ! [X1] :
      ( k11_relat_1(sK1,sK0) != X1
      | k1_funct_1(sK1,sK0) != sK2(k1_funct_1(sK1,sK0),X1)
      | ~ r2_hidden(sK2(k1_funct_1(sK1,sK0),X1),X1) ) ),
    inference(superposition,[],[f29,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
      | sK2(X0,X1) != X0
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f371,plain,(
    ~ r2_hidden(sK2(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)),k11_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f370,f55])).

fof(f370,plain,(
    ~ r2_hidden(sK2(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)),k9_relat_1(sK1,k1_tarski(sK0))) ),
    inference(subsumption_resolution,[],[f363,f303])).

fof(f363,plain,
    ( k1_funct_1(sK1,sK0) = sK2(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0))
    | ~ r2_hidden(sK2(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)),k9_relat_1(sK1,k1_tarski(sK0))) ),
    inference(superposition,[],[f65,f328])).

fof(f328,plain,(
    sK0 = sK5(sK1,k1_tarski(sK0),sK2(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0))) ),
    inference(resolution,[],[f324,f131])).

fof(f131,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(X7,k11_relat_1(sK1,X8))
      | sK5(sK1,k1_tarski(X8),X7) = X8 ) ),
    inference(forward_demodulation,[],[f125,f55])).

fof(f125,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(X7,k9_relat_1(sK1,k1_tarski(X8)))
      | sK5(sK1,k1_tarski(X8),X7) = X8 ) ),
    inference(resolution,[],[f66,f45])).

fof(f45,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f66,plain,(
    ! [X14,X15] :
      ( r2_hidden(sK5(sK1,X14,X15),X14)
      | ~ r2_hidden(X15,k9_relat_1(sK1,X14)) ) ),
    inference(subsumption_resolution,[],[f58,f27])).

fof(f58,plain,(
    ! [X14,X15] :
      ( r2_hidden(sK5(sK1,X14,X15),X14)
      | ~ r2_hidden(X15,k9_relat_1(sK1,X14))
      | ~ v1_funct_1(sK1) ) ),
    inference(resolution,[],[f26,f49])).

fof(f49,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f65,plain,(
    ! [X12,X13] :
      ( k1_funct_1(sK1,sK5(sK1,X12,X13)) = X13
      | ~ r2_hidden(X13,k9_relat_1(sK1,X12)) ) ),
    inference(subsumption_resolution,[],[f57,f27])).

fof(f57,plain,(
    ! [X12,X13] :
      ( k1_funct_1(sK1,sK5(sK1,X12,X13)) = X13
      | ~ r2_hidden(X13,k9_relat_1(sK1,X12))
      | ~ v1_funct_1(sK1) ) ),
    inference(resolution,[],[f26,f48])).

fof(f48,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK5(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK5(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:16:10 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (32656)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.48  % (32672)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.50  % (32665)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.50  % (32649)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (32659)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.51  % (32658)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.51  % (32657)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.51  % (32668)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.51  % (32652)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.52  % (32651)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (32667)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.52  % (32660)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (32650)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.52  % (32670)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.52  % (32653)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  % (32662)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (32671)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.53  % (32673)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.53  % (32648)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.53  % (32654)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.53  % (32659)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f372,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(subsumption_resolution,[],[f371,f324])).
% 0.22/0.53  fof(f324,plain,(
% 0.22/0.53    r2_hidden(sK2(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)),k11_relat_1(sK1,sK0))),
% 0.22/0.53    inference(subsumption_resolution,[],[f323,f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    k11_relat_1(sK1,sK0) != k1_tarski(k1_funct_1(sK1,sK0))),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    k11_relat_1(sK1,sK0) != k1_tarski(k1_funct_1(sK1,sK0)) & r2_hidden(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ? [X0,X1] : (k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0)) & r2_hidden(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (k11_relat_1(sK1,sK0) != k1_tarski(k1_funct_1(sK1,sK0)) & r2_hidden(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ? [X0,X1] : (k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0)) & r2_hidden(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f9])).
% 0.22/0.53  fof(f9,plain,(
% 0.22/0.53    ? [X0,X1] : ((k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0)) & r2_hidden(X0,k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.22/0.53    inference(negated_conjecture,[],[f7])).
% 0.22/0.53  fof(f7,conjecture,(
% 0.22/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).
% 0.22/0.53  fof(f323,plain,(
% 0.22/0.53    k11_relat_1(sK1,sK0) = k1_tarski(k1_funct_1(sK1,sK0)) | r2_hidden(sK2(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)),k11_relat_1(sK1,sK0))),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f322])).
% 0.22/0.53  fof(f322,plain,(
% 0.22/0.53    k1_funct_1(sK1,sK0) != k1_funct_1(sK1,sK0) | k11_relat_1(sK1,sK0) = k1_tarski(k1_funct_1(sK1,sK0)) | r2_hidden(sK2(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)),k11_relat_1(sK1,sK0))),
% 0.22/0.53    inference(superposition,[],[f303,f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.53    inference(rectify,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.53  fof(f303,plain,(
% 0.22/0.53    k1_funct_1(sK1,sK0) != sK2(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0))),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f301])).
% 0.22/0.53  fof(f301,plain,(
% 0.22/0.53    k1_funct_1(sK1,sK0) != sK2(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)) | k11_relat_1(sK1,sK0) != k11_relat_1(sK1,sK0)),
% 0.22/0.53    inference(resolution,[],[f88,f122])).
% 0.22/0.53  fof(f122,plain,(
% 0.22/0.53    r2_hidden(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0))),
% 0.22/0.53    inference(forward_demodulation,[],[f121,f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X9] : (k11_relat_1(sK1,X9) = k9_relat_1(sK1,k1_tarski(X9))) )),
% 0.22/0.53    inference(resolution,[],[f26,f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    v1_relat_1(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f121,plain,(
% 0.22/0.53    r2_hidden(k1_funct_1(sK1,sK0),k9_relat_1(sK1,k1_tarski(sK0)))),
% 0.22/0.53    inference(resolution,[],[f81,f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.22/0.53    inference(equality_resolution,[],[f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.22/0.53    inference(equality_resolution,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(sK0,X0) | r2_hidden(k1_funct_1(sK1,sK0),k9_relat_1(sK1,X0))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f80,f26])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(k1_funct_1(sK1,sK0),k9_relat_1(sK1,X0)) | ~r2_hidden(sK0,X0) | ~v1_relat_1(sK1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f76,f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    v1_funct_1(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(k1_funct_1(sK1,sK0),k9_relat_1(sK1,X0)) | ~r2_hidden(sK0,X0) | ~v1_funct_1(sK1) | ~v1_relat_1(sK1)) )),
% 0.22/0.53    inference(resolution,[],[f28,f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ( ! [X0,X7,X1] : (r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X2,X0,X7,X1] : (r2_hidden(k1_funct_1(X0,X7),X2) | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((sK3(X0,X1,X2) = k1_funct_1(X0,sK4(X0,X1,X2)) & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK5(X0,X1,X6)) = X6 & r2_hidden(sK5(X0,X1,X6),X1) & r2_hidden(sK5(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f21,f24,f23,f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK3(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = sK3(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (sK3(X0,X1,X2) = k1_funct_1(X0,sK4(X0,X1,X2)) & r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),k1_relat_1(X0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK5(X0,X1,X6)) = X6 & r2_hidden(sK5(X0,X1,X6),X1) & r2_hidden(sK5(X0,X1,X6),k1_relat_1(X0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(rectify,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    r2_hidden(sK0,k1_relat_1(sK1))),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    ( ! [X1] : (~r2_hidden(k1_funct_1(sK1,sK0),X1) | k1_funct_1(sK1,sK0) != sK2(k1_funct_1(sK1,sK0),X1) | k11_relat_1(sK1,sK0) != X1) )),
% 0.22/0.53    inference(inner_rewriting,[],[f87])).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    ( ! [X1] : (k11_relat_1(sK1,sK0) != X1 | k1_funct_1(sK1,sK0) != sK2(k1_funct_1(sK1,sK0),X1) | ~r2_hidden(sK2(k1_funct_1(sK1,sK0),X1),X1)) )),
% 0.22/0.53    inference(superposition,[],[f29,f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_tarski(X0) = X1 | sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f371,plain,(
% 0.22/0.53    ~r2_hidden(sK2(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)),k11_relat_1(sK1,sK0))),
% 0.22/0.53    inference(forward_demodulation,[],[f370,f55])).
% 0.22/0.53  fof(f370,plain,(
% 0.22/0.53    ~r2_hidden(sK2(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)),k9_relat_1(sK1,k1_tarski(sK0)))),
% 0.22/0.53    inference(subsumption_resolution,[],[f363,f303])).
% 0.22/0.53  fof(f363,plain,(
% 0.22/0.53    k1_funct_1(sK1,sK0) = sK2(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)) | ~r2_hidden(sK2(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)),k9_relat_1(sK1,k1_tarski(sK0)))),
% 0.22/0.53    inference(superposition,[],[f65,f328])).
% 0.22/0.53  fof(f328,plain,(
% 0.22/0.53    sK0 = sK5(sK1,k1_tarski(sK0),sK2(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)))),
% 0.22/0.53    inference(resolution,[],[f324,f131])).
% 0.22/0.53  fof(f131,plain,(
% 0.22/0.53    ( ! [X8,X7] : (~r2_hidden(X7,k11_relat_1(sK1,X8)) | sK5(sK1,k1_tarski(X8),X7) = X8) )),
% 0.22/0.53    inference(forward_demodulation,[],[f125,f55])).
% 0.22/0.53  fof(f125,plain,(
% 0.22/0.53    ( ! [X8,X7] : (~r2_hidden(X7,k9_relat_1(sK1,k1_tarski(X8))) | sK5(sK1,k1_tarski(X8),X7) = X8) )),
% 0.22/0.53    inference(resolution,[],[f66,f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 0.22/0.53    inference(equality_resolution,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    ( ! [X14,X15] : (r2_hidden(sK5(sK1,X14,X15),X14) | ~r2_hidden(X15,k9_relat_1(sK1,X14))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f58,f27])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X14,X15] : (r2_hidden(sK5(sK1,X14,X15),X14) | ~r2_hidden(X15,k9_relat_1(sK1,X14)) | ~v1_funct_1(sK1)) )),
% 0.22/0.53    inference(resolution,[],[f26,f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ( ! [X6,X0,X1] : (r2_hidden(sK5(X0,X1,X6),X1) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ( ! [X6,X2,X0,X1] : (r2_hidden(sK5(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ( ! [X12,X13] : (k1_funct_1(sK1,sK5(sK1,X12,X13)) = X13 | ~r2_hidden(X13,k9_relat_1(sK1,X12))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f57,f27])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ( ! [X12,X13] : (k1_funct_1(sK1,sK5(sK1,X12,X13)) = X13 | ~r2_hidden(X13,k9_relat_1(sK1,X12)) | ~v1_funct_1(sK1)) )),
% 0.22/0.53    inference(resolution,[],[f26,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X6,X0,X1] : (k1_funct_1(X0,sK5(X0,X1,X6)) = X6 | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ( ! [X6,X2,X0,X1] : (k1_funct_1(X0,sK5(X0,X1,X6)) = X6 | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f25])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (32659)------------------------------
% 0.22/0.53  % (32659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (32659)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (32659)Memory used [KB]: 11001
% 0.22/0.53  % (32659)Time elapsed: 0.104 s
% 0.22/0.53  % (32659)------------------------------
% 0.22/0.53  % (32659)------------------------------
% 0.22/0.54  % (32647)Success in time 0.171 s
%------------------------------------------------------------------------------
