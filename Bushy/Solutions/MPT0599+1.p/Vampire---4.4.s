%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t203_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:58 EDT 2019

% Result     : Theorem 10.74s
% Output     : Refutation 10.74s
% Verified   : 
% Statistics : Number of formulae       :   55 (  88 expanded)
%              Number of leaves         :   13 (  28 expanded)
%              Depth                    :   14
%              Number of atoms          :  222 ( 415 expanded)
%              Number of equality atoms :   49 (  56 expanded)
%              Maximal formula depth    :   12 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6383,plain,(
    $false ),
    inference(subsumption_resolution,[],[f71,f6380])).

fof(f6380,plain,(
    ! [X1] : k11_relat_1(k2_zfmisc_1(sK3,X1),sK2) = X1 ),
    inference(superposition,[],[f6376,f177])).

fof(f177,plain,(
    ! [X2,X0,X1] : k11_relat_1(k2_zfmisc_1(X0,X1),X2) = k9_relat_1(k2_zfmisc_1(X0,X1),k1_tarski(X2)) ),
    inference(resolution,[],[f73,f85])).

fof(f85,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t203_relat_1.p',fc6_relat_1)).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t203_relat_1.p',d16_relat_1)).

fof(f6376,plain,(
    ! [X17] : k9_relat_1(k2_zfmisc_1(sK3,X17),k1_tarski(sK2)) = X17 ),
    inference(resolution,[],[f6359,f112])).

fof(f112,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK10(X0,X1) != X0
            | ~ r2_hidden(sK10(X0,X1),X1) )
          & ( sK10(X0,X1) = X0
            | r2_hidden(sK10(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f64,f65])).

fof(f65,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK10(X0,X1) != X0
          | ~ r2_hidden(sK10(X0,X1),X1) )
        & ( sK10(X0,X1) = X0
          | r2_hidden(sK10(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
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
    inference(rectify,[],[f63])).

fof(f63,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t203_relat_1.p',d1_tarski)).

fof(f6359,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2,X0)
      | k9_relat_1(k2_zfmisc_1(sK3,X1),X0) = X1 ) ),
    inference(resolution,[],[f6334,f306])).

fof(f306,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X2,k2_zfmisc_1(X0,X1),X3)
      | k9_relat_1(k2_zfmisc_1(X0,X1),X2) = X3 ) ),
    inference(resolution,[],[f245,f85])).

fof(f245,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = X2
      | ~ sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f75,f82])).

fof(f82,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f31,f44,f43])).

fof(f43,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> sP0(X1,X0,X2) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t203_relat_1.p',d13_relat_1)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0)
      | ~ sP0(X1,X0,X2)
      | k9_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ~ sP0(X1,X0,X2) )
          & ( sP0(X1,X0,X2)
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f6334,plain,(
    ! [X66,X65] :
      ( sP0(X65,k2_zfmisc_1(sK3,X66),X66)
      | ~ r2_hidden(sK2,X65) ) ),
    inference(resolution,[],[f6314,f70])).

fof(f70,plain,(
    r2_hidden(sK2,sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( k11_relat_1(k2_zfmisc_1(sK3,sK4),sK2) != sK4
    & r2_hidden(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f29,f46])).

fof(f46,plain,
    ( ? [X0,X1,X2] :
        ( k11_relat_1(k2_zfmisc_1(X1,X2),X0) != X2
        & r2_hidden(X0,X1) )
   => ( k11_relat_1(k2_zfmisc_1(sK3,sK4),sK2) != sK4
      & r2_hidden(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( k11_relat_1(k2_zfmisc_1(X1,X2),X0) != X2
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,X1)
       => k11_relat_1(k2_zfmisc_1(X1,X2),X0) = X2 ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => k11_relat_1(k2_zfmisc_1(X1,X2),X0) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t203_relat_1.p',t203_relat_1)).

fof(f6314,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | sP0(X0,k2_zfmisc_1(X1,X2),X2) ) ),
    inference(subsumption_resolution,[],[f6313,f4106])).

fof(f4106,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,k2_zfmisc_1(X1,X2),X2),X2)
      | sP0(X0,k2_zfmisc_1(X1,X2),X2) ) ),
    inference(factoring,[],[f1336])).

fof(f1336,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK5(X0,k2_zfmisc_1(X1,X2),X3),X3)
      | r2_hidden(sK5(X0,k2_zfmisc_1(X1,X2),X3),X2)
      | sP0(X0,k2_zfmisc_1(X1,X2),X3) ) ),
    inference(resolution,[],[f79,f106])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t203_relat_1.p',t106_zfmisc_1)).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X1)
      | sP0(X0,X1,X2)
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ! [X4] :
                ( ~ r2_hidden(X4,X0)
                | ~ r2_hidden(k4_tarski(X4,sK5(X0,X1,X2)),X1) )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK6(X0,X1,X2),X0)
              & r2_hidden(k4_tarski(sK6(X0,X1,X2),sK5(X0,X1,X2)),X1) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r2_hidden(X7,X0)
                  | ~ r2_hidden(k4_tarski(X7,X6),X1) ) )
            & ( ( r2_hidden(sK7(X0,X1,X6),X0)
                & r2_hidden(k4_tarski(sK7(X0,X1,X6),X6),X1) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f50,f53,f52,f51])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X0)
                | ~ r2_hidden(k4_tarski(X4,X3),X1) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X0)
                & r2_hidden(k4_tarski(X5,X3),X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X0)
              | ~ r2_hidden(k4_tarski(X4,sK5(X0,X1,X2)),X1) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X0)
              & r2_hidden(k4_tarski(X5,sK5(X0,X1,X2)),X1) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X0)
          & r2_hidden(k4_tarski(X5,X3),X1) )
     => ( r2_hidden(sK6(X0,X1,X2),X0)
        & r2_hidden(k4_tarski(sK6(X0,X1,X2),X3),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X0)
          & r2_hidden(k4_tarski(X8,X6),X1) )
     => ( r2_hidden(sK7(X0,X1,X6),X0)
        & r2_hidden(k4_tarski(sK7(X0,X1,X6),X6),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(X4,X0)
                  | ~ r2_hidden(k4_tarski(X4,X3),X1) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X5] :
                  ( r2_hidden(X5,X0)
                  & r2_hidden(k4_tarski(X5,X3),X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( ~ r2_hidden(X7,X0)
                  | ~ r2_hidden(k4_tarski(X7,X6),X1) ) )
            & ( ? [X8] :
                  ( r2_hidden(X8,X0)
                  & r2_hidden(k4_tarski(X8,X6),X1) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( ~ r2_hidden(X4,X1)
                  | ~ r2_hidden(k4_tarski(X4,X3),X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4] :
                  ( ~ r2_hidden(X4,X1)
                  | ~ r2_hidden(k4_tarski(X4,X3),X0) ) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f6313,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,k2_zfmisc_1(X1,X2),X2)
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(sK5(X0,k2_zfmisc_1(X1,X2),X2),X2)
      | ~ r2_hidden(X3,X1) ) ),
    inference(duplicate_literal_removal,[],[f6242])).

fof(f6242,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,k2_zfmisc_1(X1,X2),X2)
      | sP0(X0,k2_zfmisc_1(X1,X2),X2)
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(sK5(X0,k2_zfmisc_1(X1,X2),X2),X2)
      | ~ r2_hidden(X3,X1) ) ),
    inference(resolution,[],[f4106,f1527])).

fof(f1527,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(sK5(X1,k2_zfmisc_1(X2,X3),X4),X4)
      | sP0(X1,k2_zfmisc_1(X2,X3),X4)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(sK5(X1,k2_zfmisc_1(X2,X3),X4),X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f81,f107])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X4,sK5(X0,X1,X2)),X1)
      | ~ r2_hidden(X4,X0)
      | sP0(X0,X1,X2)
      | ~ r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f71,plain,(
    k11_relat_1(k2_zfmisc_1(sK3,sK4),sK2) != sK4 ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
