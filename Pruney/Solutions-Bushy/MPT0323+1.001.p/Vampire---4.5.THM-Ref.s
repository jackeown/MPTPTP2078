%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0323+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:45 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 929 expanded)
%              Number of leaves         :   14 ( 288 expanded)
%              Depth                    :   22
%              Number of atoms          :  359 (6491 expanded)
%              Number of equality atoms :    8 (  72 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f131,plain,(
    $false ),
    inference(subsumption_resolution,[],[f130,f125])).

fof(f125,plain,(
    sP0(sK7(sK5)) ),
    inference(subsumption_resolution,[],[f124,f122])).

fof(f122,plain,
    ( sP0(sK7(sK5))
    | r1_tarski(sK2(sK7(sK5)),sK7(sK5)) ),
    inference(resolution,[],[f119,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | r1_tarski(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( ~ r2_hidden(sK2(X0),X0)
        & ~ r2_tarski(sK2(X0),X0)
        & r1_tarski(sK2(X0),X0) )
      | ~ sP1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(X1,X0)
          & ~ r2_tarski(X1,X0)
          & r1_tarski(X1,X0) )
     => ( ~ r2_hidden(sK2(X0),X0)
        & ~ r2_tarski(sK2(X0),X0)
        & r1_tarski(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(X1,X0)
          & ~ r2_tarski(X1,X0)
          & r1_tarski(X1,X0) )
      | ~ sP1(X0) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & ~ r2_tarski(X2,X1)
          & r1_tarski(X2,X1) )
      | ~ sP1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & ~ r2_tarski(X2,X1)
          & r1_tarski(X2,X1) )
      | ~ sP1(X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f119,plain,
    ( sP1(sK7(sK5))
    | sP0(sK7(sK5)) ),
    inference(resolution,[],[f115,f47])).

fof(f47,plain,(
    ! [X0] : r2_hidden(X0,sK7(X0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X2] :
          ( r2_hidden(X2,sK7(X0))
          | r2_tarski(X2,sK7(X0))
          | ~ r1_tarski(X2,sK7(X0)) )
      & ! [X3] :
          ( ( ! [X5] :
                ( r2_hidden(X5,sK8(X0,X3))
                | ~ r1_tarski(X5,X3) )
            & r2_hidden(sK8(X0,X3),sK7(X0)) )
          | ~ r2_hidden(X3,sK7(X0)) )
      & ! [X6,X7] :
          ( r2_hidden(X7,sK7(X0))
          | ~ r1_tarski(X7,X6)
          | ~ r2_hidden(X6,sK7(X0)) )
      & r2_hidden(X0,sK7(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f11,f29,f28])).

% (3018)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | r2_tarski(X2,X1)
              | ~ r1_tarski(X2,X1) )
          & ! [X3] :
              ( ? [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X4)
                      | ~ r1_tarski(X5,X3) )
                  & r2_hidden(X4,X1) )
              | ~ r2_hidden(X3,X1) )
          & ! [X6,X7] :
              ( r2_hidden(X7,X1)
              | ~ r1_tarski(X7,X6)
              | ~ r2_hidden(X6,X1) )
          & r2_hidden(X0,X1) )
     => ( ! [X2] :
            ( r2_hidden(X2,sK7(X0))
            | r2_tarski(X2,sK7(X0))
            | ~ r1_tarski(X2,sK7(X0)) )
        & ! [X3] :
            ( ? [X4] :
                ( ! [X5] :
                    ( r2_hidden(X5,X4)
                    | ~ r1_tarski(X5,X3) )
                & r2_hidden(X4,sK7(X0)) )
            | ~ r2_hidden(X3,sK7(X0)) )
        & ! [X7,X6] :
            ( r2_hidden(X7,sK7(X0))
            | ~ r1_tarski(X7,X6)
            | ~ r2_hidden(X6,sK7(X0)) )
        & r2_hidden(X0,sK7(X0)) ) ) ),
    introduced(choice_axiom,[])).

% (3029)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f29,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r2_hidden(X5,X4)
              | ~ r1_tarski(X5,X3) )
          & r2_hidden(X4,sK7(X0)) )
     => ( ! [X5] :
            ( r2_hidden(X5,sK8(X0,X3))
            | ~ r1_tarski(X5,X3) )
        & r2_hidden(sK8(X0,X3),sK7(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | r2_tarski(X2,X1)
          | ~ r1_tarski(X2,X1) )
      & ! [X3] :
          ( ? [X4] :
              ( ! [X5] :
                  ( r2_hidden(X5,X4)
                  | ~ r1_tarski(X5,X3) )
              & r2_hidden(X4,X1) )
          | ~ r2_hidden(X3,X1) )
      & ! [X6,X7] :
          ( r2_hidden(X7,X1)
          | ~ r1_tarski(X7,X6)
          | ~ r2_hidden(X6,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | r2_tarski(X2,X1)
          | ~ r1_tarski(X2,X1) )
      & ! [X3] :
          ( ? [X4] :
              ( ! [X5] :
                  ( r2_hidden(X5,X4)
                  | ~ r1_tarski(X5,X3) )
              & r2_hidden(X4,X1) )
          | ~ r2_hidden(X3,X1) )
      & ! [X6,X7] :
          ( r2_hidden(X7,X1)
          | ~ r1_tarski(X7,X6)
          | ~ r2_hidden(X6,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

% (3028)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f7,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & ~ r2_tarski(X2,X1)
            & r1_tarski(X2,X1) )
      & ! [X3] :
          ~ ( ! [X4] :
                ~ ( ! [X5] :
                      ( r1_tarski(X5,X3)
                     => r2_hidden(X5,X4) )
                  & r2_hidden(X4,X1) )
            & r2_hidden(X3,X1) )
      & ! [X6,X7] :
          ( ( r1_tarski(X7,X6)
            & r2_hidden(X6,X1) )
         => r2_hidden(X7,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & ~ r2_tarski(X2,X1)
            & r1_tarski(X2,X1) )
      & ! [X2] :
          ~ ( ! [X3] :
                ~ ( ! [X4] :
                      ( r1_tarski(X4,X2)
                     => r2_hidden(X4,X3) )
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X1) )
      & ! [X2,X3] :
          ( ( r1_tarski(X3,X2)
            & r2_hidden(X2,X1) )
         => r2_hidden(X3,X1) )
      & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tarski)).

% (3039)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f115,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5,sK7(X0))
      | sP0(sK7(X0))
      | sP1(sK7(X0)) ) ),
    inference(subsumption_resolution,[],[f114,f45])).

fof(f45,plain,(
    ! [X1] :
      ( r2_hidden(sK6(X1),X1)
      | sP1(X1)
      | sP0(X1)
      | ~ r2_hidden(sK5,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X1] :
      ( sP1(X1)
      | ( ~ r2_hidden(k1_zfmisc_1(sK6(X1)),X1)
        & r2_hidden(sK6(X1),X1) )
      | sP0(X1)
      | ~ r2_hidden(sK5,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f24,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
      ! [X1] :
        ( sP1(X1)
        | ? [X2] :
            ( ~ r2_hidden(k1_zfmisc_1(X2),X1)
            & r2_hidden(X2,X1) )
        | sP0(X1)
        | ~ r2_hidden(X0,X1) )
   => ! [X1] :
        ( sP1(X1)
        | ? [X2] :
            ( ~ r2_hidden(k1_zfmisc_1(X2),X1)
            & r2_hidden(X2,X1) )
        | sP0(X1)
        | ~ r2_hidden(sK5,X1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_zfmisc_1(X2),X1)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k1_zfmisc_1(sK6(X1)),X1)
        & r2_hidden(sK6(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
    ! [X1] :
      ( sP1(X1)
      | ? [X2] :
          ( ~ r2_hidden(k1_zfmisc_1(X2),X1)
          & r2_hidden(X2,X1) )
      | sP0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ? [X0] :
    ! [X1] :
      ( sP1(X1)
      | ? [X3] :
          ( ~ r2_hidden(k1_zfmisc_1(X3),X1)
          & r2_hidden(X3,X1) )
      | sP0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_folding,[],[f9,f14,f13])).

fof(f13,plain,(
    ! [X1] :
      ( ? [X4,X5] :
          ( ~ r2_hidden(X5,X1)
          & r1_tarski(X5,X4)
          & r2_hidden(X4,X1) )
      | ~ sP0(X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f9,plain,(
    ? [X0] :
    ! [X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & ~ r2_tarski(X2,X1)
          & r1_tarski(X2,X1) )
      | ? [X3] :
          ( ~ r2_hidden(k1_zfmisc_1(X3),X1)
          & r2_hidden(X3,X1) )
      | ? [X4,X5] :
          ( ~ r2_hidden(X5,X1)
          & r1_tarski(X5,X4)
          & r2_hidden(X4,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
    ! [X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & ~ r2_tarski(X2,X1)
          & r1_tarski(X2,X1) )
      | ? [X3] :
          ( ~ r2_hidden(k1_zfmisc_1(X3),X1)
          & r2_hidden(X3,X1) )
      | ? [X4,X5] :
          ( ~ r2_hidden(X5,X1)
          & r1_tarski(X5,X4)
          & r2_hidden(X4,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ~ ! [X0] :
      ? [X1] :
        ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X1)
              & ~ r2_tarski(X2,X1)
              & r1_tarski(X2,X1) )
        & ! [X3] :
            ( r2_hidden(X3,X1)
           => r2_hidden(k1_zfmisc_1(X3),X1) )
        & ! [X4,X5] :
            ( ( r1_tarski(X5,X4)
              & r2_hidden(X4,X1) )
           => r2_hidden(X5,X1) )
        & r2_hidden(X0,X1) ) ),
    inference(rectify,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
      ? [X1] :
        ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X1)
              & ~ r2_tarski(X2,X1)
              & r1_tarski(X2,X1) )
        & ! [X2] :
            ( r2_hidden(X2,X1)
           => r2_hidden(k1_zfmisc_1(X2),X1) )
        & ! [X2,X3] :
            ( ( r1_tarski(X3,X2)
              & r2_hidden(X2,X1) )
           => r2_hidden(X3,X1) )
        & r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & ~ r2_tarski(X2,X1)
            & r1_tarski(X2,X1) )
      & ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(k1_zfmisc_1(X2),X1) )
      & ! [X2,X3] :
          ( ( r1_tarski(X3,X2)
            & r2_hidden(X2,X1) )
         => r2_hidden(X3,X1) )
      & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t136_zfmisc_1)).

fof(f114,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK6(sK7(X0)),sK7(X0))
      | sP1(sK7(X0))
      | sP0(sK7(X0))
      | ~ r2_hidden(sK5,sK7(X0)) ) ),
    inference(resolution,[],[f113,f46])).

fof(f46,plain,(
    ! [X1] :
      ( ~ r2_hidden(k1_zfmisc_1(sK6(X1)),X1)
      | sP1(X1)
      | sP0(X1)
      | ~ r2_hidden(sK5,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f113,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_zfmisc_1(X0),sK7(X1))
      | ~ r2_hidden(X0,sK7(X1)) ) ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_zfmisc_1(X0),sK7(X1))
      | ~ r2_hidden(X0,sK7(X1))
      | ~ r2_hidden(X0,sK7(X1)) ) ),
    inference(resolution,[],[f107,f49])).

fof(f49,plain,(
    ! [X0,X3] :
      ( r2_hidden(sK8(X0,X3),sK7(X0))
      | ~ r2_hidden(X3,sK7(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK8(X1,X0),sK7(X2))
      | r2_hidden(k1_zfmisc_1(X0),sK7(X2))
      | ~ r2_hidden(X0,sK7(X1)) ) ),
    inference(resolution,[],[f106,f48])).

fof(f48,plain,(
    ! [X6,X0,X7] :
      ( ~ r1_tarski(X7,X6)
      | r2_hidden(X7,sK7(X0))
      | ~ r2_hidden(X6,sK7(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),sK8(X1,X0))
      | ~ r2_hidden(X0,sK7(X1)) ) ),
    inference(duplicate_literal_removal,[],[f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK7(X1))
      | r1_tarski(k1_zfmisc_1(X0),sK8(X1,X0))
      | r1_tarski(k1_zfmisc_1(X0),sK8(X1,X0)) ) ),
    inference(resolution,[],[f76,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK9(k1_zfmisc_1(X0),X1),X0)
      | r1_tarski(k1_zfmisc_1(X0),X1) ) ),
    inference(resolution,[],[f53,f60])).

fof(f60,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK10(X0,X1),X0)
            | ~ r2_hidden(sK10(X0,X1),X1) )
          & ( r1_tarski(sK10(X0,X1),X0)
            | r2_hidden(sK10(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK10(X0,X1),X0)
          | ~ r2_hidden(sK10(X0,X1),X1) )
        & ( r1_tarski(sK10(X0,X1),X0)
          | r2_hidden(sK10(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(sK9(X0,sK8(X1,X2)),X2)
      | ~ r2_hidden(X2,sK7(X1))
      | r1_tarski(X0,sK8(X1,X2)) ) ),
    inference(resolution,[],[f50,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK9(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f50,plain,(
    ! [X0,X5,X3] :
      ( r2_hidden(X5,sK8(X0,X3))
      | ~ r1_tarski(X5,X3)
      | ~ r2_hidden(X3,sK7(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f124,plain,
    ( sP0(sK7(sK5))
    | ~ r1_tarski(sK2(sK7(sK5)),sK7(sK5)) ),
    inference(subsumption_resolution,[],[f123,f120])).

fof(f120,plain,
    ( ~ r2_hidden(sK2(sK7(sK5)),sK7(sK5))
    | sP0(sK7(sK5)) ),
    inference(resolution,[],[f119,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f123,plain,
    ( sP0(sK7(sK5))
    | r2_hidden(sK2(sK7(sK5)),sK7(sK5))
    | ~ r1_tarski(sK2(sK7(sK5)),sK7(sK5)) ),
    inference(resolution,[],[f121,f51])).

fof(f51,plain,(
    ! [X2,X0] :
      ( r2_tarski(X2,sK7(X0))
      | r2_hidden(X2,sK7(X0))
      | ~ r1_tarski(X2,sK7(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f121,plain,
    ( ~ r2_tarski(sK2(sK7(sK5)),sK7(sK5))
    | sP0(sK7(sK5)) ),
    inference(resolution,[],[f119,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ r2_tarski(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f130,plain,(
    ~ sP0(sK7(sK5)) ),
    inference(subsumption_resolution,[],[f129,f128])).

fof(f128,plain,(
    r2_hidden(sK3(sK7(sK5)),sK7(sK5)) ),
    inference(resolution,[],[f125,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( ~ r2_hidden(sK4(X0),X0)
        & r1_tarski(sK4(X0),sK3(X0))
        & r2_hidden(sK3(X0),X0) )
      | ~ sP0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f21,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(X2,X0)
          & r1_tarski(X2,X1)
          & r2_hidden(X1,X0) )
     => ( ~ r2_hidden(sK4(X0),X0)
        & r1_tarski(sK4(X0),sK3(X0))
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(X2,X0)
          & r1_tarski(X2,X1)
          & r2_hidden(X1,X0) )
      | ~ sP0(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X1] :
      ( ? [X4,X5] :
          ( ~ r2_hidden(X5,X1)
          & r1_tarski(X5,X4)
          & r2_hidden(X4,X1) )
      | ~ sP0(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f129,plain,
    ( ~ r2_hidden(sK3(sK7(sK5)),sK7(sK5))
    | ~ sP0(sK7(sK5)) ),
    inference(resolution,[],[f127,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0),sK7(X1))
      | ~ r2_hidden(sK3(X0),sK7(X1))
      | ~ sP0(X0) ) ),
    inference(resolution,[],[f48,f43])).

fof(f43,plain,(
    ! [X0] :
      ( r1_tarski(sK4(X0),sK3(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f127,plain,(
    ~ r2_hidden(sK4(sK7(sK5)),sK7(sK5)) ),
    inference(resolution,[],[f125,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | ~ r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f23])).

%------------------------------------------------------------------------------
