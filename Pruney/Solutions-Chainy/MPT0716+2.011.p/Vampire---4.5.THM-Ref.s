%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 299 expanded)
%              Number of leaves         :   14 ( 100 expanded)
%              Depth                    :   13
%              Number of atoms          :  325 (2144 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f178,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f69,f70,f91,f157,f177])).

fof(f177,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f170,f168])).

fof(f168,plain,
    ( r2_hidden(sK3(sK2,k1_relat_1(sK0)),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl4_1
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f58,f159,f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f159,plain,
    ( r2_hidden(sK3(sK2,k1_relat_1(sK0)),sK2)
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f63,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f63,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl4_2
  <=> r1_tarski(sK2,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f58,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl4_1
  <=> r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f170,plain,
    ( ~ r2_hidden(sK3(sK2,k1_relat_1(sK0)),k1_relat_1(k5_relat_1(sK0,sK1)))
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f39,f40,f37,f38,f160,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
              | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              | ~ r2_hidden(X0,k1_relat_1(X2)) )
            & ( ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
                & r2_hidden(X0,k1_relat_1(X2)) )
              | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).

fof(f160,plain,
    ( ~ r2_hidden(sK3(sK2,k1_relat_1(sK0)),k1_relat_1(sK0))
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f63,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f38,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
      | ~ r1_tarski(sK2,k1_relat_1(sK0))
      | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) )
    & ( ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
        & r1_tarski(sK2,k1_relat_1(sK0)) )
      | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) )
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  | ~ r1_tarski(X2,k1_relat_1(X0))
                  | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
                & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                    & r1_tarski(X2,k1_relat_1(X0)) )
                  | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(sK0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))) )
              & ( ( r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(sK0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

% (21887)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (21877)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% (21887)Refutation not found, incomplete strategy% (21887)------------------------------
% (21887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (21887)Termination reason: Refutation not found, incomplete strategy

% (21887)Memory used [KB]: 10618
% (21887)Time elapsed: 0.138 s
% (21887)------------------------------
% (21887)------------------------------
% (21888)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (21878)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (21873)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f28,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1))
              | ~ r1_tarski(X2,k1_relat_1(sK0))
              | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))) )
            & ( ( r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(sK0)) )
              | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))) ) )
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1))
            | ~ r1_tarski(X2,k1_relat_1(sK0))
            | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))) )
          & ( ( r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1))
              & r1_tarski(X2,k1_relat_1(sK0)) )
            | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))) ) )
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1))
          | ~ r1_tarski(X2,k1_relat_1(sK0))
          | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))) )
        & ( ( r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1))
            & r1_tarski(X2,k1_relat_1(sK0)) )
          | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))) ) )
   => ( ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
        | ~ r1_tarski(sK2,k1_relat_1(sK0))
        | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) )
      & ( ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
          & r1_tarski(sK2,k1_relat_1(sK0)) )
        | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(X0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
              & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                | ~ r1_tarski(X2,k1_relat_1(X0))
                | ~ r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) )
              & ( ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) )
                | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
              <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).

fof(f37,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f40,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f39,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f157,plain,
    ( ~ spl4_1
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | ~ spl4_1
    | spl4_3 ),
    inference(subsumption_resolution,[],[f154,f145])).

fof(f145,plain,
    ( ~ r2_hidden(sK3(k9_relat_1(sK0,sK2),k1_relat_1(sK1)),k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))))
    | spl4_3 ),
    inference(forward_demodulation,[],[f142,f76])).

fof(f76,plain,(
    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f37,f39,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f142,plain,
    ( ~ r2_hidden(sK3(k9_relat_1(sK0,sK2),k1_relat_1(sK1)),k9_relat_1(sK0,k10_relat_1(sK0,k1_relat_1(sK1))))
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f73,f97,f50])).

fof(f97,plain,
    ( ~ r2_hidden(sK3(k9_relat_1(sK0,sK2),k1_relat_1(sK1)),k1_relat_1(sK1))
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f67,f52])).

fof(f67,plain,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl4_3
  <=> r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f73,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK0,k10_relat_1(sK0,X0)),X0) ),
    inference(unit_resulting_resolution,[],[f37,f38,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

fof(f154,plain,
    ( r2_hidden(sK3(k9_relat_1(sK0,sK2),k1_relat_1(sK1)),k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))))
    | ~ spl4_1
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f92,f96,f50])).

fof(f96,plain,
    ( r2_hidden(sK3(k9_relat_1(sK0,sK2),k1_relat_1(sK1)),k9_relat_1(sK0,sK2))
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f67,f51])).

fof(f92,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1))))
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f37,f58,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

fof(f91,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f89,f59])).

fof(f59,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f89,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f85,f76])).

fof(f85,plain,
    ( r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1)))
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f37,f38,f62,f66,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

fof(f66,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f62,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f70,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f41,f61,f57])).

fof(f41,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f69,plain,
    ( spl4_1
    | spl4_3 ),
    inference(avatar_split_clause,[],[f42,f65,f57])).

fof(f42,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f68,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f43,f65,f61,f57])).

fof(f43,plain,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:49:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (21884)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (21876)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (21874)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (21871)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (21872)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (21892)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (21892)Refutation not found, incomplete strategy% (21892)------------------------------
% 0.22/0.53  % (21892)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (21892)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (21892)Memory used [KB]: 10746
% 0.22/0.53  % (21892)Time elapsed: 0.117 s
% 0.22/0.53  % (21892)------------------------------
% 0.22/0.53  % (21892)------------------------------
% 0.22/0.53  % (21870)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (21899)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (21895)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (21875)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (21893)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.54  % (21880)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (21881)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (21879)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (21897)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (21885)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (21886)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (21891)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (21898)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (21896)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (21889)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (21883)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (21894)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (21896)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f178,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f68,f69,f70,f91,f157,f177])).
% 0.22/0.55  fof(f177,plain,(
% 0.22/0.55    ~spl4_1 | spl4_2),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f176])).
% 0.22/0.55  fof(f176,plain,(
% 0.22/0.55    $false | (~spl4_1 | spl4_2)),
% 0.22/0.55    inference(subsumption_resolution,[],[f170,f168])).
% 0.22/0.55  fof(f168,plain,(
% 0.22/0.55    r2_hidden(sK3(sK2,k1_relat_1(sK0)),k1_relat_1(k5_relat_1(sK0,sK1))) | (~spl4_1 | spl4_2)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f58,f159,f50])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f36])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f34,f35])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.55    inference(rectify,[],[f33])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.55    inference(nnf_transformation,[],[f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.55  fof(f159,plain,(
% 0.22/0.55    r2_hidden(sK3(sK2,k1_relat_1(sK0)),sK2) | spl4_2),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f63,f51])).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f36])).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    ~r1_tarski(sK2,k1_relat_1(sK0)) | spl4_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f61])).
% 0.22/0.55  fof(f61,plain,(
% 0.22/0.55    spl4_2 <=> r1_tarski(sK2,k1_relat_1(sK0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.55  fof(f58,plain,(
% 0.22/0.55    r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | ~spl4_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f57])).
% 0.22/0.55  fof(f57,plain,(
% 0.22/0.55    spl4_1 <=> r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.55  fof(f170,plain,(
% 0.22/0.55    ~r2_hidden(sK3(sK2,k1_relat_1(sK0)),k1_relat_1(k5_relat_1(sK0,sK1))) | spl4_2),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f39,f40,f37,f38,f160,f47])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f32])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ! [X0,X1] : (! [X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | ~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(flattening,[],[f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ! [X0,X1] : (! [X2] : (((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) | (~r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(nnf_transformation,[],[f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.55    inference(flattening,[],[f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ! [X0,X1] : (! [X2] : ((r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) <=> (r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X2))))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_1)).
% 0.22/0.55  fof(f160,plain,(
% 0.22/0.55    ~r2_hidden(sK3(sK2,k1_relat_1(sK0)),k1_relat_1(sK0)) | spl4_2),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f63,f52])).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK3(X0,X1),X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f36])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    v1_funct_1(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    (((~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) & r1_tarski(sK2,k1_relat_1(sK0))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))))) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  % (21887)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.56  % (21877)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.56  % (21887)Refutation not found, incomplete strategy% (21887)------------------------------
% 0.22/0.56  % (21887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (21887)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (21887)Memory used [KB]: 10618
% 0.22/0.56  % (21887)Time elapsed: 0.138 s
% 0.22/0.56  % (21887)------------------------------
% 0.22/0.56  % (21887)------------------------------
% 0.22/0.56  % (21888)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.56  % (21878)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.57  % (21873)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.57  fof(f28,plain,(
% 0.22/0.57    ? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) => (? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))))) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f29,plain,(
% 0.22/0.57    ? [X2] : ((~r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1)) | ~r1_tarski(X2,k1_relat_1(sK0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,X2),k1_relat_1(sK1)) & r1_tarski(X2,k1_relat_1(sK0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(sK0,sK1))))) => ((~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))) & ((r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) & r1_tarski(sK2,k1_relat_1(sK0))) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f26,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0)) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.57    inference(flattening,[],[f25])).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : (? [X2] : (((~r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) | ~r1_tarski(X2,k1_relat_1(X0))) | ~r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))) & ((r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))) | r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.57    inference(nnf_transformation,[],[f12])).
% 0.22/0.57  fof(f12,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.57    inference(flattening,[],[f11])).
% 0.22/0.57  fof(f11,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f10])).
% 0.22/0.57  fof(f10,negated_conjecture,(
% 0.22/0.57    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 0.22/0.57    inference(negated_conjecture,[],[f9])).
% 0.22/0.57  fof(f9,conjecture,(
% 0.22/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).
% 0.22/0.57  fof(f37,plain,(
% 0.22/0.57    v1_relat_1(sK0)),
% 0.22/0.57    inference(cnf_transformation,[],[f30])).
% 0.22/0.57  fof(f40,plain,(
% 0.22/0.57    v1_funct_1(sK1)),
% 0.22/0.57    inference(cnf_transformation,[],[f30])).
% 0.22/0.57  fof(f39,plain,(
% 0.22/0.57    v1_relat_1(sK1)),
% 0.22/0.57    inference(cnf_transformation,[],[f30])).
% 0.22/0.57  fof(f157,plain,(
% 0.22/0.57    ~spl4_1 | spl4_3),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f156])).
% 0.22/0.57  fof(f156,plain,(
% 0.22/0.57    $false | (~spl4_1 | spl4_3)),
% 0.22/0.57    inference(subsumption_resolution,[],[f154,f145])).
% 0.22/0.57  fof(f145,plain,(
% 0.22/0.57    ~r2_hidden(sK3(k9_relat_1(sK0,sK2),k1_relat_1(sK1)),k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1)))) | spl4_3),
% 0.22/0.57    inference(forward_demodulation,[],[f142,f76])).
% 0.22/0.57  fof(f76,plain,(
% 0.22/0.57    k1_relat_1(k5_relat_1(sK0,sK1)) = k10_relat_1(sK0,k1_relat_1(sK1))),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f37,f39,f44])).
% 0.22/0.57  fof(f44,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f13])).
% 0.22/0.57  fof(f13,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f5])).
% 0.22/0.57  fof(f5,axiom,(
% 0.22/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.22/0.57  fof(f142,plain,(
% 0.22/0.57    ~r2_hidden(sK3(k9_relat_1(sK0,sK2),k1_relat_1(sK1)),k9_relat_1(sK0,k10_relat_1(sK0,k1_relat_1(sK1)))) | spl4_3),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f73,f97,f50])).
% 0.22/0.57  fof(f97,plain,(
% 0.22/0.57    ~r2_hidden(sK3(k9_relat_1(sK0,sK2),k1_relat_1(sK1)),k1_relat_1(sK1)) | spl4_3),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f67,f52])).
% 0.22/0.57  fof(f67,plain,(
% 0.22/0.57    ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | spl4_3),
% 0.22/0.57    inference(avatar_component_clause,[],[f65])).
% 0.22/0.57  fof(f65,plain,(
% 0.22/0.57    spl4_3 <=> r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.57  fof(f73,plain,(
% 0.22/0.57    ( ! [X0] : (r1_tarski(k9_relat_1(sK0,k10_relat_1(sK0,X0)),X0)) )),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f37,f38,f46])).
% 0.22/0.57  fof(f46,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f16])).
% 0.22/0.57  fof(f16,plain,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.57    inference(flattening,[],[f15])).
% 0.22/0.57  fof(f15,plain,(
% 0.22/0.57    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.57    inference(ennf_transformation,[],[f6])).
% 0.22/0.57  fof(f6,axiom,(
% 0.22/0.57    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).
% 0.22/0.57  fof(f154,plain,(
% 0.22/0.57    r2_hidden(sK3(k9_relat_1(sK0,sK2),k1_relat_1(sK1)),k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1)))) | (~spl4_1 | spl4_3)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f92,f96,f50])).
% 0.22/0.57  fof(f96,plain,(
% 0.22/0.57    r2_hidden(sK3(k9_relat_1(sK0,sK2),k1_relat_1(sK1)),k9_relat_1(sK0,sK2)) | spl4_3),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f67,f51])).
% 0.22/0.57  fof(f92,plain,(
% 0.22/0.57    r1_tarski(k9_relat_1(sK0,sK2),k9_relat_1(sK0,k1_relat_1(k5_relat_1(sK0,sK1)))) | ~spl4_1),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f37,f58,f53])).
% 0.22/0.57  fof(f53,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f21])).
% 0.22/0.57  fof(f21,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.57    inference(flattening,[],[f20])).
% 0.22/0.57  fof(f20,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.57    inference(ennf_transformation,[],[f4])).
% 0.22/0.57  fof(f4,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).
% 0.22/0.57  fof(f91,plain,(
% 0.22/0.57    spl4_1 | ~spl4_2 | ~spl4_3),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f90])).
% 0.22/0.57  fof(f90,plain,(
% 0.22/0.57    $false | (spl4_1 | ~spl4_2 | ~spl4_3)),
% 0.22/0.57    inference(subsumption_resolution,[],[f89,f59])).
% 0.22/0.57  fof(f59,plain,(
% 0.22/0.57    ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | spl4_1),
% 0.22/0.57    inference(avatar_component_clause,[],[f57])).
% 0.22/0.57  fof(f89,plain,(
% 0.22/0.57    r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | (~spl4_2 | ~spl4_3)),
% 0.22/0.57    inference(forward_demodulation,[],[f85,f76])).
% 0.22/0.57  fof(f85,plain,(
% 0.22/0.57    r1_tarski(sK2,k10_relat_1(sK0,k1_relat_1(sK1))) | (~spl4_2 | ~spl4_3)),
% 0.22/0.57    inference(unit_resulting_resolution,[],[f37,f38,f62,f66,f55])).
% 0.22/0.57  fof(f55,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f24])).
% 0.22/0.57  fof(f24,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.57    inference(flattening,[],[f23])).
% 0.22/0.57  fof(f23,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.57    inference(ennf_transformation,[],[f7])).
% 0.22/0.57  fof(f7,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).
% 0.22/0.57  fof(f66,plain,(
% 0.22/0.57    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~spl4_3),
% 0.22/0.57    inference(avatar_component_clause,[],[f65])).
% 0.22/0.57  fof(f62,plain,(
% 0.22/0.57    r1_tarski(sK2,k1_relat_1(sK0)) | ~spl4_2),
% 0.22/0.57    inference(avatar_component_clause,[],[f61])).
% 0.22/0.57  fof(f70,plain,(
% 0.22/0.57    spl4_1 | spl4_2),
% 0.22/0.57    inference(avatar_split_clause,[],[f41,f61,f57])).
% 0.22/0.57  fof(f41,plain,(
% 0.22/0.57    r1_tarski(sK2,k1_relat_1(sK0)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 0.22/0.57    inference(cnf_transformation,[],[f30])).
% 0.22/0.57  fof(f69,plain,(
% 0.22/0.57    spl4_1 | spl4_3),
% 0.22/0.57    inference(avatar_split_clause,[],[f42,f65,f57])).
% 0.22/0.57  fof(f42,plain,(
% 0.22/0.57    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 0.22/0.57    inference(cnf_transformation,[],[f30])).
% 0.22/0.57  fof(f68,plain,(
% 0.22/0.57    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.22/0.57    inference(avatar_split_clause,[],[f43,f65,f61,f57])).
% 0.22/0.57  fof(f43,plain,(
% 0.22/0.57    ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 0.22/0.57    inference(cnf_transformation,[],[f30])).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (21896)------------------------------
% 0.22/0.57  % (21896)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (21896)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (21896)Memory used [KB]: 10874
% 0.22/0.57  % (21896)Time elapsed: 0.145 s
% 0.22/0.57  % (21896)------------------------------
% 0.22/0.57  % (21896)------------------------------
% 0.22/0.57  % (21869)Success in time 0.206 s
%------------------------------------------------------------------------------
