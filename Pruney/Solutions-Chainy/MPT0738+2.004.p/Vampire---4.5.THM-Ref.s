%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 180 expanded)
%              Number of leaves         :   12 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :  197 ( 706 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f133,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f106,f131])).

% (14473)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% (14475)Refutation not found, incomplete strategy% (14475)------------------------------
% (14475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14493)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (14490)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f131,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f127,f110])).

fof(f110,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f46,f93])).

fof(f93,plain,
    ( sK0 = sK1
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl4_3
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f46,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f45,f29])).

fof(f29,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r2_hidden(sK1,sK0)
    & ~ r1_ordinal1(sK0,sK1)
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_hidden(X1,X0)
            & ~ r1_ordinal1(X0,X1)
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ~ r2_hidden(X1,sK0)
          & ~ r1_ordinal1(sK0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( ~ r2_hidden(X1,sK0)
        & ~ r1_ordinal1(sK0,X1)
        & v3_ordinal1(X1) )
   => ( ~ r2_hidden(sK1,sK0)
      & ~ r1_ordinal1(sK0,sK1)
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(X1,X0)
          & ~ r1_ordinal1(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(X1,X0)
          & ~ r1_ordinal1(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
              | r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f45,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f44,f30])).

fof(f30,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f44,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f40,f31])).

fof(f31,plain,(
    ~ r1_ordinal1(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f127,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f111,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f111,plain,
    ( r2_hidden(sK3(sK0,sK0),sK0)
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f47,f93])).

fof(f47,plain,(
    r2_hidden(sK3(sK0,sK1),sK0) ),
    inference(resolution,[],[f46,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f106,plain,(
    ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f104,f30])).

fof(f104,plain,
    ( ~ v3_ordinal1(sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f101,f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f101,plain,
    ( ~ v1_ordinal1(sK1)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f100,f46])).

fof(f100,plain,
    ( r1_tarski(sK0,sK1)
    | ~ v1_ordinal1(sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f97,f36])).

fof(f36,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | r1_tarski(X2,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ( ~ r1_tarski(sK2(X0),X0)
          & r2_hidden(sK2(X0),X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,X0)
          & r2_hidden(X1,X0) )
     => ( ~ r1_tarski(sK2(X0),X0)
        & r2_hidden(sK2(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X2] :
            ( r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_ordinal1(X0)
        | ? [X1] :
            ( ~ r1_tarski(X1,X0)
            & r2_hidden(X1,X0) ) )
      & ( ! [X1] :
            ( r1_tarski(X1,X0)
            | ~ r2_hidden(X1,X0) )
        | ~ v1_ordinal1(X0) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f97,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl4_4
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f98,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f89,f95,f91])).

fof(f89,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f87,f32])).

fof(f32,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f87,plain,
    ( r2_hidden(sK0,sK1)
    | sK0 = sK1
    | r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f84,f30])).

fof(f84,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r2_hidden(sK0,X0)
      | sK0 = X0
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f35,f29])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f11])).

% (14488)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:55:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (14482)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (14479)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (14467)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (14469)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (14468)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (14474)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (14491)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (14470)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (14489)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (14475)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (14481)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (14472)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (14470)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (14471)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (14478)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (14478)Refutation not found, incomplete strategy% (14478)------------------------------
% 0.22/0.55  % (14478)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f133,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f98,f106,f131])).
% 0.22/0.55  % (14473)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (14475)Refutation not found, incomplete strategy% (14475)------------------------------
% 0.22/0.55  % (14475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (14493)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.55  % (14490)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.56  fof(f131,plain,(
% 0.22/0.56    ~spl4_3),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f130])).
% 0.22/0.56  fof(f130,plain,(
% 0.22/0.56    $false | ~spl4_3),
% 0.22/0.56    inference(subsumption_resolution,[],[f127,f110])).
% 0.22/0.56  fof(f110,plain,(
% 0.22/0.56    ~r1_tarski(sK0,sK0) | ~spl4_3),
% 0.22/0.56    inference(backward_demodulation,[],[f46,f93])).
% 0.22/0.56  fof(f93,plain,(
% 0.22/0.56    sK0 = sK1 | ~spl4_3),
% 0.22/0.56    inference(avatar_component_clause,[],[f91])).
% 0.22/0.56  fof(f91,plain,(
% 0.22/0.56    spl4_3 <=> sK0 = sK1),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    ~r1_tarski(sK0,sK1)),
% 0.22/0.56    inference(subsumption_resolution,[],[f45,f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    v3_ordinal1(sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f19])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    (~r2_hidden(sK1,sK0) & ~r1_ordinal1(sK0,sK1) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f18,f17])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (~r2_hidden(X1,X0) & ~r1_ordinal1(X0,X1) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (~r2_hidden(X1,sK0) & ~r1_ordinal1(sK0,X1) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ? [X1] : (~r2_hidden(X1,sK0) & ~r1_ordinal1(sK0,X1) & v3_ordinal1(X1)) => (~r2_hidden(sK1,sK0) & ~r1_ordinal1(sK0,sK1) & v3_ordinal1(sK1))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f9,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (~r2_hidden(X1,X0) & ~r1_ordinal1(X0,X1) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.56    inference(flattening,[],[f8])).
% 0.22/0.56  fof(f8,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : ((~r2_hidden(X1,X0) & ~r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,negated_conjecture,(
% 0.22/0.56    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.22/0.56    inference(negated_conjecture,[],[f6])).
% 0.22/0.56  fof(f6,conjecture,(
% 0.22/0.56    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    ~r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f44,f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    v3_ordinal1(sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f19])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    ~r1_tarski(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0)),
% 0.22/0.56    inference(resolution,[],[f40,f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ~r1_ordinal1(sK0,sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f19])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.56    inference(nnf_transformation,[],[f15])).
% 0.22/0.56  fof(f15,plain,(
% 0.22/0.56    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.56    inference(flattening,[],[f14])).
% 0.22/0.56  fof(f14,plain,(
% 0.22/0.56    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.22/0.56  fof(f127,plain,(
% 0.22/0.56    r1_tarski(sK0,sK0) | ~spl4_3),
% 0.22/0.56    inference(resolution,[],[f111,f43])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.56    inference(rectify,[],[f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.56    inference(nnf_transformation,[],[f16])).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.56  fof(f111,plain,(
% 0.22/0.56    r2_hidden(sK3(sK0,sK0),sK0) | ~spl4_3),
% 0.22/0.56    inference(backward_demodulation,[],[f47,f93])).
% 0.22/0.56  fof(f47,plain,(
% 0.22/0.56    r2_hidden(sK3(sK0,sK1),sK0)),
% 0.22/0.56    inference(resolution,[],[f46,f42])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f28])).
% 0.22/0.56  fof(f106,plain,(
% 0.22/0.56    ~spl4_4),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f105])).
% 0.22/0.56  fof(f105,plain,(
% 0.22/0.56    $false | ~spl4_4),
% 0.22/0.56    inference(subsumption_resolution,[],[f104,f30])).
% 0.22/0.56  fof(f104,plain,(
% 0.22/0.56    ~v3_ordinal1(sK1) | ~spl4_4),
% 0.22/0.56    inference(resolution,[],[f101,f33])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,plain,(
% 0.22/0.56    ! [X0] : ((v2_ordinal1(X0) & v1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_ordinal1)).
% 0.22/0.56  fof(f101,plain,(
% 0.22/0.56    ~v1_ordinal1(sK1) | ~spl4_4),
% 0.22/0.56    inference(subsumption_resolution,[],[f100,f46])).
% 0.22/0.56  fof(f100,plain,(
% 0.22/0.56    r1_tarski(sK0,sK1) | ~v1_ordinal1(sK1) | ~spl4_4),
% 0.22/0.56    inference(resolution,[],[f97,f36])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ( ! [X2,X0] : (~r2_hidden(X2,X0) | r1_tarski(X2,X0) | ~v1_ordinal1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ! [X0] : ((v1_ordinal1(X0) | (~r1_tarski(sK2(X0),X0) & r2_hidden(sK2(X0),X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ! [X0] : (? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0)) => (~r1_tarski(sK2(X0),X0) & r2_hidden(sK2(X0),X0)))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X2] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X0)) | ~v1_ordinal1(X0)))),
% 0.22/0.56    inference(rectify,[],[f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ! [X0] : ((v1_ordinal1(X0) | ? [X1] : (~r1_tarski(X1,X0) & r2_hidden(X1,X0))) & (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0)))),
% 0.22/0.56    inference(nnf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,plain,(
% 0.22/0.56    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).
% 0.22/0.56  fof(f97,plain,(
% 0.22/0.56    r2_hidden(sK0,sK1) | ~spl4_4),
% 0.22/0.56    inference(avatar_component_clause,[],[f95])).
% 0.22/0.56  fof(f95,plain,(
% 0.22/0.56    spl4_4 <=> r2_hidden(sK0,sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.56  fof(f98,plain,(
% 0.22/0.56    spl4_3 | spl4_4),
% 0.22/0.56    inference(avatar_split_clause,[],[f89,f95,f91])).
% 0.22/0.56  fof(f89,plain,(
% 0.22/0.56    r2_hidden(sK0,sK1) | sK0 = sK1),
% 0.22/0.56    inference(subsumption_resolution,[],[f87,f32])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ~r2_hidden(sK1,sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f19])).
% 0.22/0.56  fof(f87,plain,(
% 0.22/0.56    r2_hidden(sK0,sK1) | sK0 = sK1 | r2_hidden(sK1,sK0)),
% 0.22/0.56    inference(resolution,[],[f84,f30])).
% 0.22/0.56  fof(f84,plain,(
% 0.22/0.56    ( ! [X0] : (~v3_ordinal1(X0) | r2_hidden(sK0,X0) | sK0 = X0 | r2_hidden(X0,sK0)) )),
% 0.22/0.56    inference(resolution,[],[f35,f29])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v3_ordinal1(X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | r2_hidden(X1,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f12])).
% 0.22/0.56  fof(f12,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.56    inference(flattening,[],[f11])).
% 0.22/0.56  % (14488)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.56  fof(f11,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).
% 0.22/0.56  % SZS output end Proof for theBenchmark
% 0.22/0.56  % (14470)------------------------------
% 0.22/0.56  % (14470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (14470)Termination reason: Refutation
% 0.22/0.56  
% 0.22/0.56  % (14470)Memory used [KB]: 10746
% 0.22/0.56  % (14470)Time elapsed: 0.136 s
% 0.22/0.56  % (14470)------------------------------
% 0.22/0.56  % (14470)------------------------------
% 0.22/0.56  % (14466)Success in time 0.195 s
%------------------------------------------------------------------------------
