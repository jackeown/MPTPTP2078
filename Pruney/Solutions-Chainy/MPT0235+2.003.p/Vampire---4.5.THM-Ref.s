%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 179 expanded)
%              Number of leaves         :   18 (  59 expanded)
%              Depth                    :   10
%              Number of atoms          :  340 ( 701 expanded)
%              Number of equality atoms :  132 ( 284 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f421,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f108,f127,f146,f266,f304,f345,f414,f420])).

fof(f420,plain,
    ( spl5_4
    | ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f418])).

fof(f418,plain,
    ( $false
    | spl5_4
    | ~ spl5_7 ),
    inference(resolution,[],[f415,f33])).

fof(f33,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f415,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_tarski(sK1,sK1))
    | spl5_4
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f101,f126])).

fof(f126,plain,
    ( k1_xboole_0 = sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl5_7
  <=> k1_xboole_0 = sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f101,plain,
    ( ~ r1_tarski(sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1))),k2_tarski(sK1,sK1))
    | spl5_4 ),
    inference(resolution,[],[f94,f60])).

fof(f60,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK3(X0,X1),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r1_tarski(sK3(X0,X1),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK3(X0,X1),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( r1_tarski(sK3(X0,X1),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

% (10032)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% (10032)Refutation not found, incomplete strategy% (10032)------------------------------
% (10032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10046)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (10036)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (10058)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (10049)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (10034)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% (10049)Refutation not found, incomplete strategy% (10049)------------------------------
% (10049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10042)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% (10049)Termination reason: Refutation not found, incomplete strategy

% (10049)Memory used [KB]: 1663
% (10049)Time elapsed: 0.105 s
% (10049)------------------------------
% (10049)------------------------------
% (10041)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (10033)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% (10048)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (10032)Termination reason: Refutation not found, incomplete strategy

% (10032)Memory used [KB]: 6140
% (10032)Time elapsed: 0.130 s
% (10032)------------------------------
% (10032)------------------------------
% (10035)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% (10043)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (10045)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (10027)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

% (10057)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f94,plain,
    ( ~ r2_hidden(sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1))),k1_zfmisc_1(k2_tarski(sK1,sK1)))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl5_4
  <=> r2_hidden(sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1))),k1_zfmisc_1(k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f414,plain,
    ( spl5_3
    | ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f413])).

fof(f413,plain,
    ( $false
    | spl5_3
    | ~ spl5_7 ),
    inference(resolution,[],[f396,f64])).

fof(f64,plain,(
    ! [X0,X1] : sP0(X1,X0,k2_tarski(X0,X1)) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f3,f13])).

fof(f13,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f396,plain,
    ( ! [X0] : ~ sP0(X0,k1_xboole_0,k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)))
    | spl5_3
    | ~ spl5_7 ),
    inference(resolution,[],[f351,f63])).

fof(f63,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | ~ sP0(X0,X4,X2) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( sK4(X0,X1,X2) != X0
              & sK4(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X0
            | sK4(X0,X1,X2) = X1
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X0
            & sK4(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X0
          | sK4(X0,X1,X2) = X1
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ( X0 != X3
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X0 = X3
              | X1 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f351,plain,
    ( ~ r2_hidden(k1_xboole_0,k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)))
    | spl5_3
    | ~ spl5_7 ),
    inference(backward_demodulation,[],[f90,f126])).

fof(f90,plain,
    ( ~ r2_hidden(sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1))),k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl5_3
  <=> r2_hidden(sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1))),k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f345,plain,
    ( spl5_3
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f344])).

fof(f344,plain,
    ( $false
    | spl5_3
    | ~ spl5_6 ),
    inference(resolution,[],[f315,f64])).

fof(f315,plain,
    ( ! [X1] : ~ sP0(k2_tarski(sK1,sK1),X1,k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)))
    | spl5_3
    | ~ spl5_6 ),
    inference(resolution,[],[f306,f62])).

fof(f62,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | ~ sP0(X4,X1,X2) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f306,plain,
    ( ~ r2_hidden(k2_tarski(sK1,sK1),k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)))
    | spl5_3
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f90,f122])).

fof(f122,plain,
    ( k2_tarski(sK1,sK1) = sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1)))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl5_6
  <=> k2_tarski(sK1,sK1) = sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f304,plain,
    ( spl5_4
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f298])).

fof(f298,plain,
    ( $false
    | spl5_4
    | ~ spl5_6 ),
    inference(resolution,[],[f287,f56])).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f35,f34])).

fof(f34,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f287,plain,
    ( ~ r1_tarski(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1))
    | spl5_4
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f101,f122])).

fof(f266,plain,
    ( spl5_7
    | spl5_6
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f255,f92,f120,f124])).

fof(f255,plain,
    ( k2_tarski(sK1,sK1) = sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1)))
    | k1_xboole_0 = sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1)))
    | ~ spl5_4 ),
    inference(duplicate_literal_removal,[],[f252])).

fof(f252,plain,
    ( k2_tarski(sK1,sK1) = sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1)))
    | k1_xboole_0 = sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1)))
    | k2_tarski(sK1,sK1) = sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1)))
    | k2_tarski(sK1,sK1) = sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1)))
    | ~ spl5_4 ),
    inference(resolution,[],[f234,f93])).

fof(f93,plain,
    ( r2_hidden(sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1))),k1_zfmisc_1(k2_tarski(sK1,sK1)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f234,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_zfmisc_1(k2_tarski(X2,X0)))
      | k2_tarski(X2,X2) = X1
      | k1_xboole_0 = X1
      | k2_tarski(X2,X0) = X1
      | k2_tarski(X0,X0) = X1 ) ),
    inference(resolution,[],[f59,f61])).

fof(f61,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_tarski(X1,X2))
      | k2_tarski(X2,X2) = X0
      | k2_tarski(X1,X1) = X0
      | k1_xboole_0 = X0
      | k2_tarski(X1,X2) = X0 ) ),
    inference(definition_unfolding,[],[f50,f34,f34])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f146,plain,(
    ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | ~ spl5_5 ),
    inference(trivial_inequality_removal,[],[f139])).

fof(f139,plain,
    ( k1_zfmisc_1(k2_tarski(sK1,sK1)) != k1_zfmisc_1(k2_tarski(sK1,sK1))
    | ~ spl5_5 ),
    inference(superposition,[],[f55,f107])).

fof(f107,plain,
    ( k1_zfmisc_1(k2_tarski(sK1,sK1)) = k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl5_5
  <=> k1_zfmisc_1(k2_tarski(sK1,sK1)) = k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f55,plain,(
    k1_zfmisc_1(k2_tarski(sK1,sK1)) != k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)) ),
    inference(definition_unfolding,[],[f32,f34,f34])).

fof(f32,plain,(
    k1_zfmisc_1(k1_tarski(sK1)) != k2_tarski(k1_xboole_0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k1_zfmisc_1(k1_tarski(sK1)) != k2_tarski(k1_xboole_0,k1_tarski(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f15])).

fof(f15,plain,
    ( ? [X0] : k1_zfmisc_1(k1_tarski(X0)) != k2_tarski(k1_xboole_0,k1_tarski(X0))
   => k1_zfmisc_1(k1_tarski(sK1)) != k2_tarski(k1_xboole_0,k1_tarski(sK1)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] : k1_zfmisc_1(k1_tarski(X0)) != k2_tarski(k1_xboole_0,k1_tarski(X0)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] : k1_zfmisc_1(k1_tarski(X0)) = k2_tarski(k1_xboole_0,k1_tarski(X0)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] : k1_zfmisc_1(k1_tarski(X0)) = k2_tarski(k1_xboole_0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_zfmisc_1)).

fof(f127,plain,
    ( spl5_6
    | spl5_7
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f117,f88,f124,f120])).

% (10044)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (10028)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% (10055)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (10048)Refutation not found, incomplete strategy% (10048)------------------------------
% (10048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10048)Termination reason: Refutation not found, incomplete strategy

% (10048)Memory used [KB]: 10618
% (10048)Time elapsed: 0.153 s
% (10048)------------------------------
% (10048)------------------------------
% (10052)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f117,plain,
    ( k1_xboole_0 = sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1)))
    | k2_tarski(sK1,sK1) = sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1)))
    | ~ spl5_3 ),
    inference(resolution,[],[f110,f89])).

fof(f89,plain,
    ( r2_hidden(sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1))),k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k2_tarski(X0,X2))
      | X0 = X1
      | X1 = X2 ) ),
    inference(resolution,[],[f42,f64])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | X1 = X4
      | ~ r2_hidden(X4,X2)
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f108,plain,
    ( spl5_3
    | spl5_5
    | spl5_4 ),
    inference(avatar_split_clause,[],[f100,f92,f105,f88])).

fof(f100,plain,
    ( k1_zfmisc_1(k2_tarski(sK1,sK1)) = k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1))
    | r2_hidden(sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1))),k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)))
    | spl5_4 ),
    inference(resolution,[],[f94,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1),X1)
          | ~ r2_hidden(sK2(X0,X1),X0) )
        & ( r2_hidden(sK2(X0,X1),X1)
          | r2_hidden(sK2(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

% (10036)Refutation not found, incomplete strategy% (10036)------------------------------
% (10036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10036)Termination reason: Refutation not found, incomplete strategy

% (10036)Memory used [KB]: 10618
% (10036)Time elapsed: 0.147 s
% (10036)------------------------------
% (10036)------------------------------
fof(f95,plain,
    ( ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f72,f92,f88])).

fof(f72,plain,
    ( ~ r2_hidden(sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1))),k1_zfmisc_1(k2_tarski(sK1,sK1)))
    | ~ r2_hidden(sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1))),k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1))) ),
    inference(extensionality_resolution,[],[f37,f55])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | X0 = X1
      | ~ r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:22:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.52  % (10040)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (10030)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (10039)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (10047)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (10037)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (10040)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f421,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f95,f108,f127,f146,f266,f304,f345,f414,f420])).
% 0.21/0.54  fof(f420,plain,(
% 0.21/0.54    spl5_4 | ~spl5_7),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f418])).
% 0.21/0.54  fof(f418,plain,(
% 0.21/0.54    $false | (spl5_4 | ~spl5_7)),
% 0.21/0.54    inference(resolution,[],[f415,f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.54  fof(f415,plain,(
% 0.21/0.54    ~r1_tarski(k1_xboole_0,k2_tarski(sK1,sK1)) | (spl5_4 | ~spl5_7)),
% 0.21/0.54    inference(forward_demodulation,[],[f101,f126])).
% 0.21/0.54  fof(f126,plain,(
% 0.21/0.54    k1_xboole_0 = sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1))) | ~spl5_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f124])).
% 0.21/0.54  fof(f124,plain,(
% 0.21/0.54    spl5_7 <=> k1_xboole_0 = sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    ~r1_tarski(sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1))),k2_tarski(sK1,sK1)) | spl5_4),
% 0.21/0.54    inference(resolution,[],[f94,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK3(X0,X1),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r1_tarski(sK3(X0,X1),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  % (10032)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (10032)Refutation not found, incomplete strategy% (10032)------------------------------
% 0.21/0.54  % (10032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10046)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (10036)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (10058)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (10049)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (10034)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (10049)Refutation not found, incomplete strategy% (10049)------------------------------
% 0.21/0.55  % (10049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (10042)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (10049)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (10049)Memory used [KB]: 1663
% 0.21/0.55  % (10049)Time elapsed: 0.105 s
% 0.21/0.55  % (10049)------------------------------
% 0.21/0.55  % (10049)------------------------------
% 0.21/0.55  % (10041)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (10033)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.54/0.56  % (10048)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.54/0.56  % (10032)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.56  
% 1.54/0.56  % (10032)Memory used [KB]: 6140
% 1.54/0.56  % (10032)Time elapsed: 0.130 s
% 1.54/0.56  % (10032)------------------------------
% 1.54/0.56  % (10032)------------------------------
% 1.54/0.56  % (10035)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.54/0.56  % (10043)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.54/0.56  % (10045)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.54/0.56  % (10027)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.54/0.56  fof(f21,plain,(
% 1.54/0.56    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.54/0.56    inference(rectify,[],[f20])).
% 1.54/0.56  fof(f20,plain,(
% 1.54/0.56    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.54/0.56    inference(nnf_transformation,[],[f5])).
% 1.54/0.56  fof(f5,axiom,(
% 1.54/0.56    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.54/0.56  % (10057)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.54/0.56  fof(f94,plain,(
% 1.54/0.56    ~r2_hidden(sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1))),k1_zfmisc_1(k2_tarski(sK1,sK1))) | spl5_4),
% 1.54/0.56    inference(avatar_component_clause,[],[f92])).
% 1.54/0.56  fof(f92,plain,(
% 1.54/0.56    spl5_4 <=> r2_hidden(sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1))),k1_zfmisc_1(k2_tarski(sK1,sK1)))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.54/0.56  fof(f414,plain,(
% 1.54/0.56    spl5_3 | ~spl5_7),
% 1.54/0.56    inference(avatar_contradiction_clause,[],[f413])).
% 1.54/0.56  fof(f413,plain,(
% 1.54/0.56    $false | (spl5_3 | ~spl5_7)),
% 1.54/0.56    inference(resolution,[],[f396,f64])).
% 1.54/0.56  fof(f64,plain,(
% 1.54/0.56    ( ! [X0,X1] : (sP0(X1,X0,k2_tarski(X0,X1))) )),
% 1.54/0.56    inference(equality_resolution,[],[f48])).
% 1.54/0.56  fof(f48,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 1.54/0.56    inference(cnf_transformation,[],[f29])).
% 1.54/0.56  fof(f29,plain,(
% 1.54/0.56    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 1.54/0.56    inference(nnf_transformation,[],[f14])).
% 1.54/0.56  fof(f14,plain,(
% 1.54/0.56    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.54/0.56    inference(definition_folding,[],[f3,f13])).
% 1.54/0.56  fof(f13,plain,(
% 1.54/0.56    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.54/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.54/0.56  fof(f3,axiom,(
% 1.54/0.56    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.54/0.56  fof(f396,plain,(
% 1.54/0.56    ( ! [X0] : (~sP0(X0,k1_xboole_0,k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)))) ) | (spl5_3 | ~spl5_7)),
% 1.54/0.56    inference(resolution,[],[f351,f63])).
% 1.54/0.56  fof(f63,plain,(
% 1.54/0.56    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | ~sP0(X0,X4,X2)) )),
% 1.54/0.56    inference(equality_resolution,[],[f43])).
% 1.54/0.56  fof(f43,plain,(
% 1.54/0.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | ~sP0(X0,X1,X2)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f28])).
% 1.54/0.56  fof(f28,plain,(
% 1.54/0.56    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((sK4(X0,X1,X2) != X0 & sK4(X0,X1,X2) != X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X0 | sK4(X0,X1,X2) = X1 | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.54/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f27])).
% 1.54/0.56  fof(f27,plain,(
% 1.54/0.56    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK4(X0,X1,X2) != X0 & sK4(X0,X1,X2) != X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (sK4(X0,X1,X2) = X0 | sK4(X0,X1,X2) = X1 | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.54/0.56    introduced(choice_axiom,[])).
% 1.54/0.56  fof(f26,plain,(
% 1.54/0.56    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.54/0.56    inference(rectify,[],[f25])).
% 1.54/0.56  fof(f25,plain,(
% 1.54/0.56    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.54/0.56    inference(flattening,[],[f24])).
% 1.54/0.56  fof(f24,plain,(
% 1.54/0.56    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.54/0.56    inference(nnf_transformation,[],[f13])).
% 1.54/0.56  fof(f351,plain,(
% 1.54/0.56    ~r2_hidden(k1_xboole_0,k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1))) | (spl5_3 | ~spl5_7)),
% 1.54/0.56    inference(backward_demodulation,[],[f90,f126])).
% 1.54/0.56  fof(f90,plain,(
% 1.54/0.56    ~r2_hidden(sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1))),k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1))) | spl5_3),
% 1.54/0.56    inference(avatar_component_clause,[],[f88])).
% 1.54/0.56  fof(f88,plain,(
% 1.54/0.56    spl5_3 <=> r2_hidden(sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1))),k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.54/0.56  fof(f345,plain,(
% 1.54/0.56    spl5_3 | ~spl5_6),
% 1.54/0.56    inference(avatar_contradiction_clause,[],[f344])).
% 1.54/0.56  fof(f344,plain,(
% 1.54/0.56    $false | (spl5_3 | ~spl5_6)),
% 1.54/0.56    inference(resolution,[],[f315,f64])).
% 1.54/0.56  fof(f315,plain,(
% 1.54/0.56    ( ! [X1] : (~sP0(k2_tarski(sK1,sK1),X1,k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)))) ) | (spl5_3 | ~spl5_6)),
% 1.54/0.56    inference(resolution,[],[f306,f62])).
% 1.54/0.56  fof(f62,plain,(
% 1.54/0.56    ( ! [X4,X2,X1] : (r2_hidden(X4,X2) | ~sP0(X4,X1,X2)) )),
% 1.54/0.56    inference(equality_resolution,[],[f44])).
% 1.54/0.56  fof(f44,plain,(
% 1.54/0.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | ~sP0(X0,X1,X2)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f28])).
% 1.54/0.56  fof(f306,plain,(
% 1.54/0.56    ~r2_hidden(k2_tarski(sK1,sK1),k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1))) | (spl5_3 | ~spl5_6)),
% 1.54/0.56    inference(forward_demodulation,[],[f90,f122])).
% 1.54/0.56  fof(f122,plain,(
% 1.54/0.56    k2_tarski(sK1,sK1) = sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1))) | ~spl5_6),
% 1.54/0.56    inference(avatar_component_clause,[],[f120])).
% 1.54/0.56  fof(f120,plain,(
% 1.54/0.56    spl5_6 <=> k2_tarski(sK1,sK1) = sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1)))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.54/0.56  fof(f304,plain,(
% 1.54/0.56    spl5_4 | ~spl5_6),
% 1.54/0.56    inference(avatar_contradiction_clause,[],[f298])).
% 1.54/0.56  fof(f298,plain,(
% 1.54/0.56    $false | (spl5_4 | ~spl5_6)),
% 1.54/0.56    inference(resolution,[],[f287,f56])).
% 1.54/0.56  fof(f56,plain,(
% 1.54/0.56    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1))) )),
% 1.54/0.56    inference(definition_unfolding,[],[f35,f34])).
% 1.54/0.56  fof(f34,plain,(
% 1.54/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f4])).
% 1.54/0.56  fof(f4,axiom,(
% 1.54/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.54/0.56  fof(f35,plain,(
% 1.54/0.56    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f7])).
% 1.54/0.56  fof(f7,axiom,(
% 1.54/0.56    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 1.54/0.56  fof(f287,plain,(
% 1.54/0.56    ~r1_tarski(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1)) | (spl5_4 | ~spl5_6)),
% 1.54/0.56    inference(forward_demodulation,[],[f101,f122])).
% 1.54/0.56  fof(f266,plain,(
% 1.54/0.56    spl5_7 | spl5_6 | ~spl5_4),
% 1.54/0.56    inference(avatar_split_clause,[],[f255,f92,f120,f124])).
% 1.54/0.56  fof(f255,plain,(
% 1.54/0.56    k2_tarski(sK1,sK1) = sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1))) | k1_xboole_0 = sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1))) | ~spl5_4),
% 1.54/0.56    inference(duplicate_literal_removal,[],[f252])).
% 1.54/0.56  fof(f252,plain,(
% 1.54/0.56    k2_tarski(sK1,sK1) = sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1))) | k1_xboole_0 = sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1))) | k2_tarski(sK1,sK1) = sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1))) | k2_tarski(sK1,sK1) = sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1))) | ~spl5_4),
% 1.54/0.56    inference(resolution,[],[f234,f93])).
% 1.54/0.56  fof(f93,plain,(
% 1.54/0.56    r2_hidden(sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1))),k1_zfmisc_1(k2_tarski(sK1,sK1))) | ~spl5_4),
% 1.54/0.56    inference(avatar_component_clause,[],[f92])).
% 1.54/0.56  fof(f234,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X1,k1_zfmisc_1(k2_tarski(X2,X0))) | k2_tarski(X2,X2) = X1 | k1_xboole_0 = X1 | k2_tarski(X2,X0) = X1 | k2_tarski(X0,X0) = X1) )),
% 1.54/0.56    inference(resolution,[],[f59,f61])).
% 1.54/0.56  fof(f61,plain,(
% 1.54/0.56    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 1.54/0.56    inference(equality_resolution,[],[f38])).
% 1.54/0.56  fof(f38,plain,(
% 1.54/0.56    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.54/0.56    inference(cnf_transformation,[],[f23])).
% 1.54/0.56  fof(f59,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_tarski(X1,X2)) | k2_tarski(X2,X2) = X0 | k2_tarski(X1,X1) = X0 | k1_xboole_0 = X0 | k2_tarski(X1,X2) = X0) )),
% 1.54/0.56    inference(definition_unfolding,[],[f50,f34,f34])).
% 1.54/0.56  fof(f50,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f31])).
% 1.54/0.56  fof(f31,plain,(
% 1.54/0.56    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 1.54/0.56    inference(flattening,[],[f30])).
% 1.54/0.56  fof(f30,plain,(
% 1.54/0.56    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 1.54/0.56    inference(nnf_transformation,[],[f12])).
% 1.54/0.56  fof(f12,plain,(
% 1.54/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.54/0.56    inference(ennf_transformation,[],[f6])).
% 1.54/0.56  fof(f6,axiom,(
% 1.54/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 1.54/0.56  fof(f146,plain,(
% 1.54/0.56    ~spl5_5),
% 1.54/0.56    inference(avatar_contradiction_clause,[],[f145])).
% 1.54/0.56  fof(f145,plain,(
% 1.54/0.56    $false | ~spl5_5),
% 1.54/0.56    inference(trivial_inequality_removal,[],[f139])).
% 1.54/0.56  fof(f139,plain,(
% 1.54/0.56    k1_zfmisc_1(k2_tarski(sK1,sK1)) != k1_zfmisc_1(k2_tarski(sK1,sK1)) | ~spl5_5),
% 1.54/0.56    inference(superposition,[],[f55,f107])).
% 1.54/0.56  fof(f107,plain,(
% 1.54/0.56    k1_zfmisc_1(k2_tarski(sK1,sK1)) = k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)) | ~spl5_5),
% 1.54/0.56    inference(avatar_component_clause,[],[f105])).
% 1.54/0.56  fof(f105,plain,(
% 1.54/0.56    spl5_5 <=> k1_zfmisc_1(k2_tarski(sK1,sK1)) = k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.54/0.56  fof(f55,plain,(
% 1.54/0.56    k1_zfmisc_1(k2_tarski(sK1,sK1)) != k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1))),
% 1.54/0.56    inference(definition_unfolding,[],[f32,f34,f34])).
% 1.54/0.56  fof(f32,plain,(
% 1.54/0.56    k1_zfmisc_1(k1_tarski(sK1)) != k2_tarski(k1_xboole_0,k1_tarski(sK1))),
% 1.54/0.56    inference(cnf_transformation,[],[f16])).
% 1.54/0.56  fof(f16,plain,(
% 1.54/0.56    k1_zfmisc_1(k1_tarski(sK1)) != k2_tarski(k1_xboole_0,k1_tarski(sK1))),
% 1.54/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f15])).
% 1.54/0.56  fof(f15,plain,(
% 1.54/0.56    ? [X0] : k1_zfmisc_1(k1_tarski(X0)) != k2_tarski(k1_xboole_0,k1_tarski(X0)) => k1_zfmisc_1(k1_tarski(sK1)) != k2_tarski(k1_xboole_0,k1_tarski(sK1))),
% 1.54/0.56    introduced(choice_axiom,[])).
% 1.54/0.56  fof(f10,plain,(
% 1.54/0.56    ? [X0] : k1_zfmisc_1(k1_tarski(X0)) != k2_tarski(k1_xboole_0,k1_tarski(X0))),
% 1.54/0.56    inference(ennf_transformation,[],[f9])).
% 1.54/0.56  fof(f9,negated_conjecture,(
% 1.54/0.56    ~! [X0] : k1_zfmisc_1(k1_tarski(X0)) = k2_tarski(k1_xboole_0,k1_tarski(X0))),
% 1.54/0.56    inference(negated_conjecture,[],[f8])).
% 1.54/0.56  fof(f8,conjecture,(
% 1.54/0.56    ! [X0] : k1_zfmisc_1(k1_tarski(X0)) = k2_tarski(k1_xboole_0,k1_tarski(X0))),
% 1.54/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_zfmisc_1)).
% 1.54/0.56  fof(f127,plain,(
% 1.54/0.56    spl5_6 | spl5_7 | ~spl5_3),
% 1.54/0.56    inference(avatar_split_clause,[],[f117,f88,f124,f120])).
% 1.54/0.56  % (10044)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.54/0.56  % (10028)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.54/0.56  % (10055)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.54/0.56  % (10048)Refutation not found, incomplete strategy% (10048)------------------------------
% 1.54/0.56  % (10048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.56  % (10048)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.56  
% 1.54/0.56  % (10048)Memory used [KB]: 10618
% 1.54/0.56  % (10048)Time elapsed: 0.153 s
% 1.54/0.56  % (10048)------------------------------
% 1.54/0.56  % (10048)------------------------------
% 1.54/0.56  % (10052)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.54/0.57  fof(f117,plain,(
% 1.54/0.57    k1_xboole_0 = sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1))) | k2_tarski(sK1,sK1) = sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1))) | ~spl5_3),
% 1.54/0.57    inference(resolution,[],[f110,f89])).
% 1.54/0.57  fof(f89,plain,(
% 1.54/0.57    r2_hidden(sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1))),k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1))) | ~spl5_3),
% 1.54/0.57    inference(avatar_component_clause,[],[f88])).
% 1.54/0.57  fof(f110,plain,(
% 1.54/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X1,k2_tarski(X0,X2)) | X0 = X1 | X1 = X2) )),
% 1.54/0.57    inference(resolution,[],[f42,f64])).
% 1.54/0.57  fof(f42,plain,(
% 1.54/0.57    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | X1 = X4 | ~r2_hidden(X4,X2) | X0 = X4) )),
% 1.54/0.57    inference(cnf_transformation,[],[f28])).
% 1.54/0.57  fof(f108,plain,(
% 1.54/0.57    spl5_3 | spl5_5 | spl5_4),
% 1.54/0.57    inference(avatar_split_clause,[],[f100,f92,f105,f88])).
% 1.54/0.57  fof(f100,plain,(
% 1.54/0.57    k1_zfmisc_1(k2_tarski(sK1,sK1)) = k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)) | r2_hidden(sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1))),k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1))) | spl5_4),
% 1.54/0.57    inference(resolution,[],[f94,f36])).
% 1.54/0.57  fof(f36,plain,(
% 1.54/0.57    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | X0 = X1 | r2_hidden(sK2(X0,X1),X0)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f19])).
% 1.54/0.57  fof(f19,plain,(
% 1.54/0.57    ! [X0,X1] : (X0 = X1 | ((~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0)) & (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0))))),
% 1.54/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f18])).
% 1.54/0.57  fof(f18,plain,(
% 1.54/0.57    ! [X1,X0] : (? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))) => ((~r2_hidden(sK2(X0,X1),X1) | ~r2_hidden(sK2(X0,X1),X0)) & (r2_hidden(sK2(X0,X1),X1) | r2_hidden(sK2(X0,X1),X0))))),
% 1.54/0.57    introduced(choice_axiom,[])).
% 1.54/0.57  fof(f17,plain,(
% 1.54/0.57    ! [X0,X1] : (X0 = X1 | ? [X2] : ((~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) & (r2_hidden(X2,X1) | r2_hidden(X2,X0))))),
% 1.54/0.57    inference(nnf_transformation,[],[f11])).
% 1.54/0.57  fof(f11,plain,(
% 1.54/0.57    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.54/0.57    inference(ennf_transformation,[],[f1])).
% 1.54/0.57  fof(f1,axiom,(
% 1.54/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.54/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).
% 1.54/0.57  % (10036)Refutation not found, incomplete strategy% (10036)------------------------------
% 1.54/0.57  % (10036)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (10036)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.57  
% 1.54/0.57  % (10036)Memory used [KB]: 10618
% 1.54/0.57  % (10036)Time elapsed: 0.147 s
% 1.54/0.57  % (10036)------------------------------
% 1.54/0.57  % (10036)------------------------------
% 1.54/0.57  fof(f95,plain,(
% 1.54/0.57    ~spl5_3 | ~spl5_4),
% 1.54/0.57    inference(avatar_split_clause,[],[f72,f92,f88])).
% 1.54/0.57  fof(f72,plain,(
% 1.54/0.57    ~r2_hidden(sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1))),k1_zfmisc_1(k2_tarski(sK1,sK1))) | ~r2_hidden(sK2(k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)),k1_zfmisc_1(k2_tarski(sK1,sK1))),k2_tarski(k1_xboole_0,k2_tarski(sK1,sK1)))),
% 1.54/0.57    inference(extensionality_resolution,[],[f37,f55])).
% 1.54/0.57  fof(f37,plain,(
% 1.54/0.57    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | X0 = X1 | ~r2_hidden(sK2(X0,X1),X0)) )),
% 1.54/0.57    inference(cnf_transformation,[],[f19])).
% 1.54/0.57  % SZS output end Proof for theBenchmark
% 1.54/0.57  % (10040)------------------------------
% 1.54/0.57  % (10040)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (10040)Termination reason: Refutation
% 1.54/0.57  
% 1.54/0.57  % (10040)Memory used [KB]: 6396
% 1.54/0.57  % (10040)Time elapsed: 0.108 s
% 1.54/0.57  % (10040)------------------------------
% 1.54/0.57  % (10040)------------------------------
% 1.54/0.57  % (10026)Success in time 0.209 s
%------------------------------------------------------------------------------
