%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:34 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 138 expanded)
%              Number of leaves         :   20 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :  262 ( 446 expanded)
%              Number of equality atoms :   96 ( 177 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f166,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f72,f78,f123,f130,f141,f159,f165])).

fof(f165,plain,
    ( spl1_2
    | ~ spl1_8 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | spl1_2
    | ~ spl1_8 ),
    inference(unit_resulting_resolution,[],[f79,f67,f160,f82])).

fof(f82,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,k2_tarski(X3,X3))
      | r2_hidden(X3,X2)
      | k1_xboole_0 = X2 ) ),
    inference(superposition,[],[f50,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_tarski(X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f48,f45])).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f160,plain,
    ( ! [X0,X1] : r1_tarski(k1_relat_1(k1_xboole_0),k2_tarski(X0,X1))
    | ~ spl1_8 ),
    inference(resolution,[],[f158,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).

fof(f158,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ v1_relat_1(k2_tarski(k4_tarski(X4,X6),k4_tarski(X5,X7)))
        | r1_tarski(k1_relat_1(k1_xboole_0),k2_tarski(X4,X5)) )
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl1_8
  <=> ! [X5,X7,X4,X6] :
        ( r1_tarski(k1_relat_1(k1_xboole_0),k2_tarski(X4,X5))
        | ~ v1_relat_1(k2_tarski(k4_tarski(X4,X6),k4_tarski(X5,X7))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f67,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl1_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl1_2
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f79,plain,(
    ! [X0,X1] : ~ r2_hidden(k2_tarski(X0,X1),X1) ),
    inference(resolution,[],[f49,f55])).

fof(f55,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK0(X0,X1,X2) != X1
              & sK0(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( sK0(X0,X1,X2) = X1
            | sK0(X0,X1,X2) = X0
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

% (14206)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% (14206)Refutation not found, incomplete strategy% (14206)------------------------------
% (14206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14206)Termination reason: Refutation not found, incomplete strategy

% (14206)Memory used [KB]: 1663
% (14206)Time elapsed: 0.126 s
% (14206)------------------------------
% (14206)------------------------------
% (14222)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% (14222)Refutation not found, incomplete strategy% (14222)------------------------------
% (14222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14208)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% (14212)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% (14229)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% (14220)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% (14214)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% (14221)Refutation not found, incomplete strategy% (14221)------------------------------
% (14221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14229)Refutation not found, incomplete strategy% (14229)------------------------------
% (14229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14221)Termination reason: Refutation not found, incomplete strategy

% (14221)Memory used [KB]: 10618
% (14221)Time elapsed: 0.131 s
% (14221)------------------------------
% (14221)------------------------------
% (14210)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% (14226)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% (14232)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% (14223)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% (14223)Refutation not found, incomplete strategy% (14223)------------------------------
% (14223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14232)Refutation not found, incomplete strategy% (14232)------------------------------
% (14232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14229)Termination reason: Refutation not found, incomplete strategy

% (14229)Memory used [KB]: 10618
% (14229)Time elapsed: 0.129 s
% (14229)------------------------------
% (14229)------------------------------
% (14233)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% (14223)Termination reason: Refutation not found, incomplete strategy

% (14223)Memory used [KB]: 1663
% (14223)Time elapsed: 0.138 s
% (14223)------------------------------
% (14223)------------------------------
% (14234)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% (14234)Refutation not found, incomplete strategy% (14234)------------------------------
% (14234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14234)Termination reason: Refutation not found, incomplete strategy

% (14234)Memory used [KB]: 1663
% (14234)Time elapsed: 0.001 s
% (14234)------------------------------
% (14234)------------------------------
% (14232)Termination reason: Refutation not found, incomplete strategy

% (14232)Memory used [KB]: 6140
% (14232)Time elapsed: 0.136 s
% (14232)------------------------------
% (14232)------------------------------
% (14230)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% (14225)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% (14230)Refutation not found, incomplete strategy% (14230)------------------------------
% (14230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14230)Termination reason: Refutation not found, incomplete strategy

% (14230)Memory used [KB]: 6268
% (14230)Time elapsed: 0.139 s
% (14230)------------------------------
% (14230)------------------------------
% (14224)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% (14213)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% (14231)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% (14231)Refutation not found, incomplete strategy% (14231)------------------------------
% (14231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14231)Termination reason: Refutation not found, incomplete strategy

% (14231)Memory used [KB]: 6140
% (14231)Time elapsed: 0.143 s
% (14231)------------------------------
% (14231)------------------------------
% (14222)Termination reason: Refutation not found, incomplete strategy

% (14222)Memory used [KB]: 1663
% (14222)Time elapsed: 0.135 s
% (14222)------------------------------
% (14222)------------------------------
% (14219)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% (14219)Refutation not found, incomplete strategy% (14219)------------------------------
% (14219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14219)Termination reason: Refutation not found, incomplete strategy

% (14219)Memory used [KB]: 1663
% (14219)Time elapsed: 0.152 s
% (14219)------------------------------
% (14219)------------------------------
% (14218)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK0(X0,X1,X2) != X1
            & sK0(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( sK0(X0,X1,X2) = X1
          | sK0(X0,X1,X2) = X0
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
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
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
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
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f159,plain,
    ( spl1_8
    | ~ spl1_4
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f155,f121,f69,f75,f157])).

fof(f75,plain,
    ( spl1_4
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f69,plain,
    ( spl1_3
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f121,plain,
    ( spl1_5
  <=> ! [X1,X3,X0,X2] :
        ( r1_tarski(k2_relat_1(k1_xboole_0),k2_tarski(X0,X1))
        | ~ v1_relat_1(k2_tarski(k4_tarski(X2,X0),k4_tarski(X3,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f155,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ v1_relat_1(k1_xboole_0)
        | r1_tarski(k1_relat_1(k1_xboole_0),k2_tarski(X4,X5))
        | ~ v1_relat_1(k2_tarski(k4_tarski(X4,X6),k4_tarski(X5,X7))) )
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f154,f70])).

fof(f70,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f154,plain,
    ( ! [X6,X4,X7,X5] :
        ( r1_tarski(k1_relat_1(k1_xboole_0),k2_tarski(X4,X5))
        | ~ v1_relat_1(k2_tarski(k4_tarski(X4,X6),k4_tarski(X5,X7)))
        | ~ v1_relat_1(k2_relat_1(k1_xboole_0)) )
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f153,f70])).

fof(f153,plain,
    ( ! [X6,X4,X7,X5] :
        ( r1_tarski(k1_relat_1(k2_relat_1(k1_xboole_0)),k2_tarski(X4,X5))
        | ~ v1_relat_1(k2_tarski(k4_tarski(X4,X6),k4_tarski(X5,X7)))
        | ~ v1_relat_1(k2_relat_1(k1_xboole_0)) )
    | ~ spl1_5 ),
    inference(resolution,[],[f97,f124])).

fof(f124,plain,
    ( ! [X0,X1] : r1_tarski(k2_relat_1(k1_xboole_0),k2_tarski(X0,X1))
    | ~ spl1_5 ),
    inference(resolution,[],[f122,f44])).

fof(f122,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_relat_1(k2_tarski(k4_tarski(X2,X0),k4_tarski(X3,X1)))
        | r1_tarski(k2_relat_1(k1_xboole_0),k2_tarski(X0,X1)) )
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f121])).

fof(f97,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_tarski(X4,k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))
      | r1_tarski(k1_relat_1(X4),k2_tarski(X0,X2))
      | ~ v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f32,f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] : k2_tarski(X0,X2) = k1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(global_subsumption,[],[f44,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tarski(X0,X2) = k1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))
      | ~ v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_relat_1(X4) = k2_tarski(X0,X2)
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_relat_1(X4) = k2_tarski(X1,X3)
        & k1_relat_1(X4) = k2_tarski(X0,X2) )
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_relat_1(X4) = k2_tarski(X1,X3)
        & k1_relat_1(X4) = k2_tarski(X0,X2) )
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( v1_relat_1(X4)
     => ( k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4
       => ( k2_relat_1(X4) = k2_tarski(X1,X3)
          & k1_relat_1(X4) = k2_tarski(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relat_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f141,plain,(
    ~ spl1_6 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | ~ spl1_6 ),
    inference(unit_resulting_resolution,[],[f55,f129,f49])).

fof(f129,plain,
    ( ! [X0] : r2_hidden(X0,k2_relat_1(k1_xboole_0))
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl1_6
  <=> ! [X0] : r2_hidden(X0,k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f130,plain,
    ( spl1_3
    | spl1_6
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f125,f121,f128,f69])).

fof(f125,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_relat_1(k1_xboole_0))
        | k1_xboole_0 = k2_relat_1(k1_xboole_0) )
    | ~ spl1_5 ),
    inference(resolution,[],[f124,f82])).

fof(f123,plain,
    ( ~ spl1_4
    | spl1_5 ),
    inference(avatar_split_clause,[],[f119,f121,f75])).

fof(f119,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_relat_1(k1_xboole_0),k2_tarski(X0,X1))
      | ~ v1_relat_1(k2_tarski(k4_tarski(X2,X0),k4_tarski(X3,X1)))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f94,f42])).

fof(f42,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f94,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_tarski(X4,k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))
      | r1_tarski(k2_relat_1(X4),k2_tarski(X1,X3))
      | ~ v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))
      | ~ v1_relat_1(X4) ) ),
    inference(superposition,[],[f33,f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] : k2_tarski(X1,X3) = k2_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(global_subsumption,[],[f44,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tarski(X1,X3) = k2_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))
      | ~ v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relat_1(X4) = k2_tarski(X1,X3)
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f78,plain,
    ( spl1_4
    | ~ spl1_1 ),
    inference(avatar_split_clause,[],[f73,f60,f75])).

fof(f60,plain,
    ( spl1_1
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f73,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_1 ),
    inference(resolution,[],[f46,f62])).

fof(f62,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f72,plain,
    ( ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f29,f69,f65])).

fof(f29,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f63,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f43,f60])).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:42:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (14207)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.51  % (14227)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.52  % (14215)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.52  % (14217)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.52  % (14217)Refutation not found, incomplete strategy% (14217)------------------------------
% 0.22/0.52  % (14217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (14217)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (14217)Memory used [KB]: 10618
% 0.22/0.52  % (14217)Time elapsed: 0.108 s
% 0.22/0.52  % (14217)------------------------------
% 0.22/0.52  % (14217)------------------------------
% 0.22/0.52  % (14216)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.52  % (14211)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (14216)Refutation not found, incomplete strategy% (14216)------------------------------
% 0.22/0.52  % (14216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (14216)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (14216)Memory used [KB]: 6140
% 0.22/0.52  % (14216)Time elapsed: 0.107 s
% 0.22/0.52  % (14216)------------------------------
% 0.22/0.52  % (14216)------------------------------
% 0.22/0.52  % (14215)Refutation not found, incomplete strategy% (14215)------------------------------
% 0.22/0.52  % (14215)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (14205)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.25/0.53  % (14209)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.25/0.53  % (14228)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.25/0.53  % (14215)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.53  
% 1.25/0.53  % (14215)Memory used [KB]: 10618
% 1.25/0.53  % (14215)Time elapsed: 0.111 s
% 1.25/0.53  % (14215)------------------------------
% 1.25/0.53  % (14215)------------------------------
% 1.25/0.53  % (14221)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.25/0.53  % (14228)Refutation found. Thanks to Tanya!
% 1.25/0.53  % SZS status Theorem for theBenchmark
% 1.25/0.53  % SZS output start Proof for theBenchmark
% 1.25/0.53  fof(f166,plain,(
% 1.25/0.53    $false),
% 1.25/0.53    inference(avatar_sat_refutation,[],[f63,f72,f78,f123,f130,f141,f159,f165])).
% 1.25/0.53  fof(f165,plain,(
% 1.25/0.53    spl1_2 | ~spl1_8),
% 1.25/0.53    inference(avatar_contradiction_clause,[],[f161])).
% 1.25/0.53  fof(f161,plain,(
% 1.25/0.53    $false | (spl1_2 | ~spl1_8)),
% 1.25/0.53    inference(unit_resulting_resolution,[],[f79,f67,f160,f82])).
% 1.25/0.53  fof(f82,plain,(
% 1.25/0.53    ( ! [X2,X3] : (~r1_tarski(X2,k2_tarski(X3,X3)) | r2_hidden(X3,X2) | k1_xboole_0 = X2) )),
% 1.25/0.53    inference(superposition,[],[f50,f41])).
% 1.25/0.53  fof(f41,plain,(
% 1.25/0.53    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f27])).
% 1.25/0.53  fof(f27,plain,(
% 1.25/0.53    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 1.25/0.53    inference(nnf_transformation,[],[f3])).
% 1.25/0.53  fof(f3,axiom,(
% 1.25/0.53    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.25/0.53  fof(f50,plain,(
% 1.25/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k2_tarski(X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 1.25/0.53    inference(definition_unfolding,[],[f48,f45])).
% 1.25/0.53  fof(f45,plain,(
% 1.25/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f6])).
% 1.25/0.53  fof(f6,axiom,(
% 1.25/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.25/0.53  fof(f48,plain,(
% 1.25/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 1.25/0.53    inference(cnf_transformation,[],[f28])).
% 1.25/0.53  fof(f28,plain,(
% 1.25/0.53    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.25/0.53    inference(nnf_transformation,[],[f8])).
% 1.25/0.53  fof(f8,axiom,(
% 1.25/0.53    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.25/0.53  fof(f160,plain,(
% 1.25/0.53    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k1_xboole_0),k2_tarski(X0,X1))) ) | ~spl1_8),
% 1.25/0.53    inference(resolution,[],[f158,f44])).
% 1.25/0.53  fof(f44,plain,(
% 1.25/0.53    ( ! [X2,X0,X3,X1] : (v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 1.25/0.53    inference(cnf_transformation,[],[f10])).
% 1.25/0.53  fof(f10,axiom,(
% 1.25/0.53    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))),
% 1.25/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_relat_1)).
% 1.25/0.53  fof(f158,plain,(
% 1.25/0.53    ( ! [X6,X4,X7,X5] : (~v1_relat_1(k2_tarski(k4_tarski(X4,X6),k4_tarski(X5,X7))) | r1_tarski(k1_relat_1(k1_xboole_0),k2_tarski(X4,X5))) ) | ~spl1_8),
% 1.25/0.53    inference(avatar_component_clause,[],[f157])).
% 1.25/0.53  fof(f157,plain,(
% 1.25/0.53    spl1_8 <=> ! [X5,X7,X4,X6] : (r1_tarski(k1_relat_1(k1_xboole_0),k2_tarski(X4,X5)) | ~v1_relat_1(k2_tarski(k4_tarski(X4,X6),k4_tarski(X5,X7))))),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 1.25/0.53  fof(f67,plain,(
% 1.25/0.53    k1_xboole_0 != k1_relat_1(k1_xboole_0) | spl1_2),
% 1.25/0.53    inference(avatar_component_clause,[],[f65])).
% 1.25/0.53  fof(f65,plain,(
% 1.25/0.53    spl1_2 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.25/0.53    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 1.25/0.53  fof(f79,plain,(
% 1.25/0.53    ( ! [X0,X1] : (~r2_hidden(k2_tarski(X0,X1),X1)) )),
% 1.25/0.53    inference(resolution,[],[f49,f55])).
% 1.25/0.53  fof(f55,plain,(
% 1.25/0.53    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 1.25/0.53    inference(equality_resolution,[],[f54])).
% 1.25/0.53  fof(f54,plain,(
% 1.25/0.53    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 1.25/0.53    inference(equality_resolution,[],[f36])).
% 1.25/0.53  fof(f36,plain,(
% 1.25/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.25/0.53    inference(cnf_transformation,[],[f26])).
% 1.25/0.53  fof(f26,plain,(
% 1.25/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.25/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 1.25/0.53  % (14206)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.25/0.53  % (14206)Refutation not found, incomplete strategy% (14206)------------------------------
% 1.25/0.53  % (14206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  % (14206)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.53  
% 1.25/0.53  % (14206)Memory used [KB]: 1663
% 1.25/0.53  % (14206)Time elapsed: 0.126 s
% 1.25/0.53  % (14206)------------------------------
% 1.25/0.53  % (14206)------------------------------
% 1.25/0.53  % (14222)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.25/0.53  % (14222)Refutation not found, incomplete strategy% (14222)------------------------------
% 1.25/0.53  % (14222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  % (14208)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.25/0.53  % (14212)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.25/0.53  % (14229)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.25/0.54  % (14220)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.25/0.54  % (14214)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.25/0.54  % (14221)Refutation not found, incomplete strategy% (14221)------------------------------
% 1.25/0.54  % (14221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (14229)Refutation not found, incomplete strategy% (14229)------------------------------
% 1.40/0.54  % (14229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (14221)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (14221)Memory used [KB]: 10618
% 1.40/0.54  % (14221)Time elapsed: 0.131 s
% 1.40/0.54  % (14221)------------------------------
% 1.40/0.54  % (14221)------------------------------
% 1.40/0.54  % (14210)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.40/0.54  % (14226)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.40/0.54  % (14232)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.40/0.54  % (14223)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.40/0.54  % (14223)Refutation not found, incomplete strategy% (14223)------------------------------
% 1.40/0.54  % (14223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (14232)Refutation not found, incomplete strategy% (14232)------------------------------
% 1.40/0.54  % (14232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (14229)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (14229)Memory used [KB]: 10618
% 1.40/0.54  % (14229)Time elapsed: 0.129 s
% 1.40/0.54  % (14229)------------------------------
% 1.40/0.54  % (14229)------------------------------
% 1.40/0.54  % (14233)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.40/0.54  % (14223)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (14223)Memory used [KB]: 1663
% 1.40/0.54  % (14223)Time elapsed: 0.138 s
% 1.40/0.54  % (14223)------------------------------
% 1.40/0.54  % (14223)------------------------------
% 1.40/0.54  % (14234)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.40/0.54  % (14234)Refutation not found, incomplete strategy% (14234)------------------------------
% 1.40/0.54  % (14234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (14234)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (14234)Memory used [KB]: 1663
% 1.40/0.54  % (14234)Time elapsed: 0.001 s
% 1.40/0.54  % (14234)------------------------------
% 1.40/0.54  % (14234)------------------------------
% 1.40/0.54  % (14232)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (14232)Memory used [KB]: 6140
% 1.40/0.54  % (14232)Time elapsed: 0.136 s
% 1.40/0.54  % (14232)------------------------------
% 1.40/0.54  % (14232)------------------------------
% 1.40/0.54  % (14230)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.40/0.55  % (14225)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.40/0.55  % (14230)Refutation not found, incomplete strategy% (14230)------------------------------
% 1.40/0.55  % (14230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (14230)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (14230)Memory used [KB]: 6268
% 1.40/0.55  % (14230)Time elapsed: 0.139 s
% 1.40/0.55  % (14230)------------------------------
% 1.40/0.55  % (14230)------------------------------
% 1.40/0.55  % (14224)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.40/0.55  % (14213)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.40/0.55  % (14231)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.40/0.55  % (14231)Refutation not found, incomplete strategy% (14231)------------------------------
% 1.40/0.55  % (14231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (14231)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (14231)Memory used [KB]: 6140
% 1.40/0.55  % (14231)Time elapsed: 0.143 s
% 1.40/0.55  % (14231)------------------------------
% 1.40/0.55  % (14231)------------------------------
% 1.40/0.55  % (14222)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (14222)Memory used [KB]: 1663
% 1.40/0.55  % (14222)Time elapsed: 0.135 s
% 1.40/0.55  % (14222)------------------------------
% 1.40/0.55  % (14222)------------------------------
% 1.40/0.55  % (14219)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.40/0.55  % (14219)Refutation not found, incomplete strategy% (14219)------------------------------
% 1.40/0.55  % (14219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (14219)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (14219)Memory used [KB]: 1663
% 1.40/0.55  % (14219)Time elapsed: 0.152 s
% 1.40/0.55  % (14219)------------------------------
% 1.40/0.55  % (14219)------------------------------
% 1.40/0.55  % (14218)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.40/0.56  fof(f25,plain,(
% 1.40/0.56    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 1.40/0.56    introduced(choice_axiom,[])).
% 1.40/0.56  fof(f24,plain,(
% 1.40/0.56    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.40/0.56    inference(rectify,[],[f23])).
% 1.40/0.56  fof(f23,plain,(
% 1.40/0.56    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.40/0.56    inference(flattening,[],[f22])).
% 1.40/0.56  fof(f22,plain,(
% 1.40/0.56    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.40/0.56    inference(nnf_transformation,[],[f5])).
% 1.40/0.56  fof(f5,axiom,(
% 1.40/0.56    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.40/0.56  fof(f49,plain,(
% 1.40/0.56    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f21])).
% 1.40/0.56  fof(f21,plain,(
% 1.40/0.56    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 1.40/0.56    inference(ennf_transformation,[],[f1])).
% 1.40/0.56  fof(f1,axiom,(
% 1.40/0.56    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 1.40/0.56  fof(f159,plain,(
% 1.40/0.56    spl1_8 | ~spl1_4 | ~spl1_3 | ~spl1_5),
% 1.40/0.56    inference(avatar_split_clause,[],[f155,f121,f69,f75,f157])).
% 1.40/0.56  fof(f75,plain,(
% 1.40/0.56    spl1_4 <=> v1_relat_1(k1_xboole_0)),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 1.40/0.56  fof(f69,plain,(
% 1.40/0.56    spl1_3 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 1.40/0.56  fof(f121,plain,(
% 1.40/0.56    spl1_5 <=> ! [X1,X3,X0,X2] : (r1_tarski(k2_relat_1(k1_xboole_0),k2_tarski(X0,X1)) | ~v1_relat_1(k2_tarski(k4_tarski(X2,X0),k4_tarski(X3,X1))))),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 1.40/0.56  fof(f155,plain,(
% 1.40/0.56    ( ! [X6,X4,X7,X5] : (~v1_relat_1(k1_xboole_0) | r1_tarski(k1_relat_1(k1_xboole_0),k2_tarski(X4,X5)) | ~v1_relat_1(k2_tarski(k4_tarski(X4,X6),k4_tarski(X5,X7)))) ) | (~spl1_3 | ~spl1_5)),
% 1.40/0.56    inference(forward_demodulation,[],[f154,f70])).
% 1.40/0.56  fof(f70,plain,(
% 1.40/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl1_3),
% 1.40/0.56    inference(avatar_component_clause,[],[f69])).
% 1.40/0.56  fof(f154,plain,(
% 1.40/0.56    ( ! [X6,X4,X7,X5] : (r1_tarski(k1_relat_1(k1_xboole_0),k2_tarski(X4,X5)) | ~v1_relat_1(k2_tarski(k4_tarski(X4,X6),k4_tarski(X5,X7))) | ~v1_relat_1(k2_relat_1(k1_xboole_0))) ) | (~spl1_3 | ~spl1_5)),
% 1.40/0.56    inference(forward_demodulation,[],[f153,f70])).
% 1.40/0.56  fof(f153,plain,(
% 1.40/0.56    ( ! [X6,X4,X7,X5] : (r1_tarski(k1_relat_1(k2_relat_1(k1_xboole_0)),k2_tarski(X4,X5)) | ~v1_relat_1(k2_tarski(k4_tarski(X4,X6),k4_tarski(X5,X7))) | ~v1_relat_1(k2_relat_1(k1_xboole_0))) ) | ~spl1_5),
% 1.40/0.56    inference(resolution,[],[f97,f124])).
% 1.40/0.56  fof(f124,plain,(
% 1.40/0.56    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k1_xboole_0),k2_tarski(X0,X1))) ) | ~spl1_5),
% 1.40/0.56    inference(resolution,[],[f122,f44])).
% 1.40/0.56  fof(f122,plain,(
% 1.40/0.56    ( ! [X2,X0,X3,X1] : (~v1_relat_1(k2_tarski(k4_tarski(X2,X0),k4_tarski(X3,X1))) | r1_tarski(k2_relat_1(k1_xboole_0),k2_tarski(X0,X1))) ) | ~spl1_5),
% 1.40/0.56    inference(avatar_component_clause,[],[f121])).
% 1.40/0.56  fof(f97,plain,(
% 1.40/0.56    ( ! [X4,X2,X0,X3,X1] : (~r1_tarski(X4,k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) | r1_tarski(k1_relat_1(X4),k2_tarski(X0,X2)) | ~v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) | ~v1_relat_1(X4)) )),
% 1.40/0.56    inference(superposition,[],[f32,f96])).
% 1.40/0.56  fof(f96,plain,(
% 1.40/0.56    ( ! [X2,X0,X3,X1] : (k2_tarski(X0,X2) = k1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 1.40/0.56    inference(global_subsumption,[],[f44,f53])).
% 1.40/0.56  fof(f53,plain,(
% 1.40/0.56    ( ! [X2,X0,X3,X1] : (k2_tarski(X0,X2) = k1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) | ~v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 1.40/0.56    inference(equality_resolution,[],[f30])).
% 1.40/0.56  fof(f30,plain,(
% 1.40/0.56    ( ! [X4,X2,X0,X3,X1] : (k1_relat_1(X4) = k2_tarski(X0,X2) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4 | ~v1_relat_1(X4)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f17])).
% 1.40/0.56  fof(f17,plain,(
% 1.40/0.56    ! [X0,X1,X2,X3,X4] : ((k2_relat_1(X4) = k2_tarski(X1,X3) & k1_relat_1(X4) = k2_tarski(X0,X2)) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4 | ~v1_relat_1(X4))),
% 1.40/0.56    inference(flattening,[],[f16])).
% 1.40/0.56  fof(f16,plain,(
% 1.40/0.56    ! [X0,X1,X2,X3,X4] : (((k2_relat_1(X4) = k2_tarski(X1,X3) & k1_relat_1(X4) = k2_tarski(X0,X2)) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4) | ~v1_relat_1(X4))),
% 1.40/0.56    inference(ennf_transformation,[],[f11])).
% 1.40/0.56  fof(f11,axiom,(
% 1.40/0.56    ! [X0,X1,X2,X3,X4] : (v1_relat_1(X4) => (k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4 => (k2_relat_1(X4) = k2_tarski(X1,X3) & k1_relat_1(X4) = k2_tarski(X0,X2))))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relat_1)).
% 1.40/0.56  fof(f32,plain,(
% 1.40/0.56    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f19])).
% 1.40/0.56  fof(f19,plain,(
% 1.40/0.56    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.40/0.56    inference(flattening,[],[f18])).
% 1.40/0.56  fof(f18,plain,(
% 1.40/0.56    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.40/0.56    inference(ennf_transformation,[],[f12])).
% 1.40/0.56  fof(f12,axiom,(
% 1.40/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 1.40/0.56  fof(f141,plain,(
% 1.40/0.56    ~spl1_6),
% 1.40/0.56    inference(avatar_contradiction_clause,[],[f133])).
% 1.40/0.56  fof(f133,plain,(
% 1.40/0.56    $false | ~spl1_6),
% 1.40/0.56    inference(unit_resulting_resolution,[],[f55,f129,f49])).
% 1.40/0.56  fof(f129,plain,(
% 1.40/0.56    ( ! [X0] : (r2_hidden(X0,k2_relat_1(k1_xboole_0))) ) | ~spl1_6),
% 1.40/0.56    inference(avatar_component_clause,[],[f128])).
% 1.40/0.56  fof(f128,plain,(
% 1.40/0.56    spl1_6 <=> ! [X0] : r2_hidden(X0,k2_relat_1(k1_xboole_0))),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 1.40/0.56  fof(f130,plain,(
% 1.40/0.56    spl1_3 | spl1_6 | ~spl1_5),
% 1.40/0.56    inference(avatar_split_clause,[],[f125,f121,f128,f69])).
% 1.40/0.56  fof(f125,plain,(
% 1.40/0.56    ( ! [X0] : (r2_hidden(X0,k2_relat_1(k1_xboole_0)) | k1_xboole_0 = k2_relat_1(k1_xboole_0)) ) | ~spl1_5),
% 1.40/0.56    inference(resolution,[],[f124,f82])).
% 1.40/0.56  fof(f123,plain,(
% 1.40/0.56    ~spl1_4 | spl1_5),
% 1.40/0.56    inference(avatar_split_clause,[],[f119,f121,f75])).
% 1.40/0.56  fof(f119,plain,(
% 1.40/0.56    ( ! [X2,X0,X3,X1] : (r1_tarski(k2_relat_1(k1_xboole_0),k2_tarski(X0,X1)) | ~v1_relat_1(k2_tarski(k4_tarski(X2,X0),k4_tarski(X3,X1))) | ~v1_relat_1(k1_xboole_0)) )),
% 1.40/0.56    inference(resolution,[],[f94,f42])).
% 1.40/0.56  fof(f42,plain,(
% 1.40/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f4])).
% 1.40/0.56  fof(f4,axiom,(
% 1.40/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.40/0.56  fof(f94,plain,(
% 1.40/0.56    ( ! [X4,X2,X0,X3,X1] : (~r1_tarski(X4,k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) | r1_tarski(k2_relat_1(X4),k2_tarski(X1,X3)) | ~v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) | ~v1_relat_1(X4)) )),
% 1.40/0.56    inference(superposition,[],[f33,f93])).
% 1.40/0.56  fof(f93,plain,(
% 1.40/0.56    ( ! [X2,X0,X3,X1] : (k2_tarski(X1,X3) = k2_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 1.40/0.56    inference(global_subsumption,[],[f44,f52])).
% 1.40/0.56  fof(f52,plain,(
% 1.40/0.56    ( ! [X2,X0,X3,X1] : (k2_tarski(X1,X3) = k2_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) | ~v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 1.40/0.56    inference(equality_resolution,[],[f31])).
% 1.40/0.56  fof(f31,plain,(
% 1.40/0.56    ( ! [X4,X2,X0,X3,X1] : (k2_relat_1(X4) = k2_tarski(X1,X3) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4 | ~v1_relat_1(X4)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f17])).
% 1.40/0.56  fof(f33,plain,(
% 1.40/0.56    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f19])).
% 1.40/0.56  fof(f78,plain,(
% 1.40/0.56    spl1_4 | ~spl1_1),
% 1.40/0.56    inference(avatar_split_clause,[],[f73,f60,f75])).
% 1.40/0.56  fof(f60,plain,(
% 1.40/0.56    spl1_1 <=> v1_xboole_0(k1_xboole_0)),
% 1.40/0.56    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 1.40/0.56  fof(f73,plain,(
% 1.40/0.56    v1_relat_1(k1_xboole_0) | ~spl1_1),
% 1.40/0.56    inference(resolution,[],[f46,f62])).
% 1.40/0.56  fof(f62,plain,(
% 1.40/0.56    v1_xboole_0(k1_xboole_0) | ~spl1_1),
% 1.40/0.56    inference(avatar_component_clause,[],[f60])).
% 1.40/0.56  fof(f46,plain,(
% 1.40/0.56    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 1.40/0.56    inference(cnf_transformation,[],[f20])).
% 1.40/0.56  fof(f20,plain,(
% 1.40/0.56    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.40/0.56    inference(ennf_transformation,[],[f9])).
% 1.40/0.56  fof(f9,axiom,(
% 1.40/0.56    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.40/0.56  fof(f72,plain,(
% 1.40/0.56    ~spl1_2 | ~spl1_3),
% 1.40/0.56    inference(avatar_split_clause,[],[f29,f69,f65])).
% 1.40/0.56  fof(f29,plain,(
% 1.40/0.56    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 1.40/0.56    inference(cnf_transformation,[],[f15])).
% 1.40/0.56  fof(f15,plain,(
% 1.40/0.56    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 1.40/0.56    inference(ennf_transformation,[],[f14])).
% 1.40/0.56  fof(f14,negated_conjecture,(
% 1.40/0.56    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 1.40/0.56    inference(negated_conjecture,[],[f13])).
% 1.40/0.56  fof(f13,conjecture,(
% 1.40/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.40/0.56  fof(f63,plain,(
% 1.40/0.56    spl1_1),
% 1.40/0.56    inference(avatar_split_clause,[],[f43,f60])).
% 1.40/0.56  fof(f43,plain,(
% 1.40/0.56    v1_xboole_0(k1_xboole_0)),
% 1.40/0.56    inference(cnf_transformation,[],[f2])).
% 1.40/0.56  fof(f2,axiom,(
% 1.40/0.56    v1_xboole_0(k1_xboole_0)),
% 1.40/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.40/0.56  % SZS output end Proof for theBenchmark
% 1.40/0.56  % (14228)------------------------------
% 1.40/0.56  % (14228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (14228)Termination reason: Refutation
% 1.40/0.56  
% 1.40/0.56  % (14228)Memory used [KB]: 10746
% 1.40/0.56  % (14228)Time elapsed: 0.080 s
% 1.40/0.56  % (14228)------------------------------
% 1.40/0.56  % (14228)------------------------------
% 1.40/0.56  % (14204)Success in time 0.186 s
%------------------------------------------------------------------------------
