%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:46 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 102 expanded)
%              Number of leaves         :   11 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  113 ( 208 expanded)
%              Number of equality atoms :   45 (  99 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f226,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f193,f207,f225])).

fof(f225,plain,(
    ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f215])).

fof(f215,plain,
    ( $false
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f47,f189,f189,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,k1_xboole_0) ) ),
    inference(superposition,[],[f53,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f189,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl3_7
  <=> r2_hidden(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f47,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f207,plain,(
    ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f15,f39,f200,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f21,f38,f38])).

fof(f38,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f16,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f17,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f17,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f16,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f200,plain,
    ( r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl3_8 ),
    inference(resolution,[],[f198,f63])).

fof(f63,plain,(
    ! [X0] : r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(resolution,[],[f43,f47])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f25,f38])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f7])).

% (19669)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f198,plain,
    ( ! [X6] :
        ( ~ r2_hidden(sK1,X6)
        | r1_tarski(sK0,X6) )
    | ~ spl3_8 ),
    inference(trivial_inequality_removal,[],[f197])).

fof(f197,plain,
    ( ! [X6] :
        ( k1_xboole_0 != k1_xboole_0
        | r1_tarski(sK0,X6)
        | ~ r2_hidden(sK1,X6) )
    | ~ spl3_8 ),
    inference(superposition,[],[f27,f192])).

fof(f192,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k4_xboole_0(sK0,X1)
        | ~ r2_hidden(sK1,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl3_8
  <=> ! [X1] :
        ( ~ r2_hidden(sK1,X1)
        | k1_xboole_0 = k4_xboole_0(sK0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f39,plain,(
    sK0 != k2_enumset1(sK1,sK1,sK1,sK1) ),
    inference(definition_unfolding,[],[f14,f38])).

fof(f14,plain,(
    sK0 != k1_tarski(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ~ r2_hidden(X2,X0) )
      & k1_xboole_0 != X0
      & k1_tarski(X1) != X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ~ ( X1 != X2
                & r2_hidden(X2,X0) )
          & k1_xboole_0 != X0
          & k1_tarski(X1) != X0 ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f15,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f12])).

fof(f193,plain,
    ( spl3_7
    | spl3_8 ),
    inference(avatar_split_clause,[],[f184,f191,f187])).

fof(f184,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK1,X1)
      | r2_hidden(sK1,k1_xboole_0)
      | k1_xboole_0 = k4_xboole_0(sK0,X1) ) ),
    inference(duplicate_literal_removal,[],[f181])).

fof(f181,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK1,X1)
      | r2_hidden(sK1,k1_xboole_0)
      | k1_xboole_0 = k4_xboole_0(sK0,X1)
      | k1_xboole_0 = k4_xboole_0(sK0,X1) ) ),
    inference(superposition,[],[f33,f177])).

fof(f177,plain,(
    ! [X11] :
      ( sK1 = sK2(sK0,X11,k1_xboole_0)
      | k1_xboole_0 = k4_xboole_0(sK0,X11) ) ),
    inference(resolution,[],[f79,f13])).

fof(f13,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | sK1 = X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f79,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK2(X8,X9,k1_xboole_0),X8)
      | k1_xboole_0 = k4_xboole_0(X8,X9) ) ),
    inference(resolution,[],[f32,f62])).

fof(f62,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(condensation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f56,f47])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:59:04 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.52  % (19664)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.52  % (19672)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.23/0.53  % (19658)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.23/0.53  % (19659)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.23/0.53  % (19680)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.23/0.53  % (19659)Refutation not found, incomplete strategy% (19659)------------------------------
% 0.23/0.53  % (19659)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (19659)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (19659)Memory used [KB]: 1663
% 0.23/0.53  % (19659)Time elapsed: 0.114 s
% 0.23/0.53  % (19659)------------------------------
% 0.23/0.53  % (19659)------------------------------
% 0.23/0.54  % (19671)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.23/0.54  % (19663)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.23/0.54  % (19661)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.23/0.54  % (19660)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.23/0.54  % (19662)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.23/0.54  % (19681)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.23/0.55  % (19673)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.23/0.55  % (19685)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.23/0.55  % (19687)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.23/0.55  % (19679)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.23/0.55  % (19674)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.23/0.55  % (19665)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.23/0.55  % (19671)Refutation found. Thanks to Tanya!
% 0.23/0.55  % SZS status Theorem for theBenchmark
% 0.23/0.55  % (19687)Refutation not found, incomplete strategy% (19687)------------------------------
% 0.23/0.55  % (19687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (19687)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (19687)Memory used [KB]: 1663
% 0.23/0.55  % (19687)Time elapsed: 0.131 s
% 0.23/0.55  % (19687)------------------------------
% 0.23/0.55  % (19687)------------------------------
% 0.23/0.55  % (19676)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.23/0.55  % (19686)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.23/0.55  % (19674)Refutation not found, incomplete strategy% (19674)------------------------------
% 0.23/0.55  % (19674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (19674)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (19674)Memory used [KB]: 10618
% 0.23/0.55  % (19674)Time elapsed: 0.135 s
% 0.23/0.55  % (19674)------------------------------
% 0.23/0.55  % (19674)------------------------------
% 0.23/0.55  % (19677)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.23/0.56  % (19666)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.23/0.56  % (19684)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.23/0.56  % (19678)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.23/0.56  % (19682)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.23/0.56  % SZS output start Proof for theBenchmark
% 0.23/0.56  fof(f226,plain,(
% 0.23/0.56    $false),
% 0.23/0.56    inference(avatar_sat_refutation,[],[f193,f207,f225])).
% 0.23/0.56  fof(f225,plain,(
% 0.23/0.56    ~spl3_7),
% 0.23/0.56    inference(avatar_contradiction_clause,[],[f215])).
% 0.23/0.56  fof(f215,plain,(
% 0.23/0.56    $false | ~spl3_7),
% 0.23/0.56    inference(unit_resulting_resolution,[],[f47,f189,f189,f56])).
% 0.23/0.56  fof(f56,plain,(
% 0.23/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,k1_xboole_0)) )),
% 0.23/0.56    inference(superposition,[],[f53,f26])).
% 0.23/0.56  fof(f26,plain,(
% 0.23/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f3])).
% 0.23/0.56  fof(f3,axiom,(
% 0.23/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.23/0.56  fof(f53,plain,(
% 0.23/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 0.23/0.56    inference(equality_resolution,[],[f35])).
% 0.23/0.56  fof(f35,plain,(
% 0.23/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.23/0.56    inference(cnf_transformation,[],[f1])).
% 0.23/0.56  fof(f1,axiom,(
% 0.23/0.56    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.23/0.56  fof(f189,plain,(
% 0.23/0.56    r2_hidden(sK1,k1_xboole_0) | ~spl3_7),
% 0.23/0.56    inference(avatar_component_clause,[],[f187])).
% 0.23/0.56  fof(f187,plain,(
% 0.23/0.56    spl3_7 <=> r2_hidden(sK1,k1_xboole_0)),
% 0.23/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.23/0.56  fof(f47,plain,(
% 0.23/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.23/0.56    inference(equality_resolution,[],[f19])).
% 0.23/0.56  fof(f19,plain,(
% 0.23/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.23/0.56    inference(cnf_transformation,[],[f2])).
% 0.23/0.56  fof(f2,axiom,(
% 0.23/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.23/0.56  fof(f207,plain,(
% 0.23/0.56    ~spl3_8),
% 0.23/0.56    inference(avatar_contradiction_clause,[],[f202])).
% 0.23/0.56  fof(f202,plain,(
% 0.23/0.56    $false | ~spl3_8),
% 0.23/0.56    inference(unit_resulting_resolution,[],[f15,f39,f200,f42])).
% 0.23/0.56  fof(f42,plain,(
% 0.23/0.56    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 0.23/0.56    inference(definition_unfolding,[],[f21,f38,f38])).
% 0.23/0.56  fof(f38,plain,(
% 0.23/0.56    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.23/0.56    inference(definition_unfolding,[],[f16,f37])).
% 0.23/0.56  fof(f37,plain,(
% 0.23/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.23/0.56    inference(definition_unfolding,[],[f17,f30])).
% 0.23/0.56  fof(f30,plain,(
% 0.23/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f6])).
% 0.23/0.56  fof(f6,axiom,(
% 0.23/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.23/0.56  fof(f17,plain,(
% 0.23/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f5])).
% 0.23/0.56  fof(f5,axiom,(
% 0.23/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.23/0.56  fof(f16,plain,(
% 0.23/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f4])).
% 0.23/0.56  fof(f4,axiom,(
% 0.23/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.23/0.56  fof(f21,plain,(
% 0.23/0.56    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.23/0.56    inference(cnf_transformation,[],[f8])).
% 0.23/0.56  fof(f8,axiom,(
% 0.23/0.56    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.23/0.56  fof(f200,plain,(
% 0.23/0.56    r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl3_8),
% 0.23/0.56    inference(resolution,[],[f198,f63])).
% 0.23/0.56  fof(f63,plain,(
% 0.23/0.56    ( ! [X0] : (r2_hidden(X0,k2_enumset1(X0,X0,X0,X0))) )),
% 0.23/0.56    inference(resolution,[],[f43,f47])).
% 0.23/0.56  fof(f43,plain,(
% 0.23/0.56    ( ! [X0,X1] : (~r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.23/0.56    inference(definition_unfolding,[],[f25,f38])).
% 0.23/0.56  fof(f25,plain,(
% 0.23/0.56    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f7])).
% 0.23/0.56  % (19669)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.23/0.56  fof(f7,axiom,(
% 0.23/0.56    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.23/0.56  fof(f198,plain,(
% 0.23/0.56    ( ! [X6] : (~r2_hidden(sK1,X6) | r1_tarski(sK0,X6)) ) | ~spl3_8),
% 0.23/0.56    inference(trivial_inequality_removal,[],[f197])).
% 0.23/0.56  fof(f197,plain,(
% 0.23/0.56    ( ! [X6] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,X6) | ~r2_hidden(sK1,X6)) ) | ~spl3_8),
% 0.23/0.56    inference(superposition,[],[f27,f192])).
% 0.23/0.56  fof(f192,plain,(
% 0.23/0.56    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(sK0,X1) | ~r2_hidden(sK1,X1)) ) | ~spl3_8),
% 0.23/0.56    inference(avatar_component_clause,[],[f191])).
% 0.23/0.56  fof(f191,plain,(
% 0.23/0.56    spl3_8 <=> ! [X1] : (~r2_hidden(sK1,X1) | k1_xboole_0 = k4_xboole_0(sK0,X1))),
% 0.23/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.23/0.56  fof(f27,plain,(
% 0.23/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.23/0.56    inference(cnf_transformation,[],[f3])).
% 0.23/0.56  fof(f39,plain,(
% 0.23/0.56    sK0 != k2_enumset1(sK1,sK1,sK1,sK1)),
% 0.23/0.56    inference(definition_unfolding,[],[f14,f38])).
% 0.23/0.56  fof(f14,plain,(
% 0.23/0.56    sK0 != k1_tarski(sK1)),
% 0.23/0.56    inference(cnf_transformation,[],[f12])).
% 0.23/0.56  fof(f12,plain,(
% 0.23/0.56    ? [X0,X1] : (! [X2] : (X1 = X2 | ~r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.23/0.56    inference(ennf_transformation,[],[f11])).
% 0.23/0.56  fof(f11,negated_conjecture,(
% 0.23/0.56    ~! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.23/0.56    inference(negated_conjecture,[],[f10])).
% 0.23/0.56  fof(f10,conjecture,(
% 0.23/0.56    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.23/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 0.23/0.56  fof(f15,plain,(
% 0.23/0.56    k1_xboole_0 != sK0),
% 0.23/0.56    inference(cnf_transformation,[],[f12])).
% 0.23/0.56  fof(f193,plain,(
% 0.23/0.56    spl3_7 | spl3_8),
% 0.23/0.56    inference(avatar_split_clause,[],[f184,f191,f187])).
% 0.23/0.56  fof(f184,plain,(
% 0.23/0.56    ( ! [X1] : (~r2_hidden(sK1,X1) | r2_hidden(sK1,k1_xboole_0) | k1_xboole_0 = k4_xboole_0(sK0,X1)) )),
% 0.23/0.56    inference(duplicate_literal_removal,[],[f181])).
% 0.23/0.56  fof(f181,plain,(
% 0.23/0.56    ( ! [X1] : (~r2_hidden(sK1,X1) | r2_hidden(sK1,k1_xboole_0) | k1_xboole_0 = k4_xboole_0(sK0,X1) | k1_xboole_0 = k4_xboole_0(sK0,X1)) )),
% 0.23/0.56    inference(superposition,[],[f33,f177])).
% 0.23/0.56  fof(f177,plain,(
% 0.23/0.56    ( ! [X11] : (sK1 = sK2(sK0,X11,k1_xboole_0) | k1_xboole_0 = k4_xboole_0(sK0,X11)) )),
% 0.23/0.56    inference(resolution,[],[f79,f13])).
% 0.23/0.56  fof(f13,plain,(
% 0.23/0.56    ( ! [X2] : (~r2_hidden(X2,sK0) | sK1 = X2) )),
% 0.23/0.56    inference(cnf_transformation,[],[f12])).
% 0.23/0.56  fof(f79,plain,(
% 0.23/0.56    ( ! [X8,X9] : (r2_hidden(sK2(X8,X9,k1_xboole_0),X8) | k1_xboole_0 = k4_xboole_0(X8,X9)) )),
% 0.23/0.56    inference(resolution,[],[f32,f62])).
% 0.23/0.56  fof(f62,plain,(
% 0.23/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.23/0.56    inference(condensation,[],[f60])).
% 0.23/0.56  fof(f60,plain,(
% 0.23/0.56    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_xboole_0)) )),
% 0.23/0.56    inference(resolution,[],[f56,f47])).
% 0.23/0.56  fof(f32,plain,(
% 0.23/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 0.23/0.56    inference(cnf_transformation,[],[f1])).
% 0.23/0.56  fof(f33,plain,(
% 0.23/0.56    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.23/0.56    inference(cnf_transformation,[],[f1])).
% 0.23/0.56  % SZS output end Proof for theBenchmark
% 0.23/0.56  % (19671)------------------------------
% 0.23/0.56  % (19671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (19671)Termination reason: Refutation
% 0.23/0.56  
% 0.23/0.56  % (19671)Memory used [KB]: 6268
% 0.23/0.56  % (19671)Time elapsed: 0.139 s
% 0.23/0.56  % (19671)------------------------------
% 0.23/0.56  % (19671)------------------------------
% 0.23/0.56  % (19657)Success in time 0.19 s
%------------------------------------------------------------------------------
