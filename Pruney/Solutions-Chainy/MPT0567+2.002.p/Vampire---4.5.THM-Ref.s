%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   24 (  36 expanded)
%              Number of leaves         :    6 (  12 expanded)
%              Depth                    :    7
%              Number of atoms          :   51 (  72 expanded)
%              Number of equality atoms :   15 (  23 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f237,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f61,f236])).

fof(f236,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f232,f58,f53])).

fof(f53,plain,
    ( spl6_1
  <=> k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f58,plain,
    ( spl6_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f232,plain,
    ( k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0)
    | ~ spl6_2 ),
    inference(resolution,[],[f220,f72])).

fof(f72,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f51,f29])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f51,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f220,plain,
    ( ! [X6] :
        ( r2_hidden(sK3(sK0,k1_xboole_0,X6),X6)
        | k10_relat_1(sK0,k1_xboole_0) = X6 )
    | ~ spl6_2 ),
    inference(resolution,[],[f151,f72])).

fof(f151,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(sK0,X0,X1),X0)
        | r2_hidden(sK3(sK0,X0,X1),X1)
        | k10_relat_1(sK0,X0) = X1 )
    | ~ spl6_2 ),
    inference(resolution,[],[f37,f60])).

fof(f60,plain,
    ( v1_relat_1(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k10_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(f61,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f23,f58])).

fof(f23,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( k1_xboole_0 != k10_relat_1(X0,k1_xboole_0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

% (20236)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (20235)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% (20210)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% (20231)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% (20214)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% (20227)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (20220)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (20232)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (20217)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (20219)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (20219)Refutation not found, incomplete strategy% (20219)------------------------------
% (20219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20219)Termination reason: Refutation not found, incomplete strategy

% (20219)Memory used [KB]: 10618
% (20219)Time elapsed: 0.150 s
% (20219)------------------------------
% (20219)------------------------------
% (20229)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (20225)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

fof(f56,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f24,f53])).

fof(f24,plain,(
    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:10:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (20209)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (20211)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (20228)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (20216)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (20222)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (20218)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (20215)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (20218)Refutation not found, incomplete strategy% (20218)------------------------------
% 0.21/0.53  % (20218)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (20218)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (20218)Memory used [KB]: 10618
% 0.21/0.53  % (20218)Time elapsed: 0.107 s
% 0.21/0.53  % (20218)------------------------------
% 0.21/0.53  % (20218)------------------------------
% 0.21/0.53  % (20213)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (20224)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (20221)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.54  % (20234)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (20226)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (20208)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (20223)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (20208)Refutation not found, incomplete strategy% (20208)------------------------------
% 0.21/0.54  % (20208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (20208)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (20208)Memory used [KB]: 1663
% 0.21/0.54  % (20208)Time elapsed: 0.128 s
% 0.21/0.54  % (20208)------------------------------
% 0.21/0.54  % (20208)------------------------------
% 0.21/0.54  % (20224)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f237,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f56,f61,f236])).
% 0.21/0.54  fof(f236,plain,(
% 0.21/0.54    spl6_1 | ~spl6_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f232,f58,f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    spl6_1 <=> k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    spl6_2 <=> v1_relat_1(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.54  fof(f232,plain,(
% 0.21/0.54    k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0) | ~spl6_2),
% 0.21/0.54    inference(resolution,[],[f220,f72])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.54    inference(superposition,[],[f51,f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.21/0.54    inference(equality_resolution,[],[f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.21/0.54  fof(f220,plain,(
% 0.21/0.54    ( ! [X6] : (r2_hidden(sK3(sK0,k1_xboole_0,X6),X6) | k10_relat_1(sK0,k1_xboole_0) = X6) ) | ~spl6_2),
% 0.21/0.54    inference(resolution,[],[f151,f72])).
% 0.21/0.54  fof(f151,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK5(sK0,X0,X1),X0) | r2_hidden(sK3(sK0,X0,X1),X1) | k10_relat_1(sK0,X0) = X1) ) | ~spl6_2),
% 0.21/0.54    inference(resolution,[],[f37,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    v1_relat_1(sK0) | ~spl6_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f58])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r2_hidden(sK5(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | k10_relat_1(X0,X1) = X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    spl6_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f23,f58])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    v1_relat_1(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ? [X0] : (k1_xboole_0 != k10_relat_1(X0,k1_xboole_0) & v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  % (20236)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (20235)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (20210)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (20231)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (20214)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (20227)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (20220)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (20232)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (20217)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (20219)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (20219)Refutation not found, incomplete strategy% (20219)------------------------------
% 0.21/0.55  % (20219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (20219)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (20219)Memory used [KB]: 10618
% 0.21/0.55  % (20219)Time elapsed: 0.150 s
% 0.21/0.55  % (20219)------------------------------
% 0.21/0.55  % (20219)------------------------------
% 0.21/0.55  % (20229)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (20225)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  fof(f14,negated_conjecture,(
% 0.21/0.56    ~! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 0.21/0.56    inference(negated_conjecture,[],[f13])).
% 0.21/0.56  fof(f13,conjecture,(
% 0.21/0.56    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).
% 0.21/0.56  fof(f56,plain,(
% 0.21/0.56    ~spl6_1),
% 0.21/0.56    inference(avatar_split_clause,[],[f24,f53])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0)),
% 0.21/0.56    inference(cnf_transformation,[],[f15])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (20224)------------------------------
% 0.21/0.56  % (20224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (20224)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (20224)Memory used [KB]: 10874
% 0.21/0.56  % (20224)Time elapsed: 0.120 s
% 0.21/0.56  % (20224)------------------------------
% 0.21/0.56  % (20224)------------------------------
% 0.21/0.56  % (20225)Refutation not found, incomplete strategy% (20225)------------------------------
% 0.21/0.56  % (20225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (20225)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (20225)Memory used [KB]: 10618
% 0.21/0.56  % (20225)Time elapsed: 0.149 s
% 0.21/0.56  % (20225)------------------------------
% 0.21/0.56  % (20225)------------------------------
% 0.21/0.56  % (20207)Success in time 0.193 s
%------------------------------------------------------------------------------
