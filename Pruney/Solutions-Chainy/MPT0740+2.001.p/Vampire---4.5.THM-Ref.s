%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 284 expanded)
%              Number of leaves         :   12 (  87 expanded)
%              Depth                    :   11
%              Number of atoms          :  218 ( 837 expanded)
%              Number of equality atoms :   14 (  58 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f370,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f142,f150,f232,f320,f369])).

fof(f369,plain,
    ( ~ spl6_6
    | spl6_7 ),
    inference(avatar_contradiction_clause,[],[f367])).

fof(f367,plain,
    ( $false
    | ~ spl6_6
    | spl6_7 ),
    inference(unit_resulting_resolution,[],[f149,f236,f322,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f322,plain,
    ( ~ r2_hidden(sK5(k3_tarski(sK0)),sK0)
    | ~ spl6_6
    | spl6_7 ),
    inference(unit_resulting_resolution,[],[f239,f238,f237,f235,f149,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,sK0)
      | X0 = X1
      | r2_hidden(X1,X0)
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f62,f37])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(resolution,[],[f58,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_ordinal1(X0)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(X1,X2)
      | X1 = X2
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ( r2_hidden(X2,X1)
          | X1 = X2
          | r2_hidden(X1,X2)
          | ~ r2_hidden(X2,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_ordinal1)).

fof(f58,plain,(
    v2_ordinal1(sK0) ),
    inference(unit_resulting_resolution,[],[f26,f33])).

fof(f33,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
    <=> ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_ordinal1)).

fof(f26,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ~ v3_ordinal1(k3_tarski(X0))
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => v3_ordinal1(k3_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_ordinal1)).

fof(f235,plain,
    ( r2_hidden(sK4(k3_tarski(sK0)),k3_tarski(sK0))
    | spl6_7 ),
    inference(unit_resulting_resolution,[],[f165,f44])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f165,plain,
    ( ~ v2_ordinal1(k3_tarski(sK0))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl6_7
  <=> v2_ordinal1(k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f237,plain,
    ( ~ r2_hidden(sK4(k3_tarski(sK0)),sK5(k3_tarski(sK0)))
    | spl6_7 ),
    inference(unit_resulting_resolution,[],[f165,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(X0),sK5(X0))
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f238,plain,
    ( sK4(k3_tarski(sK0)) != sK5(k3_tarski(sK0))
    | spl6_7 ),
    inference(unit_resulting_resolution,[],[f165,f47])).

fof(f47,plain,(
    ! [X0] :
      ( sK4(X0) != sK5(X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f239,plain,
    ( ~ r2_hidden(sK5(k3_tarski(sK0)),sK4(k3_tarski(sK0)))
    | spl6_7 ),
    inference(unit_resulting_resolution,[],[f165,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(X0),sK4(X0))
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f236,plain,
    ( r2_hidden(sK5(k3_tarski(sK0)),k3_tarski(sK0))
    | spl6_7 ),
    inference(unit_resulting_resolution,[],[f165,f45])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f149,plain,
    ( r1_tarski(k3_tarski(sK0),sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl6_6
  <=> r1_tarski(k3_tarski(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f320,plain,
    ( ~ spl6_3
    | spl6_7 ),
    inference(avatar_contradiction_clause,[],[f315])).

fof(f315,plain,
    ( $false
    | ~ spl6_3
    | spl6_7 ),
    inference(unit_resulting_resolution,[],[f57,f274,f275,f40])).

% (12078)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ r2_hidden(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f275,plain,
    ( ~ r1_tarski(sK1(sK0,sK0),sK0)
    | ~ spl6_3
    | spl6_7 ),
    inference(unit_resulting_resolution,[],[f271,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ~ r1_tarski(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(f271,plain,
    ( ~ r1_tarski(k3_tarski(sK0),sK0)
    | ~ spl6_3
    | spl6_7 ),
    inference(unit_resulting_resolution,[],[f235,f268,f37])).

fof(f268,plain,
    ( ~ r2_hidden(sK4(k3_tarski(sK0)),sK0)
    | ~ spl6_3
    | spl6_7 ),
    inference(unit_resulting_resolution,[],[f236,f238,f237,f239,f127])).

fof(f127,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,k3_tarski(sK0))
        | r2_hidden(X1,X2)
        | X1 = X2
        | ~ r2_hidden(X1,sK0)
        | r2_hidden(X2,X1) )
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl6_3
  <=> ! [X1,X2] :
        ( X1 = X2
        | r2_hidden(X1,X2)
        | ~ r2_hidden(X2,k3_tarski(sK0))
        | ~ r2_hidden(X1,sK0)
        | r2_hidden(X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f274,plain,
    ( r2_hidden(sK1(sK0,sK0),sK0)
    | ~ spl6_3
    | spl6_7 ),
    inference(unit_resulting_resolution,[],[f271,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X0)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f57,plain,(
    v1_ordinal1(sK0) ),
    inference(unit_resulting_resolution,[],[f26,f32])).

fof(f32,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f232,plain,(
    ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f57,f197,f198,f40])).

fof(f198,plain,
    ( ~ r1_tarski(sK1(sK0,sK0),sK0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f195,f29])).

fof(f195,plain,
    ( ~ r1_tarski(k3_tarski(sK0),sK0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f178,f188,f37])).

fof(f188,plain,
    ( ~ r2_hidden(sK3(k3_tarski(sK0)),sK0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f179,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).

fof(f179,plain,
    ( ~ r1_tarski(sK3(k3_tarski(sK0)),k3_tarski(sK0))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f171,f42])).

fof(f42,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ r1_tarski(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f171,plain,
    ( ~ v1_ordinal1(k3_tarski(sK0))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f27,f166,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0)
      | v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f166,plain,
    ( v2_ordinal1(k3_tarski(sK0))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f164])).

fof(f27,plain,(
    ~ v3_ordinal1(k3_tarski(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f178,plain,
    ( r2_hidden(sK3(k3_tarski(sK0)),k3_tarski(sK0))
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f171,f41])).

% (12077)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f41,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f197,plain,
    ( r2_hidden(sK1(sK0,sK0),sK0)
    | ~ spl6_7 ),
    inference(unit_resulting_resolution,[],[f195,f28])).

fof(f150,plain,
    ( spl6_6
    | spl6_3
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f143,f140,f126,f147])).

fof(f140,plain,
    ( spl6_5
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X0,X1)
        | ~ r2_hidden(sK1(X2,sK0),sK0)
        | X0 = X1
        | r2_hidden(X1,X0)
        | ~ r2_hidden(X0,k3_tarski(X2))
        | ~ r2_hidden(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f143,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,X1)
        | X0 = X1
        | r2_hidden(X1,X0)
        | ~ r2_hidden(X0,k3_tarski(sK0))
        | ~ r2_hidden(X1,sK0)
        | r1_tarski(k3_tarski(sK0),sK0) )
    | ~ spl6_5 ),
    inference(resolution,[],[f141,f28])).

fof(f141,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK1(X2,sK0),sK0)
        | r2_hidden(X0,X1)
        | X0 = X1
        | r2_hidden(X1,X0)
        | ~ r2_hidden(X0,k3_tarski(X2))
        | ~ r2_hidden(X1,sK0) )
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f140])).

fof(f142,plain,
    ( ~ spl6_1
    | spl6_5 ),
    inference(avatar_split_clause,[],[f117,f140,f84])).

fof(f84,plain,
    ( spl6_1
  <=> v1_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X1,sK0)
      | ~ r2_hidden(X0,k3_tarski(X2))
      | r2_hidden(X1,X0)
      | X0 = X1
      | ~ r2_hidden(sK1(X2,sK0),sK0)
      | ~ v1_ordinal1(sK0) ) ),
    inference(resolution,[],[f77,f40])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(sK1(X2,sK0),sK0)
      | r2_hidden(X1,X0)
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X1,k3_tarski(X2))
      | r2_hidden(X0,X1)
      | X0 = X1 ) ),
    inference(resolution,[],[f72,f29])).

fof(f106,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f97])).

fof(f97,plain,
    ( $false
    | spl6_1 ),
    inference(unit_resulting_resolution,[],[f26,f86,f32])).

fof(f86,plain,
    ( ~ v1_ordinal1(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f84])).

% (12094)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:47:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.52  % (12088)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (12080)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (12081)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (12103)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.53  % (12097)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (12076)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (12097)Refutation not found, incomplete strategy% (12097)------------------------------
% 0.22/0.54  % (12097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (12097)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (12097)Memory used [KB]: 1663
% 0.22/0.54  % (12097)Time elapsed: 0.090 s
% 0.22/0.54  % (12097)------------------------------
% 0.22/0.54  % (12097)------------------------------
% 0.22/0.54  % (12082)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (12098)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (12098)Refutation not found, incomplete strategy% (12098)------------------------------
% 0.22/0.54  % (12098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (12098)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (12098)Memory used [KB]: 10618
% 0.22/0.54  % (12098)Time elapsed: 0.131 s
% 0.22/0.54  % (12098)------------------------------
% 0.22/0.54  % (12098)------------------------------
% 0.22/0.54  % (12080)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 1.41/0.55  % (12090)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.41/0.55  % (12083)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.41/0.56  % (12079)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.41/0.56  % (12091)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.41/0.56  % (12105)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.41/0.56  % (12096)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.56  % (12096)Refutation not found, incomplete strategy% (12096)------------------------------
% 1.41/0.56  % (12096)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (12096)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (12096)Memory used [KB]: 10746
% 1.41/0.56  % (12096)Time elapsed: 0.144 s
% 1.41/0.56  % (12096)------------------------------
% 1.41/0.56  % (12096)------------------------------
% 1.41/0.56  % SZS output start Proof for theBenchmark
% 1.41/0.56  fof(f370,plain,(
% 1.41/0.56    $false),
% 1.41/0.56    inference(avatar_sat_refutation,[],[f106,f142,f150,f232,f320,f369])).
% 1.41/0.56  fof(f369,plain,(
% 1.41/0.56    ~spl6_6 | spl6_7),
% 1.41/0.56    inference(avatar_contradiction_clause,[],[f367])).
% 1.41/0.56  fof(f367,plain,(
% 1.41/0.56    $false | (~spl6_6 | spl6_7)),
% 1.41/0.56    inference(unit_resulting_resolution,[],[f149,f236,f322,f37])).
% 1.41/0.56  fof(f37,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f20])).
% 1.41/0.56  fof(f20,plain,(
% 1.41/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.41/0.56    inference(ennf_transformation,[],[f1])).
% 1.41/0.56  fof(f1,axiom,(
% 1.41/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.41/0.56  fof(f322,plain,(
% 1.41/0.56    ~r2_hidden(sK5(k3_tarski(sK0)),sK0) | (~spl6_6 | spl6_7)),
% 1.41/0.56    inference(unit_resulting_resolution,[],[f239,f238,f237,f235,f149,f72])).
% 1.41/0.56  fof(f72,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X2,sK0) | X0 = X1 | r2_hidden(X1,X0) | ~r2_hidden(X0,sK0) | ~r2_hidden(X1,X2) | r2_hidden(X0,X1)) )),
% 1.41/0.56    inference(resolution,[],[f62,f37])).
% 1.41/0.56  fof(f62,plain,(
% 1.41/0.56    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X1,sK0)) )),
% 1.41/0.56    inference(resolution,[],[f58,f43])).
% 1.41/0.56  fof(f43,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (~v2_ordinal1(X0) | ~r2_hidden(X2,X0) | r2_hidden(X1,X2) | X1 = X2 | r2_hidden(X2,X1) | ~r2_hidden(X1,X0)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f22])).
% 1.41/0.56  fof(f22,plain,(
% 1.41/0.56    ! [X0] : (v2_ordinal1(X0) <=> ! [X1,X2] : (r2_hidden(X2,X1) | X1 = X2 | r2_hidden(X1,X2) | ~r2_hidden(X2,X0) | ~r2_hidden(X1,X0)))),
% 1.41/0.56    inference(ennf_transformation,[],[f7])).
% 1.41/0.56  fof(f7,axiom,(
% 1.41/0.56    ! [X0] : (v2_ordinal1(X0) <=> ! [X1,X2] : ~(~r2_hidden(X2,X1) & X1 != X2 & ~r2_hidden(X1,X2) & r2_hidden(X2,X0) & r2_hidden(X1,X0)))),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_ordinal1)).
% 1.41/0.56  fof(f58,plain,(
% 1.41/0.56    v2_ordinal1(sK0)),
% 1.41/0.56    inference(unit_resulting_resolution,[],[f26,f33])).
% 1.41/0.56  fof(f33,plain,(
% 1.41/0.56    ( ! [X0] : (v2_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f8])).
% 1.41/0.56  fof(f8,axiom,(
% 1.41/0.56    ! [X0] : (v3_ordinal1(X0) <=> (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_ordinal1)).
% 1.41/0.56  fof(f26,plain,(
% 1.41/0.56    v3_ordinal1(sK0)),
% 1.41/0.56    inference(cnf_transformation,[],[f14])).
% 1.41/0.56  fof(f14,plain,(
% 1.41/0.56    ? [X0] : (~v3_ordinal1(k3_tarski(X0)) & v3_ordinal1(X0))),
% 1.41/0.56    inference(ennf_transformation,[],[f13])).
% 1.41/0.56  fof(f13,negated_conjecture,(
% 1.41/0.56    ~! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k3_tarski(X0)))),
% 1.41/0.56    inference(negated_conjecture,[],[f12])).
% 1.41/0.56  fof(f12,conjecture,(
% 1.41/0.56    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k3_tarski(X0)))),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_ordinal1)).
% 1.41/0.56  fof(f235,plain,(
% 1.41/0.56    r2_hidden(sK4(k3_tarski(sK0)),k3_tarski(sK0)) | spl6_7),
% 1.41/0.56    inference(unit_resulting_resolution,[],[f165,f44])).
% 1.41/0.56  fof(f44,plain,(
% 1.41/0.56    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v2_ordinal1(X0)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f22])).
% 1.41/0.56  fof(f165,plain,(
% 1.41/0.56    ~v2_ordinal1(k3_tarski(sK0)) | spl6_7),
% 1.41/0.56    inference(avatar_component_clause,[],[f164])).
% 1.41/0.56  fof(f164,plain,(
% 1.41/0.56    spl6_7 <=> v2_ordinal1(k3_tarski(sK0))),
% 1.41/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.41/0.56  fof(f237,plain,(
% 1.41/0.56    ~r2_hidden(sK4(k3_tarski(sK0)),sK5(k3_tarski(sK0))) | spl6_7),
% 1.41/0.56    inference(unit_resulting_resolution,[],[f165,f46])).
% 1.41/0.56  fof(f46,plain,(
% 1.41/0.56    ( ! [X0] : (~r2_hidden(sK4(X0),sK5(X0)) | v2_ordinal1(X0)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f22])).
% 1.41/0.56  fof(f238,plain,(
% 1.41/0.56    sK4(k3_tarski(sK0)) != sK5(k3_tarski(sK0)) | spl6_7),
% 1.41/0.56    inference(unit_resulting_resolution,[],[f165,f47])).
% 1.41/0.56  fof(f47,plain,(
% 1.41/0.56    ( ! [X0] : (sK4(X0) != sK5(X0) | v2_ordinal1(X0)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f22])).
% 1.41/0.56  fof(f239,plain,(
% 1.41/0.56    ~r2_hidden(sK5(k3_tarski(sK0)),sK4(k3_tarski(sK0))) | spl6_7),
% 1.41/0.56    inference(unit_resulting_resolution,[],[f165,f48])).
% 1.41/0.56  fof(f48,plain,(
% 1.41/0.56    ( ! [X0] : (~r2_hidden(sK5(X0),sK4(X0)) | v2_ordinal1(X0)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f22])).
% 1.41/0.56  fof(f236,plain,(
% 1.41/0.56    r2_hidden(sK5(k3_tarski(sK0)),k3_tarski(sK0)) | spl6_7),
% 1.41/0.56    inference(unit_resulting_resolution,[],[f165,f45])).
% 1.41/0.56  fof(f45,plain,(
% 1.41/0.56    ( ! [X0] : (r2_hidden(sK5(X0),X0) | v2_ordinal1(X0)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f22])).
% 1.41/0.56  fof(f149,plain,(
% 1.41/0.56    r1_tarski(k3_tarski(sK0),sK0) | ~spl6_6),
% 1.41/0.56    inference(avatar_component_clause,[],[f147])).
% 1.41/0.56  fof(f147,plain,(
% 1.41/0.56    spl6_6 <=> r1_tarski(k3_tarski(sK0),sK0)),
% 1.41/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.41/0.56  fof(f320,plain,(
% 1.41/0.56    ~spl6_3 | spl6_7),
% 1.41/0.56    inference(avatar_contradiction_clause,[],[f315])).
% 1.41/0.56  fof(f315,plain,(
% 1.41/0.56    $false | (~spl6_3 | spl6_7)),
% 1.41/0.56    inference(unit_resulting_resolution,[],[f57,f274,f275,f40])).
% 1.41/0.56  % (12078)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.41/0.56  fof(f40,plain,(
% 1.41/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0) | ~v1_ordinal1(X0)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f21])).
% 1.41/0.56  fof(f21,plain,(
% 1.41/0.56    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)))),
% 1.41/0.56    inference(ennf_transformation,[],[f6])).
% 1.41/0.56  fof(f6,axiom,(
% 1.41/0.56    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).
% 1.41/0.56  fof(f275,plain,(
% 1.41/0.56    ~r1_tarski(sK1(sK0,sK0),sK0) | (~spl6_3 | spl6_7)),
% 1.41/0.56    inference(unit_resulting_resolution,[],[f271,f29])).
% 1.41/0.56  fof(f29,plain,(
% 1.41/0.56    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ~r1_tarski(sK1(X0,X1),X1)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f15])).
% 1.41/0.56  fof(f15,plain,(
% 1.41/0.56    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 1.41/0.56    inference(ennf_transformation,[],[f4])).
% 1.41/0.56  fof(f4,axiom,(
% 1.41/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).
% 1.41/0.56  fof(f271,plain,(
% 1.41/0.56    ~r1_tarski(k3_tarski(sK0),sK0) | (~spl6_3 | spl6_7)),
% 1.41/0.56    inference(unit_resulting_resolution,[],[f235,f268,f37])).
% 1.41/0.56  fof(f268,plain,(
% 1.41/0.56    ~r2_hidden(sK4(k3_tarski(sK0)),sK0) | (~spl6_3 | spl6_7)),
% 1.41/0.56    inference(unit_resulting_resolution,[],[f236,f238,f237,f239,f127])).
% 1.41/0.56  fof(f127,plain,(
% 1.41/0.56    ( ! [X2,X1] : (~r2_hidden(X2,k3_tarski(sK0)) | r2_hidden(X1,X2) | X1 = X2 | ~r2_hidden(X1,sK0) | r2_hidden(X2,X1)) ) | ~spl6_3),
% 1.41/0.56    inference(avatar_component_clause,[],[f126])).
% 1.41/0.56  fof(f126,plain,(
% 1.41/0.56    spl6_3 <=> ! [X1,X2] : (X1 = X2 | r2_hidden(X1,X2) | ~r2_hidden(X2,k3_tarski(sK0)) | ~r2_hidden(X1,sK0) | r2_hidden(X2,X1))),
% 1.41/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.41/0.56  fof(f274,plain,(
% 1.41/0.56    r2_hidden(sK1(sK0,sK0),sK0) | (~spl6_3 | spl6_7)),
% 1.41/0.56    inference(unit_resulting_resolution,[],[f271,f28])).
% 1.41/0.56  fof(f28,plain,(
% 1.41/0.56    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_tarski(k3_tarski(X0),X1)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f15])).
% 1.41/0.56  fof(f57,plain,(
% 1.41/0.56    v1_ordinal1(sK0)),
% 1.41/0.56    inference(unit_resulting_resolution,[],[f26,f32])).
% 1.41/0.56  fof(f32,plain,(
% 1.41/0.56    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f8])).
% 1.41/0.56  fof(f232,plain,(
% 1.41/0.56    ~spl6_7),
% 1.41/0.56    inference(avatar_contradiction_clause,[],[f227])).
% 1.41/0.56  fof(f227,plain,(
% 1.41/0.56    $false | ~spl6_7),
% 1.41/0.56    inference(unit_resulting_resolution,[],[f57,f197,f198,f40])).
% 1.41/0.56  fof(f198,plain,(
% 1.41/0.56    ~r1_tarski(sK1(sK0,sK0),sK0) | ~spl6_7),
% 1.41/0.56    inference(unit_resulting_resolution,[],[f195,f29])).
% 1.41/0.56  fof(f195,plain,(
% 1.41/0.56    ~r1_tarski(k3_tarski(sK0),sK0) | ~spl6_7),
% 1.41/0.56    inference(unit_resulting_resolution,[],[f178,f188,f37])).
% 1.41/0.56  fof(f188,plain,(
% 1.41/0.56    ~r2_hidden(sK3(k3_tarski(sK0)),sK0) | ~spl6_7),
% 1.41/0.56    inference(unit_resulting_resolution,[],[f179,f30])).
% 1.41/0.56  fof(f30,plain,(
% 1.41/0.56    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f16])).
% 1.41/0.56  fof(f16,plain,(
% 1.41/0.56    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 1.41/0.56    inference(ennf_transformation,[],[f3])).
% 1.41/0.56  fof(f3,axiom,(
% 1.41/0.56    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).
% 1.41/0.56  fof(f179,plain,(
% 1.41/0.56    ~r1_tarski(sK3(k3_tarski(sK0)),k3_tarski(sK0)) | ~spl6_7),
% 1.41/0.56    inference(unit_resulting_resolution,[],[f171,f42])).
% 1.41/0.56  fof(f42,plain,(
% 1.41/0.56    ( ! [X0] : (v1_ordinal1(X0) | ~r1_tarski(sK3(X0),X0)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f21])).
% 1.41/0.56  fof(f171,plain,(
% 1.41/0.56    ~v1_ordinal1(k3_tarski(sK0)) | ~spl6_7),
% 1.41/0.56    inference(unit_resulting_resolution,[],[f27,f166,f34])).
% 1.41/0.56  fof(f34,plain,(
% 1.41/0.56    ( ! [X0] : (~v2_ordinal1(X0) | ~v1_ordinal1(X0) | v3_ordinal1(X0)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f8])).
% 1.41/0.56  fof(f166,plain,(
% 1.41/0.56    v2_ordinal1(k3_tarski(sK0)) | ~spl6_7),
% 1.41/0.56    inference(avatar_component_clause,[],[f164])).
% 1.41/0.56  fof(f27,plain,(
% 1.41/0.56    ~v3_ordinal1(k3_tarski(sK0))),
% 1.41/0.56    inference(cnf_transformation,[],[f14])).
% 1.41/0.56  fof(f178,plain,(
% 1.41/0.56    r2_hidden(sK3(k3_tarski(sK0)),k3_tarski(sK0)) | ~spl6_7),
% 1.41/0.56    inference(unit_resulting_resolution,[],[f171,f41])).
% 1.41/0.56  % (12077)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.41/0.56  fof(f41,plain,(
% 1.41/0.56    ( ! [X0] : (v1_ordinal1(X0) | r2_hidden(sK3(X0),X0)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f21])).
% 1.41/0.56  fof(f197,plain,(
% 1.41/0.56    r2_hidden(sK1(sK0,sK0),sK0) | ~spl6_7),
% 1.41/0.56    inference(unit_resulting_resolution,[],[f195,f28])).
% 1.41/0.56  fof(f150,plain,(
% 1.41/0.56    spl6_6 | spl6_3 | ~spl6_5),
% 1.41/0.56    inference(avatar_split_clause,[],[f143,f140,f126,f147])).
% 1.41/0.56  fof(f140,plain,(
% 1.41/0.56    spl6_5 <=> ! [X1,X0,X2] : (r2_hidden(X0,X1) | ~r2_hidden(sK1(X2,sK0),sK0) | X0 = X1 | r2_hidden(X1,X0) | ~r2_hidden(X0,k3_tarski(X2)) | ~r2_hidden(X1,sK0))),
% 1.41/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.41/0.56  fof(f143,plain,(
% 1.41/0.56    ( ! [X0,X1] : (r2_hidden(X0,X1) | X0 = X1 | r2_hidden(X1,X0) | ~r2_hidden(X0,k3_tarski(sK0)) | ~r2_hidden(X1,sK0) | r1_tarski(k3_tarski(sK0),sK0)) ) | ~spl6_5),
% 1.41/0.56    inference(resolution,[],[f141,f28])).
% 1.41/0.56  fof(f141,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (~r2_hidden(sK1(X2,sK0),sK0) | r2_hidden(X0,X1) | X0 = X1 | r2_hidden(X1,X0) | ~r2_hidden(X0,k3_tarski(X2)) | ~r2_hidden(X1,sK0)) ) | ~spl6_5),
% 1.41/0.56    inference(avatar_component_clause,[],[f140])).
% 1.41/0.56  fof(f142,plain,(
% 1.41/0.56    ~spl6_1 | spl6_5),
% 1.41/0.56    inference(avatar_split_clause,[],[f117,f140,f84])).
% 1.41/0.56  fof(f84,plain,(
% 1.41/0.56    spl6_1 <=> v1_ordinal1(sK0)),
% 1.41/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.41/0.56  fof(f117,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X1,sK0) | ~r2_hidden(X0,k3_tarski(X2)) | r2_hidden(X1,X0) | X0 = X1 | ~r2_hidden(sK1(X2,sK0),sK0) | ~v1_ordinal1(sK0)) )),
% 1.41/0.56    inference(resolution,[],[f77,f40])).
% 1.41/0.56  fof(f77,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (~r1_tarski(sK1(X2,sK0),sK0) | r2_hidden(X1,X0) | ~r2_hidden(X0,sK0) | ~r2_hidden(X1,k3_tarski(X2)) | r2_hidden(X0,X1) | X0 = X1) )),
% 1.41/0.56    inference(resolution,[],[f72,f29])).
% 1.41/0.56  fof(f106,plain,(
% 1.41/0.56    spl6_1),
% 1.41/0.56    inference(avatar_contradiction_clause,[],[f97])).
% 1.41/0.56  fof(f97,plain,(
% 1.41/0.56    $false | spl6_1),
% 1.41/0.56    inference(unit_resulting_resolution,[],[f26,f86,f32])).
% 1.41/0.56  fof(f86,plain,(
% 1.41/0.56    ~v1_ordinal1(sK0) | spl6_1),
% 1.41/0.56    inference(avatar_component_clause,[],[f84])).
% 1.41/0.56  % (12094)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.41/0.56  % SZS output end Proof for theBenchmark
% 1.41/0.56  % (12080)------------------------------
% 1.41/0.56  % (12080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (12089)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.41/0.56  % (12080)Termination reason: Refutation
% 1.41/0.56  
% 1.41/0.56  % (12080)Memory used [KB]: 6396
% 1.41/0.56  % (12080)Time elapsed: 0.127 s
% 1.41/0.56  % (12080)------------------------------
% 1.41/0.56  % (12080)------------------------------
% 1.41/0.56  % (12078)Refutation not found, incomplete strategy% (12078)------------------------------
% 1.41/0.56  % (12078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (12078)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (12078)Memory used [KB]: 10618
% 1.41/0.56  % (12078)Time elapsed: 0.146 s
% 1.41/0.56  % (12078)------------------------------
% 1.41/0.56  % (12078)------------------------------
% 1.41/0.57  % (12075)Success in time 0.199 s
%------------------------------------------------------------------------------
