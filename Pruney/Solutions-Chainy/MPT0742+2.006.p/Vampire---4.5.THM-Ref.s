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
% DateTime   : Thu Dec  3 12:55:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 229 expanded)
%              Number of leaves         :   12 (  64 expanded)
%              Depth                    :   12
%              Number of atoms          :  195 ( 881 expanded)
%              Number of equality atoms :    9 (  62 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f455,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f138,f197,f243,f254,f454])).

fof(f454,plain,
    ( ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_contradiction_clause,[],[f451])).

fof(f451,plain,
    ( $false
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(unit_resulting_resolution,[],[f136,f133,f261,f266,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f266,plain,
    ( ~ r1_ordinal1(sK3(sK0),sK2(sK3(sK0)))
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(unit_resulting_resolution,[],[f136,f262,f25])).

fof(f25,plain,(
    ! [X2] :
      ( ~ r1_ordinal1(X2,sK2(X2))
      | ~ r2_hidden(X2,sK0)
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

% (1734)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (1724)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% (1739)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (1743)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (1727)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (1725)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% (1745)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (1738)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (1744)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% (1745)Refutation not found, incomplete strategy% (1745)------------------------------
% (1745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1745)Termination reason: Refutation not found, incomplete strategy

% (1745)Memory used [KB]: 10618
% (1745)Time elapsed: 0.150 s
% (1745)------------------------------
% (1745)------------------------------
% (1735)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (1737)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (1736)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f12,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( ~ r1_ordinal1(X2,X3)
              & r2_hidden(X3,X0)
              & v3_ordinal1(X3) )
          | ~ r2_hidden(X2,X0)
          | ~ v3_ordinal1(X2) )
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( ~ r1_ordinal1(X2,X3)
              & r2_hidden(X3,X0)
              & v3_ordinal1(X3) )
          | ~ r2_hidden(X2,X0)
          | ~ v3_ordinal1(X2) )
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1)
      & v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v3_ordinal1(X1)
       => ~ ( ! [X2] :
                ( v3_ordinal1(X2)
               => ~ ( ! [X3] :
                        ( v3_ordinal1(X3)
                       => ( r2_hidden(X3,X0)
                         => r1_ordinal1(X2,X3) ) )
                    & r2_hidden(X2,X0) ) )
            & k1_xboole_0 != X0
            & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ~ ( ! [X2] :
              ( v3_ordinal1(X2)
             => ~ ( ! [X3] :
                      ( v3_ordinal1(X3)
                     => ( r2_hidden(X3,X0)
                       => r1_ordinal1(X2,X3) ) )
                  & r2_hidden(X2,X0) ) )
          & k1_xboole_0 != X0
          & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_ordinal1)).

fof(f262,plain,
    ( r2_hidden(sK3(sK0),sK0)
    | ~ spl6_9 ),
    inference(unit_resulting_resolution,[],[f253,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

fof(f253,plain,
    ( r2_hidden(sK2(sK3(sK0)),sK0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl6_9
  <=> r2_hidden(sK2(sK3(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f261,plain,
    ( ~ r2_hidden(sK2(sK3(sK0)),sK3(sK0))
    | ~ spl6_9 ),
    inference(unit_resulting_resolution,[],[f253,f253,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,sK3(X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f133,plain,
    ( v3_ordinal1(sK2(sK3(sK0)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl6_7
  <=> v3_ordinal1(sK2(sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f136,plain,
    ( v3_ordinal1(sK3(sK0))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl6_8
  <=> v3_ordinal1(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f254,plain,
    ( spl6_6
    | spl6_9
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f79,f135,f251,f128])).

fof(f128,plain,
    ( spl6_6
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(sK3(sK0))
      | r2_hidden(sK2(sK3(sK0)),sK0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f24,f31])).

fof(f24,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | ~ v3_ordinal1(X2)
      | r2_hidden(sK2(X2),sK0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f243,plain,(
    ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f198,f226,f38])).

fof(f38,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | r2_hidden(sK5(X0),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
      | ? [X1] :
          ( ( ~ r1_tarski(X1,X0)
            | ~ v3_ordinal1(X1) )
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => ( r1_tarski(X1,X0)
            & v3_ordinal1(X1) ) )
     => v3_ordinal1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_ordinal1)).

fof(f226,plain,
    ( ~ v3_ordinal1(k1_xboole_0)
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f204,f129,f28,f198,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X0,X1)
      | X0 = X1
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f28,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f12])).

fof(f129,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f128])).

fof(f204,plain,
    ( v3_ordinal1(sK0)
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f129,f38])).

fof(f198,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f40,f129,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f197,plain,(
    spl6_8 ),
    inference(avatar_contradiction_clause,[],[f191])).

fof(f191,plain,
    ( $false
    | spl6_8 ),
    inference(unit_resulting_resolution,[],[f153,f181,f38])).

fof(f181,plain,
    ( ~ v3_ordinal1(k1_xboole_0)
    | spl6_8 ),
    inference(unit_resulting_resolution,[],[f159,f150,f28,f153,f39])).

fof(f150,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | spl6_8 ),
    inference(unit_resulting_resolution,[],[f148,f31])).

fof(f148,plain,
    ( ~ r2_hidden(sK3(sK0),sK0)
    | spl6_8 ),
    inference(unit_resulting_resolution,[],[f27,f143,f33])).

fof(f143,plain,
    ( ~ r2_hidden(sK3(sK0),sK1)
    | spl6_8 ),
    inference(unit_resulting_resolution,[],[f26,f137,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r2_hidden(X0,X1)
      | v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

fof(f137,plain,
    ( ~ v3_ordinal1(sK3(sK0))
    | spl6_8 ),
    inference(avatar_component_clause,[],[f135])).

fof(f26,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f27,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f159,plain,
    ( v3_ordinal1(sK0)
    | spl6_8 ),
    inference(unit_resulting_resolution,[],[f150,f38])).

fof(f153,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | spl6_8 ),
    inference(unit_resulting_resolution,[],[f40,f150,f33])).

fof(f138,plain,
    ( spl6_6
    | spl6_7
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f57,f135,f131,f128])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(sK3(sK0))
      | v3_ordinal1(sK2(sK3(sK0)))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f23,f31])).

fof(f23,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | ~ v3_ordinal1(X2)
      | v3_ordinal1(sK2(X2)) ) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:29:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (1728)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (1740)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (1718)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (1731)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (1723)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (1720)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (1741)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (1747)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (1721)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (1722)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (1726)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (1733)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (1719)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (1746)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (1730)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (1722)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f455,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f138,f197,f243,f254,f454])).
% 0.21/0.54  fof(f454,plain,(
% 0.21/0.54    ~spl6_7 | ~spl6_8 | ~spl6_9),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f451])).
% 0.21/0.54  fof(f451,plain,(
% 0.21/0.54    $false | (~spl6_7 | ~spl6_8 | ~spl6_9)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f136,f133,f261,f266,f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_ordinal1(X0,X1) | r2_hidden(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(flattening,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.21/0.54  fof(f266,plain,(
% 0.21/0.54    ~r1_ordinal1(sK3(sK0),sK2(sK3(sK0))) | (~spl6_8 | ~spl6_9)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f136,f262,f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ( ! [X2] : (~r1_ordinal1(X2,sK2(X2)) | ~r2_hidden(X2,sK0) | ~v3_ordinal1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  % (1734)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (1724)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (1739)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (1743)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (1727)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (1725)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (1745)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (1738)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (1744)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (1745)Refutation not found, incomplete strategy% (1745)------------------------------
% 0.21/0.55  % (1745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (1745)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (1745)Memory used [KB]: 10618
% 0.21/0.55  % (1745)Time elapsed: 0.150 s
% 0.21/0.55  % (1745)------------------------------
% 0.21/0.55  % (1745)------------------------------
% 0.21/0.55  % (1735)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (1737)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (1736)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  fof(f12,plain,(
% 0.21/0.55    ? [X0,X1] : (! [X2] : (? [X3] : (~r1_ordinal1(X2,X3) & r2_hidden(X3,X0) & v3_ordinal1(X3)) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) & k1_xboole_0 != X0 & r1_tarski(X0,X1) & v3_ordinal1(X1))),
% 0.21/0.55    inference(flattening,[],[f11])).
% 0.21/0.55  fof(f11,plain,(
% 0.21/0.55    ? [X0,X1] : ((! [X2] : ((? [X3] : ((~r1_ordinal1(X2,X3) & r2_hidden(X3,X0)) & v3_ordinal1(X3)) | ~r2_hidden(X2,X0)) | ~v3_ordinal1(X2)) & k1_xboole_0 != X0 & r1_tarski(X0,X1)) & v3_ordinal1(X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1] : (v3_ordinal1(X1) => ~(! [X2] : (v3_ordinal1(X2) => ~(! [X3] : (v3_ordinal1(X3) => (r2_hidden(X3,X0) => r1_ordinal1(X2,X3))) & r2_hidden(X2,X0))) & k1_xboole_0 != X0 & r1_tarski(X0,X1)))),
% 0.21/0.55    inference(negated_conjecture,[],[f9])).
% 0.21/0.55  fof(f9,conjecture,(
% 0.21/0.55    ! [X0,X1] : (v3_ordinal1(X1) => ~(! [X2] : (v3_ordinal1(X2) => ~(! [X3] : (v3_ordinal1(X3) => (r2_hidden(X3,X0) => r1_ordinal1(X2,X3))) & r2_hidden(X2,X0))) & k1_xboole_0 != X0 & r1_tarski(X0,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_ordinal1)).
% 0.21/0.55  fof(f262,plain,(
% 0.21/0.55    r2_hidden(sK3(sK0),sK0) | ~spl6_9),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f253,f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(sK3(X1),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).
% 0.21/0.55  fof(f253,plain,(
% 0.21/0.55    r2_hidden(sK2(sK3(sK0)),sK0) | ~spl6_9),
% 0.21/0.55    inference(avatar_component_clause,[],[f251])).
% 0.21/0.55  fof(f251,plain,(
% 0.21/0.55    spl6_9 <=> r2_hidden(sK2(sK3(sK0)),sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.55  fof(f261,plain,(
% 0.21/0.55    ~r2_hidden(sK2(sK3(sK0)),sK3(sK0)) | ~spl6_9),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f253,f253,f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ( ! [X0,X3,X1] : (~r2_hidden(X3,sK3(X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f15])).
% 0.21/0.55  fof(f133,plain,(
% 0.21/0.55    v3_ordinal1(sK2(sK3(sK0))) | ~spl6_7),
% 0.21/0.55    inference(avatar_component_clause,[],[f131])).
% 0.21/0.55  fof(f131,plain,(
% 0.21/0.55    spl6_7 <=> v3_ordinal1(sK2(sK3(sK0)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.55  fof(f136,plain,(
% 0.21/0.55    v3_ordinal1(sK3(sK0)) | ~spl6_8),
% 0.21/0.55    inference(avatar_component_clause,[],[f135])).
% 0.21/0.55  fof(f135,plain,(
% 0.21/0.55    spl6_8 <=> v3_ordinal1(sK3(sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.55  fof(f254,plain,(
% 0.21/0.55    spl6_6 | spl6_9 | ~spl6_8),
% 0.21/0.55    inference(avatar_split_clause,[],[f79,f135,f251,f128])).
% 0.21/0.55  fof(f128,plain,(
% 0.21/0.55    spl6_6 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    ( ! [X0] : (~v3_ordinal1(sK3(sK0)) | r2_hidden(sK2(sK3(sK0)),sK0) | ~r2_hidden(X0,sK0)) )),
% 0.21/0.55    inference(resolution,[],[f24,f31])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ( ! [X2] : (~r2_hidden(X2,sK0) | ~v3_ordinal1(X2) | r2_hidden(sK2(X2),sK0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f12])).
% 0.21/0.55  fof(f243,plain,(
% 0.21/0.55    ~spl6_6),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f236])).
% 0.21/0.55  fof(f236,plain,(
% 0.21/0.55    $false | ~spl6_6),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f198,f226,f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ( ! [X0] : (v3_ordinal1(X0) | r2_hidden(sK5(X0),X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0] : (v3_ordinal1(X0) | ? [X1] : ((~r1_tarski(X1,X0) | ~v3_ordinal1(X1)) & r2_hidden(X1,X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0] : (! [X1] : (r2_hidden(X1,X0) => (r1_tarski(X1,X0) & v3_ordinal1(X1))) => v3_ordinal1(X0))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_ordinal1)).
% 0.21/0.55  fof(f226,plain,(
% 0.21/0.55    ~v3_ordinal1(k1_xboole_0) | ~spl6_6),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f204,f129,f28,f198,f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r2_hidden(X0,X1) | X0 = X1 | r2_hidden(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.55    inference(flattening,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    k1_xboole_0 != sK0),
% 0.21/0.55    inference(cnf_transformation,[],[f12])).
% 0.21/0.55  fof(f129,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl6_6),
% 0.21/0.55    inference(avatar_component_clause,[],[f128])).
% 0.21/0.55  fof(f204,plain,(
% 0.21/0.55    v3_ordinal1(sK0) | ~spl6_6),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f129,f38])).
% 0.21/0.55  fof(f198,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl6_6),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f40,f129,f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.55  fof(f197,plain,(
% 0.21/0.55    spl6_8),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f191])).
% 0.21/0.55  fof(f191,plain,(
% 0.21/0.55    $false | spl6_8),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f153,f181,f38])).
% 0.21/0.55  fof(f181,plain,(
% 0.21/0.55    ~v3_ordinal1(k1_xboole_0) | spl6_8),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f159,f150,f28,f153,f39])).
% 0.21/0.55  fof(f150,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | spl6_8),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f148,f31])).
% 0.21/0.55  fof(f148,plain,(
% 0.21/0.55    ~r2_hidden(sK3(sK0),sK0) | spl6_8),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f27,f143,f33])).
% 0.21/0.55  fof(f143,plain,(
% 0.21/0.55    ~r2_hidden(sK3(sK0),sK1) | spl6_8),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f26,f137,f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~r2_hidden(X0,X1) | v3_ordinal1(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 0.21/0.55    inference(flattening,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).
% 0.21/0.55  fof(f137,plain,(
% 0.21/0.55    ~v3_ordinal1(sK3(sK0)) | spl6_8),
% 0.21/0.55    inference(avatar_component_clause,[],[f135])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    v3_ordinal1(sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f12])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    r1_tarski(sK0,sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f12])).
% 0.21/0.55  fof(f159,plain,(
% 0.21/0.55    v3_ordinal1(sK0) | spl6_8),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f150,f38])).
% 0.21/0.55  fof(f153,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | spl6_8),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f40,f150,f33])).
% 0.21/0.55  fof(f138,plain,(
% 0.21/0.55    spl6_6 | spl6_7 | ~spl6_8),
% 0.21/0.55    inference(avatar_split_clause,[],[f57,f135,f131,f128])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    ( ! [X0] : (~v3_ordinal1(sK3(sK0)) | v3_ordinal1(sK2(sK3(sK0))) | ~r2_hidden(X0,sK0)) )),
% 0.21/0.55    inference(resolution,[],[f23,f31])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ( ! [X2] : (~r2_hidden(X2,sK0) | ~v3_ordinal1(X2) | v3_ordinal1(sK2(X2))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f12])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (1722)------------------------------
% 0.21/0.55  % (1722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (1722)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (1722)Memory used [KB]: 6396
% 0.21/0.55  % (1722)Time elapsed: 0.145 s
% 0.21/0.55  % (1722)------------------------------
% 0.21/0.55  % (1722)------------------------------
% 0.21/0.55  % (1732)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (1742)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.56  % (1717)Success in time 0.197 s
%------------------------------------------------------------------------------
