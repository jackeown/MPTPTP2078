%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:57 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 115 expanded)
%              Number of leaves         :   17 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :  195 ( 327 expanded)
%              Number of equality atoms :   40 (  63 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f464,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f68,f73,f85,f90,f108,f128,f172,f463])).

fof(f463,plain,
    ( ~ spl7_4
    | spl7_5
    | ~ spl7_8
    | ~ spl7_15 ),
    inference(avatar_contradiction_clause,[],[f459])).

fof(f459,plain,
    ( $false
    | ~ spl7_4
    | spl7_5
    | ~ spl7_8
    | ~ spl7_15 ),
    inference(resolution,[],[f370,f54])).

fof(f54,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f370,plain,
    ( ! [X4] : ~ r1_tarski(X4,sK3(k1_xboole_0))
    | ~ spl7_4
    | spl7_5
    | ~ spl7_8
    | ~ spl7_15 ),
    inference(forward_demodulation,[],[f348,f26])).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f348,plain,
    ( ! [X4] : ~ r1_tarski(k2_xboole_0(X4,k1_xboole_0),sK3(k1_xboole_0))
    | ~ spl7_4
    | spl7_5
    | ~ spl7_8
    | ~ spl7_15 ),
    inference(backward_demodulation,[],[f263,f309])).

fof(f309,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_4
    | spl7_5
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f308,f89])).

fof(f89,plain,
    ( sK0 != sK1
    | spl7_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl7_5
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f308,plain,
    ( sK0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_4
    | ~ spl7_15 ),
    inference(resolution,[],[f178,f84])).

fof(f84,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl7_4
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

% (26113)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (26089)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% (26090)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% (26095)Refutation not found, incomplete strategy% (26095)------------------------------
% (26095)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26095)Termination reason: Refutation not found, incomplete strategy

% (26095)Memory used [KB]: 10618
% (26095)Time elapsed: 0.148 s
% (26095)------------------------------
% (26095)------------------------------
% (26097)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (26111)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% (26105)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f178,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | sK1 = X0
        | k1_xboole_0 = X0 )
    | ~ spl7_15 ),
    inference(superposition,[],[f40,f171])).

fof(f171,plain,
    ( sK1 = k1_tarski(sK2(sK1))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl7_15
  <=> sK1 = k1_tarski(sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f263,plain,
    ( ! [X4] : ~ r1_tarski(k2_xboole_0(X4,sK0),sK3(sK0))
    | ~ spl7_8 ),
    inference(resolution,[],[f166,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f166,plain,
    ( ! [X1] : r2_hidden(sK3(sK0),k2_xboole_0(X1,sK0))
    | ~ spl7_8 ),
    inference(resolution,[],[f115,f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f115,plain,
    ( ! [X1] : sP6(sK3(sK0),sK0,X1)
    | ~ spl7_8 ),
    inference(resolution,[],[f107,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | sP6(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f107,plain,
    ( r2_hidden(sK3(sK0),sK0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl7_8
  <=> r2_hidden(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f172,plain,
    ( spl7_15
    | spl7_1
    | ~ spl7_2
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f148,f125,f65,f60,f169])).

fof(f60,plain,
    ( spl7_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f65,plain,
    ( spl7_2
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f125,plain,
    ( spl7_10
  <=> sK1 = k6_domain_1(sK1,sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f148,plain,
    ( sK1 = k1_tarski(sK2(sK1))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_10 ),
    inference(forward_demodulation,[],[f147,f127])).

fof(f127,plain,
    ( sK1 = k6_domain_1(sK1,sK2(sK1))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f125])).

fof(f147,plain,
    ( k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f146,f67])).

fof(f67,plain,
    ( v1_zfmisc_1(sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f146,plain,
    ( k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))
    | ~ v1_zfmisc_1(sK1)
    | spl7_1 ),
    inference(subsumption_resolution,[],[f145,f62])).

fof(f62,plain,
    ( ~ v1_xboole_0(sK1)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f145,plain,
    ( k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))
    | v1_xboole_0(sK1)
    | ~ v1_zfmisc_1(sK1)
    | spl7_1 ),
    inference(resolution,[],[f74,f27])).

fof(f27,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),X0)
      | v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

fof(f74,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k1_tarski(X0) = k6_domain_1(sK1,X0) )
    | spl7_1 ),
    inference(resolution,[],[f62,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f128,plain,
    ( spl7_10
    | spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f77,f65,f60,f125])).

fof(f77,plain,
    ( sK1 = k6_domain_1(sK1,sK2(sK1))
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f76,f67])).

fof(f76,plain,
    ( sK1 = k6_domain_1(sK1,sK2(sK1))
    | ~ v1_zfmisc_1(sK1)
    | spl7_1 ),
    inference(resolution,[],[f62,f28])).

fof(f28,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | k6_domain_1(X0,sK2(X0)) = X0
      | ~ v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f108,plain,
    ( spl7_8
    | spl7_3 ),
    inference(avatar_split_clause,[],[f79,f70,f105])).

fof(f70,plain,
    ( spl7_3
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f79,plain,
    ( r2_hidden(sK3(sK0),sK0)
    | spl7_3 ),
    inference(resolution,[],[f72,f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f72,plain,
    ( ~ v1_xboole_0(sK0)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f90,plain,(
    ~ spl7_5 ),
    inference(avatar_split_clause,[],[f24,f87])).

fof(f24,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f85,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f23,f82])).

fof(f23,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f73,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f25,f70])).

fof(f25,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f68,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f22,f65])).

fof(f22,plain,(
    v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f63,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f21,f60])).

fof(f21,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:10:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (26091)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (26094)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.50  % (26084)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (26086)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (26094)Refutation not found, incomplete strategy% (26094)------------------------------
% 0.20/0.51  % (26094)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (26099)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (26103)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.51  % (26094)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (26094)Memory used [KB]: 10618
% 0.20/0.51  % (26094)Time elapsed: 0.093 s
% 0.20/0.51  % (26094)------------------------------
% 0.20/0.51  % (26094)------------------------------
% 0.20/0.52  % (26107)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (26086)Refutation not found, incomplete strategy% (26086)------------------------------
% 0.20/0.52  % (26086)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (26086)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (26086)Memory used [KB]: 10746
% 0.20/0.52  % (26086)Time elapsed: 0.103 s
% 0.20/0.52  % (26086)------------------------------
% 0.20/0.52  % (26086)------------------------------
% 0.20/0.52  % (26088)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (26106)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.36/0.53  % (26087)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.36/0.53  % (26098)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.36/0.53  % (26096)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.53  % (26108)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.36/0.53  % (26093)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.36/0.54  % (26095)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.36/0.54  % (26110)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.36/0.54  % (26101)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.36/0.54  % (26112)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.36/0.54  % (26085)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.36/0.54  % (26106)Refutation not found, incomplete strategy% (26106)------------------------------
% 1.36/0.54  % (26106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (26106)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (26106)Memory used [KB]: 10746
% 1.36/0.54  % (26101)Refutation not found, incomplete strategy% (26101)------------------------------
% 1.36/0.54  % (26101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (26106)Time elapsed: 0.083 s
% 1.36/0.54  % (26106)------------------------------
% 1.36/0.54  % (26106)------------------------------
% 1.36/0.54  % (26101)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (26101)Memory used [KB]: 10746
% 1.36/0.54  % (26101)Time elapsed: 0.139 s
% 1.36/0.54  % (26101)------------------------------
% 1.36/0.54  % (26101)------------------------------
% 1.44/0.55  % (26104)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.44/0.55  % (26092)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.44/0.55  % (26109)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.44/0.55  % (26100)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.44/0.55  % (26102)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.44/0.55  % (26104)Refutation found. Thanks to Tanya!
% 1.44/0.55  % SZS status Theorem for theBenchmark
% 1.44/0.55  % SZS output start Proof for theBenchmark
% 1.44/0.55  fof(f464,plain,(
% 1.44/0.55    $false),
% 1.44/0.55    inference(avatar_sat_refutation,[],[f63,f68,f73,f85,f90,f108,f128,f172,f463])).
% 1.44/0.55  fof(f463,plain,(
% 1.44/0.55    ~spl7_4 | spl7_5 | ~spl7_8 | ~spl7_15),
% 1.44/0.55    inference(avatar_contradiction_clause,[],[f459])).
% 1.44/0.55  fof(f459,plain,(
% 1.44/0.55    $false | (~spl7_4 | spl7_5 | ~spl7_8 | ~spl7_15)),
% 1.44/0.55    inference(resolution,[],[f370,f54])).
% 1.44/0.55  fof(f54,plain,(
% 1.44/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.44/0.55    inference(equality_resolution,[],[f34])).
% 1.44/0.55  fof(f34,plain,(
% 1.44/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.44/0.55    inference(cnf_transformation,[],[f4])).
% 1.44/0.55  fof(f4,axiom,(
% 1.44/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.44/0.55  fof(f370,plain,(
% 1.44/0.55    ( ! [X4] : (~r1_tarski(X4,sK3(k1_xboole_0))) ) | (~spl7_4 | spl7_5 | ~spl7_8 | ~spl7_15)),
% 1.44/0.55    inference(forward_demodulation,[],[f348,f26])).
% 1.44/0.55  fof(f26,plain,(
% 1.44/0.55    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.44/0.55    inference(cnf_transformation,[],[f6])).
% 1.44/0.55  fof(f6,axiom,(
% 1.44/0.55    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.44/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.44/0.55  fof(f348,plain,(
% 1.44/0.55    ( ! [X4] : (~r1_tarski(k2_xboole_0(X4,k1_xboole_0),sK3(k1_xboole_0))) ) | (~spl7_4 | spl7_5 | ~spl7_8 | ~spl7_15)),
% 1.44/0.55    inference(backward_demodulation,[],[f263,f309])).
% 1.44/0.55  fof(f309,plain,(
% 1.44/0.55    k1_xboole_0 = sK0 | (~spl7_4 | spl7_5 | ~spl7_15)),
% 1.44/0.55    inference(subsumption_resolution,[],[f308,f89])).
% 1.44/0.55  fof(f89,plain,(
% 1.44/0.55    sK0 != sK1 | spl7_5),
% 1.44/0.55    inference(avatar_component_clause,[],[f87])).
% 1.44/0.55  fof(f87,plain,(
% 1.44/0.55    spl7_5 <=> sK0 = sK1),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.44/0.55  fof(f308,plain,(
% 1.44/0.55    sK0 = sK1 | k1_xboole_0 = sK0 | (~spl7_4 | ~spl7_15)),
% 1.44/0.55    inference(resolution,[],[f178,f84])).
% 1.44/0.55  fof(f84,plain,(
% 1.44/0.55    r1_tarski(sK0,sK1) | ~spl7_4),
% 1.44/0.55    inference(avatar_component_clause,[],[f82])).
% 1.44/0.55  fof(f82,plain,(
% 1.44/0.55    spl7_4 <=> r1_tarski(sK0,sK1)),
% 1.44/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.44/0.55  % (26113)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.44/0.55  % (26089)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.44/0.56  % (26090)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.44/0.56  % (26095)Refutation not found, incomplete strategy% (26095)------------------------------
% 1.44/0.56  % (26095)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (26095)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.56  
% 1.44/0.56  % (26095)Memory used [KB]: 10618
% 1.44/0.56  % (26095)Time elapsed: 0.148 s
% 1.44/0.56  % (26095)------------------------------
% 1.44/0.56  % (26095)------------------------------
% 1.44/0.56  % (26097)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.44/0.56  % (26111)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.44/0.57  % (26105)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.44/0.57  fof(f178,plain,(
% 1.44/0.57    ( ! [X0] : (~r1_tarski(X0,sK1) | sK1 = X0 | k1_xboole_0 = X0) ) | ~spl7_15),
% 1.44/0.57    inference(superposition,[],[f40,f171])).
% 1.44/0.57  fof(f171,plain,(
% 1.44/0.57    sK1 = k1_tarski(sK2(sK1)) | ~spl7_15),
% 1.44/0.57    inference(avatar_component_clause,[],[f169])).
% 1.44/0.57  fof(f169,plain,(
% 1.44/0.57    spl7_15 <=> sK1 = k1_tarski(sK2(sK1))),
% 1.44/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 1.44/0.57  fof(f40,plain,(
% 1.44/0.57    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) = X0 | k1_xboole_0 = X0) )),
% 1.44/0.57    inference(cnf_transformation,[],[f8])).
% 1.44/0.57  fof(f8,axiom,(
% 1.44/0.57    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.44/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.44/0.57  fof(f263,plain,(
% 1.44/0.57    ( ! [X4] : (~r1_tarski(k2_xboole_0(X4,sK0),sK3(sK0))) ) | ~spl7_8),
% 1.44/0.57    inference(resolution,[],[f166,f45])).
% 1.44/0.57  fof(f45,plain,(
% 1.44/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f20])).
% 1.44/0.57  fof(f20,plain,(
% 1.44/0.57    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.44/0.57    inference(ennf_transformation,[],[f9])).
% 1.44/0.57  fof(f9,axiom,(
% 1.44/0.57    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.44/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.44/0.57  fof(f166,plain,(
% 1.44/0.57    ( ! [X1] : (r2_hidden(sK3(sK0),k2_xboole_0(X1,sK0))) ) | ~spl7_8),
% 1.44/0.57    inference(resolution,[],[f115,f58])).
% 1.44/0.57  fof(f58,plain,(
% 1.44/0.57    ( ! [X0,X3,X1] : (~sP6(X3,X1,X0) | r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 1.44/0.57    inference(equality_resolution,[],[f49])).
% 1.44/0.57  fof(f49,plain,(
% 1.44/0.57    ( ! [X2,X0,X3,X1] : (~sP6(X3,X1,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.44/0.57    inference(cnf_transformation,[],[f3])).
% 1.44/0.57  fof(f3,axiom,(
% 1.44/0.57    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.44/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.44/0.57  fof(f115,plain,(
% 1.44/0.57    ( ! [X1] : (sP6(sK3(sK0),sK0,X1)) ) | ~spl7_8),
% 1.44/0.57    inference(resolution,[],[f107,f47])).
% 1.44/0.57  fof(f47,plain,(
% 1.44/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | sP6(X3,X1,X0)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f3])).
% 1.44/0.57  fof(f107,plain,(
% 1.44/0.57    r2_hidden(sK3(sK0),sK0) | ~spl7_8),
% 1.44/0.57    inference(avatar_component_clause,[],[f105])).
% 1.44/0.57  fof(f105,plain,(
% 1.44/0.57    spl7_8 <=> r2_hidden(sK3(sK0),sK0)),
% 1.44/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.44/0.57  fof(f172,plain,(
% 1.44/0.57    spl7_15 | spl7_1 | ~spl7_2 | ~spl7_10),
% 1.44/0.57    inference(avatar_split_clause,[],[f148,f125,f65,f60,f169])).
% 1.44/0.57  fof(f60,plain,(
% 1.44/0.57    spl7_1 <=> v1_xboole_0(sK1)),
% 1.44/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.44/0.57  fof(f65,plain,(
% 1.44/0.57    spl7_2 <=> v1_zfmisc_1(sK1)),
% 1.44/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.44/0.57  fof(f125,plain,(
% 1.44/0.57    spl7_10 <=> sK1 = k6_domain_1(sK1,sK2(sK1))),
% 1.44/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.44/0.57  fof(f148,plain,(
% 1.44/0.57    sK1 = k1_tarski(sK2(sK1)) | (spl7_1 | ~spl7_2 | ~spl7_10)),
% 1.44/0.57    inference(forward_demodulation,[],[f147,f127])).
% 1.44/0.57  fof(f127,plain,(
% 1.44/0.57    sK1 = k6_domain_1(sK1,sK2(sK1)) | ~spl7_10),
% 1.44/0.57    inference(avatar_component_clause,[],[f125])).
% 1.44/0.57  fof(f147,plain,(
% 1.44/0.57    k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1)) | (spl7_1 | ~spl7_2)),
% 1.44/0.57    inference(subsumption_resolution,[],[f146,f67])).
% 1.44/0.57  fof(f67,plain,(
% 1.44/0.57    v1_zfmisc_1(sK1) | ~spl7_2),
% 1.44/0.57    inference(avatar_component_clause,[],[f65])).
% 1.44/0.57  fof(f146,plain,(
% 1.44/0.57    k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1)) | ~v1_zfmisc_1(sK1) | spl7_1),
% 1.44/0.57    inference(subsumption_resolution,[],[f145,f62])).
% 1.44/0.57  fof(f62,plain,(
% 1.44/0.57    ~v1_xboole_0(sK1) | spl7_1),
% 1.44/0.57    inference(avatar_component_clause,[],[f60])).
% 1.44/0.57  fof(f145,plain,(
% 1.44/0.57    k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1)) | v1_xboole_0(sK1) | ~v1_zfmisc_1(sK1) | spl7_1),
% 1.44/0.57    inference(resolution,[],[f74,f27])).
% 1.44/0.57  fof(f27,plain,(
% 1.44/0.57    ( ! [X0] : (m1_subset_1(sK2(X0),X0) | v1_xboole_0(X0) | ~v1_zfmisc_1(X0)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f16])).
% 1.44/0.57  fof(f16,plain,(
% 1.44/0.57    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 1.44/0.57    inference(ennf_transformation,[],[f11])).
% 1.44/0.57  fof(f11,axiom,(
% 1.44/0.57    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 1.44/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).
% 1.44/0.57  fof(f74,plain,(
% 1.44/0.57    ( ! [X0] : (~m1_subset_1(X0,sK1) | k1_tarski(X0) = k6_domain_1(sK1,X0)) ) | spl7_1),
% 1.44/0.57    inference(resolution,[],[f62,f33])).
% 1.44/0.57  fof(f33,plain,(
% 1.44/0.57    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k1_tarski(X1) = k6_domain_1(X0,X1)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f18])).
% 1.44/0.57  fof(f18,plain,(
% 1.44/0.57    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.44/0.57    inference(flattening,[],[f17])).
% 1.44/0.57  fof(f17,plain,(
% 1.44/0.57    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.44/0.57    inference(ennf_transformation,[],[f10])).
% 1.44/0.57  fof(f10,axiom,(
% 1.44/0.57    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 1.44/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.44/0.57  fof(f128,plain,(
% 1.44/0.57    spl7_10 | spl7_1 | ~spl7_2),
% 1.44/0.57    inference(avatar_split_clause,[],[f77,f65,f60,f125])).
% 1.44/0.57  fof(f77,plain,(
% 1.44/0.57    sK1 = k6_domain_1(sK1,sK2(sK1)) | (spl7_1 | ~spl7_2)),
% 1.44/0.57    inference(subsumption_resolution,[],[f76,f67])).
% 1.44/0.57  fof(f76,plain,(
% 1.44/0.57    sK1 = k6_domain_1(sK1,sK2(sK1)) | ~v1_zfmisc_1(sK1) | spl7_1),
% 1.44/0.57    inference(resolution,[],[f62,f28])).
% 1.44/0.57  fof(f28,plain,(
% 1.44/0.57    ( ! [X0] : (v1_xboole_0(X0) | k6_domain_1(X0,sK2(X0)) = X0 | ~v1_zfmisc_1(X0)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f16])).
% 1.44/0.57  fof(f108,plain,(
% 1.44/0.57    spl7_8 | spl7_3),
% 1.44/0.57    inference(avatar_split_clause,[],[f79,f70,f105])).
% 1.44/0.57  fof(f70,plain,(
% 1.44/0.57    spl7_3 <=> v1_xboole_0(sK0)),
% 1.44/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.44/0.57  fof(f79,plain,(
% 1.44/0.57    r2_hidden(sK3(sK0),sK0) | spl7_3),
% 1.44/0.57    inference(resolution,[],[f72,f30])).
% 1.44/0.57  fof(f30,plain,(
% 1.44/0.57    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f1])).
% 1.44/0.57  fof(f1,axiom,(
% 1.44/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.44/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.44/0.57  fof(f72,plain,(
% 1.44/0.57    ~v1_xboole_0(sK0) | spl7_3),
% 1.44/0.57    inference(avatar_component_clause,[],[f70])).
% 1.44/0.57  fof(f90,plain,(
% 1.44/0.57    ~spl7_5),
% 1.44/0.57    inference(avatar_split_clause,[],[f24,f87])).
% 1.44/0.57  fof(f24,plain,(
% 1.44/0.57    sK0 != sK1),
% 1.44/0.57    inference(cnf_transformation,[],[f15])).
% 1.44/0.57  fof(f15,plain,(
% 1.44/0.57    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.44/0.57    inference(flattening,[],[f14])).
% 1.44/0.57  fof(f14,plain,(
% 1.44/0.57    ? [X0] : (? [X1] : ((X0 != X1 & r1_tarski(X0,X1)) & (v1_zfmisc_1(X1) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 1.44/0.57    inference(ennf_transformation,[],[f13])).
% 1.44/0.57  fof(f13,negated_conjecture,(
% 1.44/0.57    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.44/0.57    inference(negated_conjecture,[],[f12])).
% 1.44/0.57  fof(f12,conjecture,(
% 1.44/0.57    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.44/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 1.44/0.57  fof(f85,plain,(
% 1.44/0.57    spl7_4),
% 1.44/0.57    inference(avatar_split_clause,[],[f23,f82])).
% 1.44/0.57  fof(f23,plain,(
% 1.44/0.57    r1_tarski(sK0,sK1)),
% 1.44/0.57    inference(cnf_transformation,[],[f15])).
% 1.44/0.57  fof(f73,plain,(
% 1.44/0.57    ~spl7_3),
% 1.44/0.57    inference(avatar_split_clause,[],[f25,f70])).
% 1.44/0.57  fof(f25,plain,(
% 1.44/0.57    ~v1_xboole_0(sK0)),
% 1.44/0.57    inference(cnf_transformation,[],[f15])).
% 1.44/0.57  fof(f68,plain,(
% 1.44/0.57    spl7_2),
% 1.44/0.57    inference(avatar_split_clause,[],[f22,f65])).
% 1.44/0.57  fof(f22,plain,(
% 1.44/0.57    v1_zfmisc_1(sK1)),
% 1.44/0.57    inference(cnf_transformation,[],[f15])).
% 1.44/0.57  fof(f63,plain,(
% 1.44/0.57    ~spl7_1),
% 1.44/0.57    inference(avatar_split_clause,[],[f21,f60])).
% 1.44/0.57  fof(f21,plain,(
% 1.44/0.57    ~v1_xboole_0(sK1)),
% 1.44/0.57    inference(cnf_transformation,[],[f15])).
% 1.44/0.57  % SZS output end Proof for theBenchmark
% 1.44/0.57  % (26104)------------------------------
% 1.44/0.57  % (26104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.57  % (26104)Termination reason: Refutation
% 1.44/0.57  
% 1.44/0.57  % (26104)Memory used [KB]: 11001
% 1.44/0.57  % (26104)Time elapsed: 0.148 s
% 1.44/0.57  % (26104)------------------------------
% 1.44/0.57  % (26104)------------------------------
% 1.44/0.58  % (26083)Success in time 0.218 s
%------------------------------------------------------------------------------
