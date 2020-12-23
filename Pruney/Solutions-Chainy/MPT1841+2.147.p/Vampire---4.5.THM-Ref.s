%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:29 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 133 expanded)
%              Number of leaves         :   24 (  53 expanded)
%              Depth                    :    9
%              Number of atoms          :  203 ( 308 expanded)
%              Number of equality atoms :   30 (  42 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f259,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f57,f62,f67,f84,f90,f98,f106,f158,f238,f256,f258])).

fof(f258,plain,(
    ~ spl4_22 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | ~ spl4_22 ),
    inference(resolution,[],[f255,f68])).

fof(f68,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f29,f30])).

fof(f30,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f29,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

fof(f255,plain,
    ( v1_subset_1(sK0,sK0)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl4_22
  <=> v1_subset_1(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f256,plain,
    ( spl4_22
    | ~ spl4_6
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f240,f155,f87,f253])).

fof(f87,plain,
    ( spl4_6
  <=> v1_subset_1(k1_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f155,plain,
    ( spl4_18
  <=> sK0 = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f240,plain,
    ( v1_subset_1(sK0,sK0)
    | ~ spl4_6
    | ~ spl4_18 ),
    inference(backward_demodulation,[],[f89,f157])).

fof(f157,plain,
    ( sK0 = k1_tarski(sK1)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f155])).

fof(f89,plain,
    ( v1_subset_1(k1_tarski(sK1),sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f238,plain,(
    ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | ~ spl4_12 ),
    inference(equality_resolution,[],[f233])).

fof(f233,plain,
    ( ! [X0] : k1_xboole_0 != X0
    | ~ spl4_12 ),
    inference(superposition,[],[f46,f187])).

fof(f187,plain,
    ( ! [X2] : k5_xboole_0(k1_tarski(sK1),k5_xboole_0(X2,k3_xboole_0(X2,k1_tarski(sK1)))) = X2
    | ~ spl4_12 ),
    inference(resolution,[],[f171,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 ) ),
    inference(definition_unfolding,[],[f37,f45])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f36,f35])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f171,plain,
    ( ! [X0] : r1_tarski(k1_tarski(sK1),X0)
    | ~ spl4_12 ),
    inference(resolution,[],[f127,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f41,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f127,plain,
    ( v1_xboole_0(k1_tarski(sK1))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl4_12
  <=> v1_xboole_0(k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f46,plain,(
    ! [X0,X1] : k1_xboole_0 != k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k3_xboole_0(X1,k1_tarski(X0)))) ),
    inference(definition_unfolding,[],[f34,f45])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f158,plain,
    ( spl4_18
    | spl4_12
    | ~ spl4_2
    | spl4_1
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f136,f103,f49,f54,f125,f155])).

fof(f54,plain,
    ( spl4_2
  <=> v1_zfmisc_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f49,plain,
    ( spl4_1
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f103,plain,
    ( spl4_8
  <=> r1_tarski(k1_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f136,plain,
    ( v1_xboole_0(sK0)
    | ~ v1_zfmisc_1(sK0)
    | v1_xboole_0(k1_tarski(sK1))
    | sK0 = k1_tarski(sK1)
    | ~ spl4_8 ),
    inference(resolution,[],[f31,f105])).

fof(f105,plain,
    ( r1_tarski(k1_tarski(sK1),sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f103])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | v1_xboole_0(X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f106,plain,
    ( spl4_8
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f99,f95,f103])).

fof(f95,plain,
    ( spl4_7
  <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f99,plain,
    ( r1_tarski(k1_tarski(sK1),sK0)
    | ~ spl4_7 ),
    inference(resolution,[],[f97,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f97,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f95])).

fof(f98,plain,
    ( spl4_1
    | spl4_7
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f93,f81,f64,f95,f49])).

fof(f64,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f81,plain,
    ( spl4_5
  <=> k6_domain_1(sK0,sK1) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f93,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0)
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f91,f83])).

fof(f83,plain,
    ( k6_domain_1(sK0,sK1) = k1_tarski(sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f91,plain,
    ( v1_xboole_0(sK0)
    | m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(resolution,[],[f39,f66])).

fof(f66,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

% (4209)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f90,plain,
    ( spl4_6
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f85,f81,f59,f87])).

fof(f59,plain,
    ( spl4_3
  <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f85,plain,
    ( v1_subset_1(k1_tarski(sK1),sK0)
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f61,f83])).

% (4214)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f61,plain,
    ( v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f84,plain,
    ( spl4_5
    | spl4_1
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f78,f64,f49,f81])).

fof(f78,plain,
    ( v1_xboole_0(sK0)
    | k6_domain_1(sK0,sK1) = k1_tarski(sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f38,f66])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f67,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f25,f64])).

fof(f25,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

fof(f62,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f26,f59])).

fof(f26,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f57,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f27,f54])).

fof(f27,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f52,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f28,f49])).

fof(f28,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:59:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (4215)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (4208)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (4215)Refutation not found, incomplete strategy% (4215)------------------------------
% 0.21/0.52  % (4215)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (4215)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (4215)Memory used [KB]: 10746
% 0.21/0.52  % (4215)Time elapsed: 0.095 s
% 0.21/0.52  % (4215)------------------------------
% 0.21/0.52  % (4215)------------------------------
% 0.21/0.52  % (4210)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (4212)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (4216)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (4216)Refutation not found, incomplete strategy% (4216)------------------------------
% 0.21/0.53  % (4216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4216)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (4216)Memory used [KB]: 10618
% 0.21/0.53  % (4216)Time elapsed: 0.107 s
% 0.21/0.53  % (4216)------------------------------
% 0.21/0.53  % (4216)------------------------------
% 0.21/0.53  % (4223)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (4225)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.30/0.54  % (4223)Refutation found. Thanks to Tanya!
% 1.30/0.54  % SZS status Theorem for theBenchmark
% 1.30/0.54  % SZS output start Proof for theBenchmark
% 1.30/0.54  fof(f259,plain,(
% 1.30/0.54    $false),
% 1.30/0.54    inference(avatar_sat_refutation,[],[f52,f57,f62,f67,f84,f90,f98,f106,f158,f238,f256,f258])).
% 1.30/0.54  fof(f258,plain,(
% 1.30/0.54    ~spl4_22),
% 1.30/0.54    inference(avatar_contradiction_clause,[],[f257])).
% 1.30/0.54  fof(f257,plain,(
% 1.30/0.54    $false | ~spl4_22),
% 1.30/0.54    inference(resolution,[],[f255,f68])).
% 1.30/0.54  fof(f68,plain,(
% 1.30/0.54    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 1.30/0.54    inference(backward_demodulation,[],[f29,f30])).
% 1.30/0.54  fof(f30,plain,(
% 1.30/0.54    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.30/0.54    inference(cnf_transformation,[],[f7])).
% 1.30/0.54  fof(f7,axiom,(
% 1.30/0.54    ! [X0] : k2_subset_1(X0) = X0),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.30/0.54  fof(f29,plain,(
% 1.30/0.54    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f8])).
% 1.30/0.54  fof(f8,axiom,(
% 1.30/0.54    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).
% 1.30/0.54  fof(f255,plain,(
% 1.30/0.54    v1_subset_1(sK0,sK0) | ~spl4_22),
% 1.30/0.54    inference(avatar_component_clause,[],[f253])).
% 1.30/0.54  fof(f253,plain,(
% 1.30/0.54    spl4_22 <=> v1_subset_1(sK0,sK0)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.30/0.54  fof(f256,plain,(
% 1.30/0.54    spl4_22 | ~spl4_6 | ~spl4_18),
% 1.30/0.54    inference(avatar_split_clause,[],[f240,f155,f87,f253])).
% 1.30/0.54  fof(f87,plain,(
% 1.30/0.54    spl4_6 <=> v1_subset_1(k1_tarski(sK1),sK0)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.30/0.54  fof(f155,plain,(
% 1.30/0.54    spl4_18 <=> sK0 = k1_tarski(sK1)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.30/0.54  fof(f240,plain,(
% 1.30/0.54    v1_subset_1(sK0,sK0) | (~spl4_6 | ~spl4_18)),
% 1.30/0.54    inference(backward_demodulation,[],[f89,f157])).
% 1.30/0.54  fof(f157,plain,(
% 1.30/0.54    sK0 = k1_tarski(sK1) | ~spl4_18),
% 1.30/0.54    inference(avatar_component_clause,[],[f155])).
% 1.30/0.54  fof(f89,plain,(
% 1.30/0.54    v1_subset_1(k1_tarski(sK1),sK0) | ~spl4_6),
% 1.30/0.54    inference(avatar_component_clause,[],[f87])).
% 1.30/0.54  fof(f238,plain,(
% 1.30/0.54    ~spl4_12),
% 1.30/0.54    inference(avatar_contradiction_clause,[],[f237])).
% 1.30/0.54  fof(f237,plain,(
% 1.30/0.54    $false | ~spl4_12),
% 1.30/0.54    inference(equality_resolution,[],[f233])).
% 1.30/0.54  fof(f233,plain,(
% 1.30/0.54    ( ! [X0] : (k1_xboole_0 != X0) ) | ~spl4_12),
% 1.30/0.54    inference(superposition,[],[f46,f187])).
% 1.30/0.54  fof(f187,plain,(
% 1.30/0.54    ( ! [X2] : (k5_xboole_0(k1_tarski(sK1),k5_xboole_0(X2,k3_xboole_0(X2,k1_tarski(sK1)))) = X2) ) | ~spl4_12),
% 1.30/0.54    inference(resolution,[],[f171,f47])).
% 1.30/0.54  fof(f47,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1) )),
% 1.30/0.54    inference(definition_unfolding,[],[f37,f45])).
% 1.30/0.54  fof(f45,plain,(
% 1.30/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.30/0.54    inference(definition_unfolding,[],[f36,f35])).
% 1.30/0.54  fof(f35,plain,(
% 1.30/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.30/0.54    inference(cnf_transformation,[],[f3])).
% 1.30/0.54  fof(f3,axiom,(
% 1.30/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.30/0.54  fof(f36,plain,(
% 1.30/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.30/0.54    inference(cnf_transformation,[],[f5])).
% 1.30/0.54  fof(f5,axiom,(
% 1.30/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.30/0.54  fof(f37,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.30/0.54    inference(cnf_transformation,[],[f19])).
% 1.30/0.54  fof(f19,plain,(
% 1.30/0.54    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.30/0.54    inference(ennf_transformation,[],[f4])).
% 1.30/0.54  fof(f4,axiom,(
% 1.30/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.30/0.54  fof(f171,plain,(
% 1.30/0.54    ( ! [X0] : (r1_tarski(k1_tarski(sK1),X0)) ) | ~spl4_12),
% 1.30/0.54    inference(resolution,[],[f127,f70])).
% 1.30/0.54  fof(f70,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~v1_xboole_0(X0) | r1_tarski(X0,X1)) )),
% 1.30/0.54    inference(resolution,[],[f41,f33])).
% 1.30/0.54  fof(f33,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f1])).
% 1.30/0.54  fof(f1,axiom,(
% 1.30/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.30/0.54  fof(f41,plain,(
% 1.30/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f24])).
% 1.30/0.54  fof(f24,plain,(
% 1.30/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.30/0.54    inference(ennf_transformation,[],[f2])).
% 1.30/0.54  fof(f2,axiom,(
% 1.30/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.30/0.54  fof(f127,plain,(
% 1.30/0.54    v1_xboole_0(k1_tarski(sK1)) | ~spl4_12),
% 1.30/0.54    inference(avatar_component_clause,[],[f125])).
% 1.30/0.54  fof(f125,plain,(
% 1.30/0.54    spl4_12 <=> v1_xboole_0(k1_tarski(sK1))),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.30/0.54  fof(f46,plain,(
% 1.30/0.54    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k3_xboole_0(X1,k1_tarski(X0))))) )),
% 1.30/0.54    inference(definition_unfolding,[],[f34,f45])).
% 1.30/0.54  fof(f34,plain,(
% 1.30/0.54    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 1.30/0.54    inference(cnf_transformation,[],[f6])).
% 1.30/0.54  fof(f6,axiom,(
% 1.30/0.54    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.30/0.54  fof(f158,plain,(
% 1.30/0.54    spl4_18 | spl4_12 | ~spl4_2 | spl4_1 | ~spl4_8),
% 1.30/0.54    inference(avatar_split_clause,[],[f136,f103,f49,f54,f125,f155])).
% 1.30/0.54  fof(f54,plain,(
% 1.30/0.54    spl4_2 <=> v1_zfmisc_1(sK0)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.30/0.54  fof(f49,plain,(
% 1.30/0.54    spl4_1 <=> v1_xboole_0(sK0)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.30/0.54  fof(f103,plain,(
% 1.30/0.54    spl4_8 <=> r1_tarski(k1_tarski(sK1),sK0)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.30/0.54  fof(f136,plain,(
% 1.30/0.54    v1_xboole_0(sK0) | ~v1_zfmisc_1(sK0) | v1_xboole_0(k1_tarski(sK1)) | sK0 = k1_tarski(sK1) | ~spl4_8),
% 1.30/0.54    inference(resolution,[],[f31,f105])).
% 1.30/0.54  fof(f105,plain,(
% 1.30/0.54    r1_tarski(k1_tarski(sK1),sK0) | ~spl4_8),
% 1.30/0.54    inference(avatar_component_clause,[],[f103])).
% 1.30/0.54  fof(f31,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | v1_xboole_0(X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X0) | X0 = X1) )),
% 1.30/0.54    inference(cnf_transformation,[],[f18])).
% 1.30/0.54  fof(f18,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.30/0.54    inference(flattening,[],[f17])).
% 1.30/0.54  fof(f17,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.30/0.54    inference(ennf_transformation,[],[f12])).
% 1.30/0.54  fof(f12,axiom,(
% 1.30/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 1.30/0.54  fof(f106,plain,(
% 1.30/0.54    spl4_8 | ~spl4_7),
% 1.30/0.54    inference(avatar_split_clause,[],[f99,f95,f103])).
% 1.30/0.54  fof(f95,plain,(
% 1.30/0.54    spl4_7 <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.30/0.54  fof(f99,plain,(
% 1.30/0.54    r1_tarski(k1_tarski(sK1),sK0) | ~spl4_7),
% 1.30/0.54    inference(resolution,[],[f97,f44])).
% 1.30/0.54  fof(f44,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f9])).
% 1.30/0.54  fof(f9,axiom,(
% 1.30/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.30/0.54  fof(f97,plain,(
% 1.30/0.54    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) | ~spl4_7),
% 1.30/0.54    inference(avatar_component_clause,[],[f95])).
% 1.30/0.54  fof(f98,plain,(
% 1.30/0.54    spl4_1 | spl4_7 | ~spl4_4 | ~spl4_5),
% 1.30/0.54    inference(avatar_split_clause,[],[f93,f81,f64,f95,f49])).
% 1.30/0.54  fof(f64,plain,(
% 1.30/0.54    spl4_4 <=> m1_subset_1(sK1,sK0)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.30/0.54  fof(f81,plain,(
% 1.30/0.54    spl4_5 <=> k6_domain_1(sK0,sK1) = k1_tarski(sK1)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.30/0.54  fof(f93,plain,(
% 1.30/0.54    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) | v1_xboole_0(sK0) | (~spl4_4 | ~spl4_5)),
% 1.30/0.54    inference(forward_demodulation,[],[f91,f83])).
% 1.30/0.54  fof(f83,plain,(
% 1.30/0.54    k6_domain_1(sK0,sK1) = k1_tarski(sK1) | ~spl4_5),
% 1.30/0.54    inference(avatar_component_clause,[],[f81])).
% 1.30/0.54  fof(f91,plain,(
% 1.30/0.54    v1_xboole_0(sK0) | m1_subset_1(k6_domain_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl4_4),
% 1.30/0.54    inference(resolution,[],[f39,f66])).
% 1.30/0.54  fof(f66,plain,(
% 1.30/0.54    m1_subset_1(sK1,sK0) | ~spl4_4),
% 1.30/0.54    inference(avatar_component_clause,[],[f64])).
% 1.30/0.54  fof(f39,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.30/0.54    inference(cnf_transformation,[],[f23])).
% 1.30/0.54  % (4209)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.30/0.54  fof(f23,plain,(
% 1.30/0.54    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.30/0.54    inference(flattening,[],[f22])).
% 1.30/0.54  fof(f22,plain,(
% 1.30/0.54    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.30/0.54    inference(ennf_transformation,[],[f10])).
% 1.30/0.54  fof(f10,axiom,(
% 1.30/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 1.30/0.54  fof(f90,plain,(
% 1.30/0.54    spl4_6 | ~spl4_3 | ~spl4_5),
% 1.30/0.54    inference(avatar_split_clause,[],[f85,f81,f59,f87])).
% 1.30/0.54  fof(f59,plain,(
% 1.30/0.54    spl4_3 <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 1.30/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.30/0.54  fof(f85,plain,(
% 1.30/0.54    v1_subset_1(k1_tarski(sK1),sK0) | (~spl4_3 | ~spl4_5)),
% 1.30/0.54    inference(backward_demodulation,[],[f61,f83])).
% 1.30/0.54  % (4214)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.30/0.54  fof(f61,plain,(
% 1.30/0.54    v1_subset_1(k6_domain_1(sK0,sK1),sK0) | ~spl4_3),
% 1.30/0.54    inference(avatar_component_clause,[],[f59])).
% 1.30/0.54  fof(f84,plain,(
% 1.30/0.54    spl4_5 | spl4_1 | ~spl4_4),
% 1.30/0.54    inference(avatar_split_clause,[],[f78,f64,f49,f81])).
% 1.30/0.54  fof(f78,plain,(
% 1.30/0.54    v1_xboole_0(sK0) | k6_domain_1(sK0,sK1) = k1_tarski(sK1) | ~spl4_4),
% 1.30/0.54    inference(resolution,[],[f38,f66])).
% 1.30/0.54  fof(f38,plain,(
% 1.30/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f21])).
% 1.30/0.54  fof(f21,plain,(
% 1.30/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.30/0.54    inference(flattening,[],[f20])).
% 1.30/0.54  fof(f20,plain,(
% 1.30/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.30/0.54    inference(ennf_transformation,[],[f11])).
% 1.30/0.54  fof(f11,axiom,(
% 1.30/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.30/0.54  fof(f67,plain,(
% 1.30/0.54    spl4_4),
% 1.30/0.54    inference(avatar_split_clause,[],[f25,f64])).
% 1.30/0.54  fof(f25,plain,(
% 1.30/0.54    m1_subset_1(sK1,sK0)),
% 1.30/0.54    inference(cnf_transformation,[],[f16])).
% 1.30/0.54  fof(f16,plain,(
% 1.30/0.54    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 1.30/0.54    inference(flattening,[],[f15])).
% 1.30/0.54  fof(f15,plain,(
% 1.30/0.54    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 1.30/0.54    inference(ennf_transformation,[],[f14])).
% 1.30/0.54  fof(f14,negated_conjecture,(
% 1.30/0.54    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 1.30/0.54    inference(negated_conjecture,[],[f13])).
% 1.30/0.54  fof(f13,conjecture,(
% 1.30/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 1.30/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).
% 1.30/0.54  fof(f62,plain,(
% 1.30/0.54    spl4_3),
% 1.30/0.54    inference(avatar_split_clause,[],[f26,f59])).
% 1.30/0.54  fof(f26,plain,(
% 1.30/0.54    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 1.30/0.54    inference(cnf_transformation,[],[f16])).
% 1.30/0.54  fof(f57,plain,(
% 1.30/0.54    spl4_2),
% 1.30/0.54    inference(avatar_split_clause,[],[f27,f54])).
% 1.30/0.54  fof(f27,plain,(
% 1.30/0.54    v1_zfmisc_1(sK0)),
% 1.30/0.54    inference(cnf_transformation,[],[f16])).
% 1.30/0.54  fof(f52,plain,(
% 1.30/0.54    ~spl4_1),
% 1.30/0.54    inference(avatar_split_clause,[],[f28,f49])).
% 1.30/0.54  fof(f28,plain,(
% 1.30/0.54    ~v1_xboole_0(sK0)),
% 1.30/0.54    inference(cnf_transformation,[],[f16])).
% 1.30/0.54  % SZS output end Proof for theBenchmark
% 1.30/0.54  % (4223)------------------------------
% 1.30/0.54  % (4223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (4223)Termination reason: Refutation
% 1.30/0.54  
% 1.30/0.54  % (4223)Memory used [KB]: 10874
% 1.30/0.54  % (4223)Time elapsed: 0.121 s
% 1.30/0.54  % (4223)------------------------------
% 1.30/0.54  % (4223)------------------------------
% 1.30/0.55  % (4209)Refutation not found, incomplete strategy% (4209)------------------------------
% 1.30/0.55  % (4209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (4209)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (4209)Memory used [KB]: 10746
% 1.30/0.55  % (4209)Time elapsed: 0.128 s
% 1.30/0.55  % (4209)------------------------------
% 1.30/0.55  % (4209)------------------------------
% 1.30/0.55  % (4217)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.30/0.55  % (4235)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.30/0.55  % (4206)Success in time 0.178 s
%------------------------------------------------------------------------------
