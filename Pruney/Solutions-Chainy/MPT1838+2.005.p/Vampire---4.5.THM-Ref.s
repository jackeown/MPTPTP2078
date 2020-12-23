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
% DateTime   : Thu Dec  3 13:19:54 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 151 expanded)
%              Number of leaves         :   17 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :  217 ( 435 expanded)
%              Number of equality atoms :   36 (  85 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f333,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f77,f82,f94,f99,f117,f139,f173,f201,f332])).

fof(f332,plain,
    ( ~ spl9_4
    | spl9_5
    | ~ spl9_8
    | ~ spl9_13
    | ~ spl9_14 ),
    inference(avatar_contradiction_clause,[],[f331])).

fof(f331,plain,
    ( $false
    | ~ spl9_4
    | spl9_5
    | ~ spl9_8
    | ~ spl9_13
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f318,f322])).

fof(f322,plain,
    ( ! [X4] : r2_hidden(sK3(k1_xboole_0),X4)
    | ~ spl9_4
    | spl9_5
    | ~ spl9_8
    | ~ spl9_13 ),
    inference(subsumption_resolution,[],[f321,f27])).

fof(f27,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f321,plain,
    ( ! [X4] :
        ( ~ r1_tarski(k1_xboole_0,X4)
        | r2_hidden(sK3(k1_xboole_0),X4) )
    | ~ spl9_4
    | spl9_5
    | ~ spl9_8
    | ~ spl9_13 ),
    inference(forward_demodulation,[],[f283,f272])).

fof(f272,plain,
    ( k1_xboole_0 = sK0
    | ~ spl9_4
    | spl9_5
    | ~ spl9_13 ),
    inference(subsumption_resolution,[],[f268,f98])).

fof(f98,plain,
    ( sK0 != sK1
    | spl9_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl9_5
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f268,plain,
    ( sK0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl9_4
    | ~ spl9_13 ),
    inference(resolution,[],[f174,f93])).

fof(f93,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl9_4
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f174,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | sK1 = X0
        | k1_xboole_0 = X0 )
    | ~ spl9_13 ),
    inference(superposition,[],[f43,f172])).

fof(f172,plain,
    ( sK1 = k1_tarski(sK2(sK1))
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl9_13
  <=> sK1 = k1_tarski(sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f283,plain,
    ( ! [X4] :
        ( r2_hidden(sK3(k1_xboole_0),X4)
        | ~ r1_tarski(sK0,X4) )
    | ~ spl9_4
    | spl9_5
    | ~ spl9_8
    | ~ spl9_13 ),
    inference(backward_demodulation,[],[f128,f272])).

fof(f128,plain,
    ( ! [X4] :
        ( ~ r1_tarski(sK0,X4)
        | r2_hidden(sK3(sK0),X4) )
    | ~ spl9_8 ),
    inference(resolution,[],[f116,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f116,plain,
    ( r2_hidden(sK3(sK0),sK0)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl9_8
  <=> r2_hidden(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f318,plain,
    ( ! [X0] : ~ r2_hidden(sK3(k1_xboole_0),k4_xboole_0(X0,sK1))
    | ~ spl9_4
    | spl9_5
    | ~ spl9_13
    | ~ spl9_14 ),
    inference(backward_demodulation,[],[f266,f272])).

fof(f266,plain,
    ( ! [X0] : ~ r2_hidden(sK3(sK0),k4_xboole_0(X0,sK1))
    | ~ spl9_14 ),
    inference(resolution,[],[f209,f64])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( sP6(X3,X1,X0)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f209,plain,
    ( ! [X3] : ~ sP6(sK3(sK0),sK1,X3)
    | ~ spl9_14 ),
    inference(resolution,[],[f200,f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ sP6(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f200,plain,
    ( r2_hidden(sK3(sK0),sK1)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl9_14
  <=> r2_hidden(sK3(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f201,plain,
    ( spl9_14
    | ~ spl9_4
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f194,f114,f91,f198])).

fof(f194,plain,
    ( r2_hidden(sK3(sK0),sK1)
    | ~ spl9_4
    | ~ spl9_8 ),
    inference(resolution,[],[f128,f93])).

fof(f173,plain,
    ( spl9_13
    | spl9_1
    | ~ spl9_2
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f160,f136,f74,f69,f170])).

fof(f69,plain,
    ( spl9_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f74,plain,
    ( spl9_2
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f136,plain,
    ( spl9_10
  <=> sK1 = k6_domain_1(sK1,sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f160,plain,
    ( sK1 = k1_tarski(sK2(sK1))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_10 ),
    inference(forward_demodulation,[],[f159,f138])).

fof(f138,plain,
    ( sK1 = k6_domain_1(sK1,sK2(sK1))
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f136])).

fof(f159,plain,
    ( k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f158,f76])).

fof(f76,plain,
    ( v1_zfmisc_1(sK1)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f158,plain,
    ( k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))
    | ~ v1_zfmisc_1(sK1)
    | spl9_1 ),
    inference(subsumption_resolution,[],[f157,f71])).

fof(f71,plain,
    ( ~ v1_xboole_0(sK1)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f157,plain,
    ( k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))
    | v1_xboole_0(sK1)
    | ~ v1_zfmisc_1(sK1)
    | spl9_1 ),
    inference(resolution,[],[f83,f29])).

fof(f29,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),X0)
      | v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

fof(f83,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k1_tarski(X0) = k6_domain_1(sK1,X0) )
    | spl9_1 ),
    inference(resolution,[],[f71,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f139,plain,
    ( spl9_10
    | spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f86,f74,f69,f136])).

fof(f86,plain,
    ( sK1 = k6_domain_1(sK1,sK2(sK1))
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f85,f76])).

fof(f85,plain,
    ( sK1 = k6_domain_1(sK1,sK2(sK1))
    | ~ v1_zfmisc_1(sK1)
    | spl9_1 ),
    inference(resolution,[],[f71,f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | k6_domain_1(X0,sK2(X0)) = X0
      | ~ v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f117,plain,
    ( spl9_8
    | spl9_3 ),
    inference(avatar_split_clause,[],[f88,f79,f114])).

fof(f79,plain,
    ( spl9_3
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f88,plain,
    ( r2_hidden(sK3(sK0),sK0)
    | spl9_3 ),
    inference(resolution,[],[f81,f32])).

fof(f32,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f81,plain,
    ( ~ v1_xboole_0(sK0)
    | spl9_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f99,plain,(
    ~ spl9_5 ),
    inference(avatar_split_clause,[],[f25,f96])).

fof(f25,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r1_tarski(X0,X1)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ( v1_zfmisc_1(X1)
              & ~ v1_xboole_0(X1) )
           => ( r1_tarski(X0,X1)
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f94,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f24,f91])).

fof(f24,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f82,plain,(
    ~ spl9_3 ),
    inference(avatar_split_clause,[],[f26,f79])).

fof(f26,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f77,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f23,f74])).

fof(f23,plain,(
    v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f72,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f22,f69])).

fof(f22,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:38:55 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (9935)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (9927)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (9919)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (9915)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (9918)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (9913)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (9939)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (9940)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (9941)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (9937)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (9938)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (9912)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (9916)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (9917)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (9932)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (9933)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (9922)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (9931)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.43/0.55  % (9930)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.43/0.55  % (9913)Refutation not found, incomplete strategy% (9913)------------------------------
% 1.43/0.55  % (9913)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (9913)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (9913)Memory used [KB]: 10746
% 1.43/0.55  % (9913)Time elapsed: 0.135 s
% 1.43/0.55  % (9913)------------------------------
% 1.43/0.55  % (9913)------------------------------
% 1.43/0.55  % (9921)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.43/0.56  % (9936)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.43/0.56  % (9925)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.43/0.56  % (9924)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.43/0.56  % (9923)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.43/0.56  % (9929)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.43/0.56  % (9934)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.43/0.56  % (9926)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.43/0.56  % (9923)Refutation not found, incomplete strategy% (9923)------------------------------
% 1.43/0.56  % (9923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (9929)Refutation not found, incomplete strategy% (9929)------------------------------
% 1.43/0.56  % (9929)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.57  % (9923)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.57  
% 1.43/0.57  % (9923)Memory used [KB]: 10618
% 1.43/0.57  % (9923)Time elapsed: 0.153 s
% 1.43/0.57  % (9923)------------------------------
% 1.43/0.57  % (9923)------------------------------
% 1.56/0.57  % (9932)Refutation found. Thanks to Tanya!
% 1.56/0.57  % SZS status Theorem for theBenchmark
% 1.56/0.57  % (9934)Refutation not found, incomplete strategy% (9934)------------------------------
% 1.56/0.57  % (9934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (9922)Refutation not found, incomplete strategy% (9922)------------------------------
% 1.56/0.57  % (9922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (9922)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.57  
% 1.56/0.57  % (9922)Memory used [KB]: 10618
% 1.56/0.57  % (9922)Time elapsed: 0.159 s
% 1.56/0.57  % (9922)------------------------------
% 1.56/0.57  % (9922)------------------------------
% 1.56/0.57  % (9920)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.56/0.57  % (9934)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.57  
% 1.56/0.57  % (9929)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.57  % (9934)Memory used [KB]: 10746
% 1.56/0.57  % (9934)Time elapsed: 0.159 s
% 1.56/0.57  
% 1.56/0.57  % (9934)------------------------------
% 1.56/0.57  % (9934)------------------------------
% 1.56/0.57  % (9929)Memory used [KB]: 10746
% 1.56/0.57  % (9929)Time elapsed: 0.152 s
% 1.56/0.57  % (9929)------------------------------
% 1.56/0.57  % (9929)------------------------------
% 1.56/0.58  % (9911)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.56/0.59  % SZS output start Proof for theBenchmark
% 1.56/0.59  fof(f333,plain,(
% 1.56/0.59    $false),
% 1.56/0.59    inference(avatar_sat_refutation,[],[f72,f77,f82,f94,f99,f117,f139,f173,f201,f332])).
% 1.56/0.59  fof(f332,plain,(
% 1.56/0.59    ~spl9_4 | spl9_5 | ~spl9_8 | ~spl9_13 | ~spl9_14),
% 1.56/0.59    inference(avatar_contradiction_clause,[],[f331])).
% 1.56/0.59  fof(f331,plain,(
% 1.56/0.59    $false | (~spl9_4 | spl9_5 | ~spl9_8 | ~spl9_13 | ~spl9_14)),
% 1.56/0.59    inference(subsumption_resolution,[],[f318,f322])).
% 1.56/0.59  fof(f322,plain,(
% 1.56/0.59    ( ! [X4] : (r2_hidden(sK3(k1_xboole_0),X4)) ) | (~spl9_4 | spl9_5 | ~spl9_8 | ~spl9_13)),
% 1.56/0.59    inference(subsumption_resolution,[],[f321,f27])).
% 1.56/0.59  fof(f27,plain,(
% 1.56/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.56/0.59    inference(cnf_transformation,[],[f8])).
% 1.56/0.59  fof(f8,axiom,(
% 1.56/0.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.56/0.59  fof(f321,plain,(
% 1.56/0.59    ( ! [X4] : (~r1_tarski(k1_xboole_0,X4) | r2_hidden(sK3(k1_xboole_0),X4)) ) | (~spl9_4 | spl9_5 | ~spl9_8 | ~spl9_13)),
% 1.56/0.59    inference(forward_demodulation,[],[f283,f272])).
% 1.56/0.59  fof(f272,plain,(
% 1.56/0.59    k1_xboole_0 = sK0 | (~spl9_4 | spl9_5 | ~spl9_13)),
% 1.56/0.59    inference(subsumption_resolution,[],[f268,f98])).
% 1.56/0.59  fof(f98,plain,(
% 1.56/0.59    sK0 != sK1 | spl9_5),
% 1.56/0.59    inference(avatar_component_clause,[],[f96])).
% 1.56/0.59  fof(f96,plain,(
% 1.56/0.59    spl9_5 <=> sK0 = sK1),
% 1.56/0.59    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 1.56/0.59  fof(f268,plain,(
% 1.56/0.59    sK0 = sK1 | k1_xboole_0 = sK0 | (~spl9_4 | ~spl9_13)),
% 1.56/0.59    inference(resolution,[],[f174,f93])).
% 1.56/0.59  fof(f93,plain,(
% 1.56/0.59    r1_tarski(sK0,sK1) | ~spl9_4),
% 1.56/0.59    inference(avatar_component_clause,[],[f91])).
% 1.56/0.59  fof(f91,plain,(
% 1.56/0.59    spl9_4 <=> r1_tarski(sK0,sK1)),
% 1.56/0.59    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 1.56/0.59  fof(f174,plain,(
% 1.56/0.59    ( ! [X0] : (~r1_tarski(X0,sK1) | sK1 = X0 | k1_xboole_0 = X0) ) | ~spl9_13),
% 1.56/0.59    inference(superposition,[],[f43,f172])).
% 1.56/0.59  fof(f172,plain,(
% 1.56/0.59    sK1 = k1_tarski(sK2(sK1)) | ~spl9_13),
% 1.56/0.59    inference(avatar_component_clause,[],[f170])).
% 1.56/0.59  fof(f170,plain,(
% 1.56/0.59    spl9_13 <=> sK1 = k1_tarski(sK2(sK1))),
% 1.56/0.59    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 1.56/0.59  fof(f43,plain,(
% 1.56/0.59    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) = X0 | k1_xboole_0 = X0) )),
% 1.56/0.59    inference(cnf_transformation,[],[f10])).
% 1.56/0.59  fof(f10,axiom,(
% 1.56/0.59    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.56/0.59  fof(f283,plain,(
% 1.56/0.59    ( ! [X4] : (r2_hidden(sK3(k1_xboole_0),X4) | ~r1_tarski(sK0,X4)) ) | (~spl9_4 | spl9_5 | ~spl9_8 | ~spl9_13)),
% 1.56/0.59    inference(backward_demodulation,[],[f128,f272])).
% 1.56/0.59  fof(f128,plain,(
% 1.56/0.59    ( ! [X4] : (~r1_tarski(sK0,X4) | r2_hidden(sK3(sK0),X4)) ) | ~spl9_8),
% 1.56/0.59    inference(resolution,[],[f116,f40])).
% 1.56/0.59  fof(f40,plain,(
% 1.56/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.56/0.59    inference(cnf_transformation,[],[f21])).
% 1.56/0.59  fof(f21,plain,(
% 1.56/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.56/0.59    inference(ennf_transformation,[],[f3])).
% 1.56/0.59  fof(f3,axiom,(
% 1.56/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.56/0.59  fof(f116,plain,(
% 1.56/0.59    r2_hidden(sK3(sK0),sK0) | ~spl9_8),
% 1.56/0.59    inference(avatar_component_clause,[],[f114])).
% 1.56/0.59  fof(f114,plain,(
% 1.56/0.59    spl9_8 <=> r2_hidden(sK3(sK0),sK0)),
% 1.56/0.59    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 1.56/0.59  fof(f318,plain,(
% 1.56/0.59    ( ! [X0] : (~r2_hidden(sK3(k1_xboole_0),k4_xboole_0(X0,sK1))) ) | (~spl9_4 | spl9_5 | ~spl9_13 | ~spl9_14)),
% 1.56/0.59    inference(backward_demodulation,[],[f266,f272])).
% 1.56/0.59  fof(f266,plain,(
% 1.56/0.59    ( ! [X0] : (~r2_hidden(sK3(sK0),k4_xboole_0(X0,sK1))) ) | ~spl9_14),
% 1.56/0.59    inference(resolution,[],[f209,f64])).
% 1.56/0.59  fof(f64,plain,(
% 1.56/0.59    ( ! [X0,X3,X1] : (sP6(X3,X1,X0) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 1.56/0.59    inference(equality_resolution,[],[f50])).
% 1.56/0.59  fof(f50,plain,(
% 1.56/0.59    ( ! [X2,X0,X3,X1] : (sP6(X3,X1,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.56/0.59    inference(cnf_transformation,[],[f5])).
% 1.56/0.59  fof(f5,axiom,(
% 1.56/0.59    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.56/0.59  fof(f209,plain,(
% 1.56/0.59    ( ! [X3] : (~sP6(sK3(sK0),sK1,X3)) ) | ~spl9_14),
% 1.56/0.59    inference(resolution,[],[f200,f48])).
% 1.56/0.59  fof(f48,plain,(
% 1.56/0.59    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~sP6(X3,X1,X0)) )),
% 1.56/0.59    inference(cnf_transformation,[],[f5])).
% 1.56/0.59  fof(f200,plain,(
% 1.56/0.59    r2_hidden(sK3(sK0),sK1) | ~spl9_14),
% 1.56/0.59    inference(avatar_component_clause,[],[f198])).
% 1.56/0.59  fof(f198,plain,(
% 1.56/0.59    spl9_14 <=> r2_hidden(sK3(sK0),sK1)),
% 1.56/0.59    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 1.56/0.59  fof(f201,plain,(
% 1.56/0.59    spl9_14 | ~spl9_4 | ~spl9_8),
% 1.56/0.59    inference(avatar_split_clause,[],[f194,f114,f91,f198])).
% 1.56/0.59  fof(f194,plain,(
% 1.56/0.59    r2_hidden(sK3(sK0),sK1) | (~spl9_4 | ~spl9_8)),
% 1.56/0.59    inference(resolution,[],[f128,f93])).
% 1.56/0.59  fof(f173,plain,(
% 1.56/0.59    spl9_13 | spl9_1 | ~spl9_2 | ~spl9_10),
% 1.56/0.59    inference(avatar_split_clause,[],[f160,f136,f74,f69,f170])).
% 1.56/0.59  fof(f69,plain,(
% 1.56/0.59    spl9_1 <=> v1_xboole_0(sK1)),
% 1.56/0.59    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.56/0.59  fof(f74,plain,(
% 1.56/0.59    spl9_2 <=> v1_zfmisc_1(sK1)),
% 1.56/0.59    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.56/0.59  fof(f136,plain,(
% 1.56/0.59    spl9_10 <=> sK1 = k6_domain_1(sK1,sK2(sK1))),
% 1.56/0.59    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 1.56/0.59  fof(f160,plain,(
% 1.56/0.59    sK1 = k1_tarski(sK2(sK1)) | (spl9_1 | ~spl9_2 | ~spl9_10)),
% 1.56/0.59    inference(forward_demodulation,[],[f159,f138])).
% 1.56/0.59  fof(f138,plain,(
% 1.56/0.59    sK1 = k6_domain_1(sK1,sK2(sK1)) | ~spl9_10),
% 1.56/0.59    inference(avatar_component_clause,[],[f136])).
% 1.56/0.59  fof(f159,plain,(
% 1.56/0.59    k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1)) | (spl9_1 | ~spl9_2)),
% 1.56/0.59    inference(subsumption_resolution,[],[f158,f76])).
% 1.56/0.59  fof(f76,plain,(
% 1.56/0.59    v1_zfmisc_1(sK1) | ~spl9_2),
% 1.56/0.59    inference(avatar_component_clause,[],[f74])).
% 1.56/0.59  fof(f158,plain,(
% 1.56/0.59    k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1)) | ~v1_zfmisc_1(sK1) | spl9_1),
% 1.56/0.59    inference(subsumption_resolution,[],[f157,f71])).
% 1.56/0.59  fof(f71,plain,(
% 1.56/0.59    ~v1_xboole_0(sK1) | spl9_1),
% 1.56/0.59    inference(avatar_component_clause,[],[f69])).
% 1.56/0.59  fof(f157,plain,(
% 1.56/0.59    k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1)) | v1_xboole_0(sK1) | ~v1_zfmisc_1(sK1) | spl9_1),
% 1.56/0.59    inference(resolution,[],[f83,f29])).
% 1.56/0.59  fof(f29,plain,(
% 1.56/0.59    ( ! [X0] : (m1_subset_1(sK2(X0),X0) | v1_xboole_0(X0) | ~v1_zfmisc_1(X0)) )),
% 1.56/0.59    inference(cnf_transformation,[],[f17])).
% 1.56/0.59  fof(f17,plain,(
% 1.56/0.59    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 1.56/0.59    inference(ennf_transformation,[],[f12])).
% 1.56/0.59  fof(f12,axiom,(
% 1.56/0.59    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 1.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).
% 1.56/0.59  fof(f83,plain,(
% 1.56/0.59    ( ! [X0] : (~m1_subset_1(X0,sK1) | k1_tarski(X0) = k6_domain_1(sK1,X0)) ) | spl9_1),
% 1.56/0.59    inference(resolution,[],[f71,f36])).
% 1.56/0.59  fof(f36,plain,(
% 1.56/0.59    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k1_tarski(X1) = k6_domain_1(X0,X1)) )),
% 1.56/0.59    inference(cnf_transformation,[],[f20])).
% 1.56/0.59  fof(f20,plain,(
% 1.56/0.59    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.56/0.59    inference(flattening,[],[f19])).
% 1.56/0.59  fof(f19,plain,(
% 1.56/0.59    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.56/0.59    inference(ennf_transformation,[],[f11])).
% 1.56/0.59  fof(f11,axiom,(
% 1.56/0.59    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 1.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.56/0.59  fof(f139,plain,(
% 1.56/0.59    spl9_10 | spl9_1 | ~spl9_2),
% 1.56/0.59    inference(avatar_split_clause,[],[f86,f74,f69,f136])).
% 1.56/0.59  fof(f86,plain,(
% 1.56/0.59    sK1 = k6_domain_1(sK1,sK2(sK1)) | (spl9_1 | ~spl9_2)),
% 1.56/0.59    inference(subsumption_resolution,[],[f85,f76])).
% 1.56/0.59  fof(f85,plain,(
% 1.56/0.59    sK1 = k6_domain_1(sK1,sK2(sK1)) | ~v1_zfmisc_1(sK1) | spl9_1),
% 1.56/0.59    inference(resolution,[],[f71,f30])).
% 1.56/0.59  fof(f30,plain,(
% 1.56/0.59    ( ! [X0] : (v1_xboole_0(X0) | k6_domain_1(X0,sK2(X0)) = X0 | ~v1_zfmisc_1(X0)) )),
% 1.56/0.59    inference(cnf_transformation,[],[f17])).
% 1.56/0.59  fof(f117,plain,(
% 1.56/0.59    spl9_8 | spl9_3),
% 1.56/0.59    inference(avatar_split_clause,[],[f88,f79,f114])).
% 1.56/0.59  fof(f79,plain,(
% 1.56/0.59    spl9_3 <=> v1_xboole_0(sK0)),
% 1.56/0.59    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 1.56/0.59  fof(f88,plain,(
% 1.56/0.59    r2_hidden(sK3(sK0),sK0) | spl9_3),
% 1.56/0.59    inference(resolution,[],[f81,f32])).
% 1.56/0.59  fof(f32,plain,(
% 1.56/0.59    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) )),
% 1.56/0.59    inference(cnf_transformation,[],[f2])).
% 1.56/0.59  fof(f2,axiom,(
% 1.56/0.59    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.56/0.59  fof(f81,plain,(
% 1.56/0.59    ~v1_xboole_0(sK0) | spl9_3),
% 1.56/0.59    inference(avatar_component_clause,[],[f79])).
% 1.56/0.59  fof(f99,plain,(
% 1.56/0.59    ~spl9_5),
% 1.56/0.59    inference(avatar_split_clause,[],[f25,f96])).
% 1.56/0.59  fof(f25,plain,(
% 1.56/0.59    sK0 != sK1),
% 1.56/0.59    inference(cnf_transformation,[],[f16])).
% 1.56/0.59  fof(f16,plain,(
% 1.56/0.59    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.56/0.59    inference(flattening,[],[f15])).
% 1.56/0.59  fof(f15,plain,(
% 1.56/0.59    ? [X0] : (? [X1] : ((X0 != X1 & r1_tarski(X0,X1)) & (v1_zfmisc_1(X1) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 1.56/0.59    inference(ennf_transformation,[],[f14])).
% 1.56/0.59  fof(f14,negated_conjecture,(
% 1.56/0.59    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.56/0.59    inference(negated_conjecture,[],[f13])).
% 1.56/0.59  fof(f13,conjecture,(
% 1.56/0.59    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.56/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 1.56/0.59  fof(f94,plain,(
% 1.56/0.59    spl9_4),
% 1.56/0.59    inference(avatar_split_clause,[],[f24,f91])).
% 1.56/0.59  fof(f24,plain,(
% 1.56/0.59    r1_tarski(sK0,sK1)),
% 1.56/0.59    inference(cnf_transformation,[],[f16])).
% 1.56/0.59  fof(f82,plain,(
% 1.56/0.59    ~spl9_3),
% 1.56/0.59    inference(avatar_split_clause,[],[f26,f79])).
% 1.56/0.59  fof(f26,plain,(
% 1.56/0.59    ~v1_xboole_0(sK0)),
% 1.56/0.59    inference(cnf_transformation,[],[f16])).
% 1.56/0.59  fof(f77,plain,(
% 1.56/0.59    spl9_2),
% 1.56/0.59    inference(avatar_split_clause,[],[f23,f74])).
% 1.56/0.59  fof(f23,plain,(
% 1.56/0.59    v1_zfmisc_1(sK1)),
% 1.56/0.59    inference(cnf_transformation,[],[f16])).
% 1.56/0.59  fof(f72,plain,(
% 1.56/0.59    ~spl9_1),
% 1.56/0.59    inference(avatar_split_clause,[],[f22,f69])).
% 1.56/0.59  fof(f22,plain,(
% 1.56/0.59    ~v1_xboole_0(sK1)),
% 1.56/0.59    inference(cnf_transformation,[],[f16])).
% 1.56/0.59  % SZS output end Proof for theBenchmark
% 1.56/0.59  % (9932)------------------------------
% 1.56/0.59  % (9932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.59  % (9932)Termination reason: Refutation
% 1.56/0.59  
% 1.56/0.59  % (9932)Memory used [KB]: 11001
% 1.56/0.59  % (9932)Time elapsed: 0.154 s
% 1.56/0.59  % (9932)------------------------------
% 1.56/0.59  % (9932)------------------------------
% 1.56/0.59  % (9910)Success in time 0.217 s
%------------------------------------------------------------------------------
