%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 145 expanded)
%              Number of leaves         :   21 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  219 ( 381 expanded)
%              Number of equality atoms :   65 ( 102 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f185,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f53,f58,f70,f75,f86,f97,f109,f114,f138,f163,f181,f184])).

fof(f184,plain,
    ( ~ spl5_14
    | ~ spl5_17 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | ~ spl5_14
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f137,f162])).

fof(f162,plain,
    ( ! [X0] : k1_tarski(X0) != sK1
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl5_17
  <=> ! [X0] : k1_tarski(X0) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f137,plain,
    ( sK1 = k1_tarski(sK2(sK1))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl5_14
  <=> sK1 = k1_tarski(sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f181,plain,
    ( ~ spl5_11
    | ~ spl5_16 ),
    inference(avatar_contradiction_clause,[],[f180])).

fof(f180,plain,
    ( $false
    | ~ spl5_11
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f174,f33])).

fof(f33,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f174,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_tarski(sK3(k1_xboole_0)),k1_xboole_0)
    | ~ spl5_11
    | ~ spl5_16 ),
    inference(backward_demodulation,[],[f133,f159])).

fof(f159,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl5_16
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f133,plain,
    ( sK0 = k2_xboole_0(k1_tarski(sK3(sK0)),sK0)
    | ~ spl5_11 ),
    inference(resolution,[],[f113,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f113,plain,
    ( r1_tarski(k1_tarski(sK3(sK0)),sK0)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl5_11
  <=> r1_tarski(k1_tarski(sK3(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f163,plain,
    ( spl5_16
    | spl5_17
    | spl5_5
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f148,f135,f94,f72,f161,f157])).

fof(f72,plain,
    ( spl5_5
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f94,plain,
    ( spl5_8
  <=> sK1 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f148,plain,
    ( ! [X0] :
        ( k1_tarski(X0) != sK1
        | k1_xboole_0 = sK0 )
    | spl5_5
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f99,f147])).

fof(f147,plain,
    ( k1_xboole_0 != sK1
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(superposition,[],[f142,f96])).

fof(f96,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f94])).

fof(f142,plain,
    ( ! [X0] : k1_xboole_0 != k2_xboole_0(X0,sK1)
    | ~ spl5_14 ),
    inference(superposition,[],[f141,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f141,plain,
    ( ! [X3] : k1_xboole_0 != k2_xboole_0(sK1,X3)
    | ~ spl5_14 ),
    inference(superposition,[],[f33,f137])).

fof(f99,plain,
    ( ! [X0] :
        ( k1_tarski(X0) != sK1
        | k1_xboole_0 = sK0
        | k1_xboole_0 = sK1 )
    | spl5_5
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f98,f74])).

fof(f74,plain,
    ( sK0 != sK1
    | spl5_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f98,plain,
    ( ! [X0] :
        ( k1_tarski(X0) != sK1
        | sK0 = sK1
        | k1_xboole_0 = sK0
        | k1_xboole_0 = sK1 )
    | ~ spl5_8 ),
    inference(superposition,[],[f43,f96])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) != k2_xboole_0(X1,X2)
      | X1 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | X1 = X2
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f138,plain,
    ( spl5_14
    | spl5_1
    | ~ spl5_2
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f129,f106,f50,f45,f135])).

fof(f45,plain,
    ( spl5_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f50,plain,
    ( spl5_2
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f106,plain,
    ( spl5_10
  <=> sK1 = k6_domain_1(sK1,sK2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f129,plain,
    ( sK1 = k1_tarski(sK2(sK1))
    | spl5_1
    | ~ spl5_2
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f128,f108])).

fof(f108,plain,
    ( sK1 = k6_domain_1(sK1,sK2(sK1))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f106])).

fof(f128,plain,
    ( k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f127,f52])).

fof(f52,plain,
    ( v1_zfmisc_1(sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f127,plain,
    ( k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))
    | ~ v1_zfmisc_1(sK1)
    | spl5_1 ),
    inference(subsumption_resolution,[],[f126,f47])).

fof(f47,plain,
    ( ~ v1_xboole_0(sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f126,plain,
    ( k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))
    | v1_xboole_0(sK1)
    | ~ v1_zfmisc_1(sK1)
    | spl5_1 ),
    inference(resolution,[],[f59,f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

fof(f59,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k1_tarski(X0) = k6_domain_1(sK1,X0) )
    | spl5_1 ),
    inference(resolution,[],[f47,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f114,plain,
    ( spl5_11
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f90,f83,f111])).

fof(f83,plain,
    ( spl5_7
  <=> r2_hidden(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f90,plain,
    ( r1_tarski(k1_tarski(sK3(sK0)),sK0)
    | ~ spl5_7 ),
    inference(resolution,[],[f85,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f85,plain,
    ( r2_hidden(sK3(sK0),sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f83])).

fof(f109,plain,
    ( spl5_10
    | spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f62,f50,f45,f106])).

fof(f62,plain,
    ( sK1 = k6_domain_1(sK1,sK2(sK1))
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f61,f52])).

fof(f61,plain,
    ( sK1 = k6_domain_1(sK1,sK2(sK1))
    | ~ v1_zfmisc_1(sK1)
    | spl5_1 ),
    inference(resolution,[],[f47,f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | k6_domain_1(X0,sK2(X0)) = X0
      | ~ v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f97,plain,
    ( spl5_8
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f76,f67,f94])).

fof(f67,plain,
    ( spl5_4
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f76,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl5_4 ),
    inference(resolution,[],[f69,f36])).

fof(f69,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f86,plain,
    ( spl5_7
    | spl5_3 ),
    inference(avatar_split_clause,[],[f64,f55,f83])).

fof(f55,plain,
    ( spl5_3
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f64,plain,
    ( r2_hidden(sK3(sK0),sK0)
    | spl5_3 ),
    inference(resolution,[],[f57,f31])).

fof(f31,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f57,plain,
    ( ~ v1_xboole_0(sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f75,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f25,f72])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f70,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f24,f67])).

fof(f24,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f58,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f26,f55])).

fof(f26,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f53,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f23,f50])).

fof(f23,plain,(
    v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f48,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f22,f45])).

fof(f22,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:13:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (5579)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (5587)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.48  % (5595)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.48  % (5573)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.49  % (5589)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.49  % (5582)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.49  % (5587)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f185,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f48,f53,f58,f70,f75,f86,f97,f109,f114,f138,f163,f181,f184])).
% 0.20/0.49  fof(f184,plain,(
% 0.20/0.49    ~spl5_14 | ~spl5_17),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f183])).
% 0.20/0.49  fof(f183,plain,(
% 0.20/0.49    $false | (~spl5_14 | ~spl5_17)),
% 0.20/0.49    inference(subsumption_resolution,[],[f137,f162])).
% 0.20/0.49  fof(f162,plain,(
% 0.20/0.49    ( ! [X0] : (k1_tarski(X0) != sK1) ) | ~spl5_17),
% 0.20/0.49    inference(avatar_component_clause,[],[f161])).
% 0.20/0.49  fof(f161,plain,(
% 0.20/0.49    spl5_17 <=> ! [X0] : k1_tarski(X0) != sK1),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.20/0.49  fof(f137,plain,(
% 0.20/0.49    sK1 = k1_tarski(sK2(sK1)) | ~spl5_14),
% 0.20/0.49    inference(avatar_component_clause,[],[f135])).
% 0.20/0.49  fof(f135,plain,(
% 0.20/0.49    spl5_14 <=> sK1 = k1_tarski(sK2(sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.20/0.49  fof(f181,plain,(
% 0.20/0.49    ~spl5_11 | ~spl5_16),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f180])).
% 0.20/0.49  fof(f180,plain,(
% 0.20/0.49    $false | (~spl5_11 | ~spl5_16)),
% 0.20/0.49    inference(subsumption_resolution,[],[f174,f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.20/0.49  fof(f174,plain,(
% 0.20/0.49    k1_xboole_0 = k2_xboole_0(k1_tarski(sK3(k1_xboole_0)),k1_xboole_0) | (~spl5_11 | ~spl5_16)),
% 0.20/0.49    inference(backward_demodulation,[],[f133,f159])).
% 0.20/0.49  fof(f159,plain,(
% 0.20/0.49    k1_xboole_0 = sK0 | ~spl5_16),
% 0.20/0.49    inference(avatar_component_clause,[],[f157])).
% 0.20/0.49  fof(f157,plain,(
% 0.20/0.49    spl5_16 <=> k1_xboole_0 = sK0),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.49  fof(f133,plain,(
% 0.20/0.49    sK0 = k2_xboole_0(k1_tarski(sK3(sK0)),sK0) | ~spl5_11),
% 0.20/0.49    inference(resolution,[],[f113,f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.49  fof(f113,plain,(
% 0.20/0.49    r1_tarski(k1_tarski(sK3(sK0)),sK0) | ~spl5_11),
% 0.20/0.49    inference(avatar_component_clause,[],[f111])).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    spl5_11 <=> r1_tarski(k1_tarski(sK3(sK0)),sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.49  fof(f163,plain,(
% 0.20/0.49    spl5_16 | spl5_17 | spl5_5 | ~spl5_8 | ~spl5_14),
% 0.20/0.49    inference(avatar_split_clause,[],[f148,f135,f94,f72,f161,f157])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    spl5_5 <=> sK0 = sK1),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    spl5_8 <=> sK1 = k2_xboole_0(sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.49  fof(f148,plain,(
% 0.20/0.49    ( ! [X0] : (k1_tarski(X0) != sK1 | k1_xboole_0 = sK0) ) | (spl5_5 | ~spl5_8 | ~spl5_14)),
% 0.20/0.49    inference(subsumption_resolution,[],[f99,f147])).
% 0.20/0.49  fof(f147,plain,(
% 0.20/0.49    k1_xboole_0 != sK1 | (~spl5_8 | ~spl5_14)),
% 0.20/0.49    inference(superposition,[],[f142,f96])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    sK1 = k2_xboole_0(sK0,sK1) | ~spl5_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f94])).
% 0.20/0.49  fof(f142,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 != k2_xboole_0(X0,sK1)) ) | ~spl5_14),
% 0.20/0.49    inference(superposition,[],[f141,f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.49  fof(f141,plain,(
% 0.20/0.49    ( ! [X3] : (k1_xboole_0 != k2_xboole_0(sK1,X3)) ) | ~spl5_14),
% 0.20/0.49    inference(superposition,[],[f33,f137])).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    ( ! [X0] : (k1_tarski(X0) != sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1) ) | (spl5_5 | ~spl5_8)),
% 0.20/0.49    inference(subsumption_resolution,[],[f98,f74])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    sK0 != sK1 | spl5_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f72])).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    ( ! [X0] : (k1_tarski(X0) != sK1 | sK0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1) ) | ~spl5_8),
% 0.20/0.49    inference(superposition,[],[f43,f96])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k1_tarski(X0) != k2_xboole_0(X1,X2) | X1 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X2) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k1_xboole_0 = X2 | k1_xboole_0 = X1 | X1 = X2 | k1_tarski(X0) != k2_xboole_0(X1,X2))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 0.20/0.49  fof(f138,plain,(
% 0.20/0.49    spl5_14 | spl5_1 | ~spl5_2 | ~spl5_10),
% 0.20/0.49    inference(avatar_split_clause,[],[f129,f106,f50,f45,f135])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    spl5_1 <=> v1_xboole_0(sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    spl5_2 <=> v1_zfmisc_1(sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    spl5_10 <=> sK1 = k6_domain_1(sK1,sK2(sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.49  fof(f129,plain,(
% 0.20/0.49    sK1 = k1_tarski(sK2(sK1)) | (spl5_1 | ~spl5_2 | ~spl5_10)),
% 0.20/0.49    inference(forward_demodulation,[],[f128,f108])).
% 0.20/0.49  fof(f108,plain,(
% 0.20/0.49    sK1 = k6_domain_1(sK1,sK2(sK1)) | ~spl5_10),
% 0.20/0.49    inference(avatar_component_clause,[],[f106])).
% 0.20/0.49  fof(f128,plain,(
% 0.20/0.49    k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1)) | (spl5_1 | ~spl5_2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f127,f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    v1_zfmisc_1(sK1) | ~spl5_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f50])).
% 0.20/0.49  fof(f127,plain,(
% 0.20/0.49    k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1)) | ~v1_zfmisc_1(sK1) | spl5_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f126,f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ~v1_xboole_0(sK1) | spl5_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f45])).
% 0.20/0.49  fof(f126,plain,(
% 0.20/0.49    k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1)) | v1_xboole_0(sK1) | ~v1_zfmisc_1(sK1) | spl5_1),
% 0.20/0.49    inference(resolution,[],[f59,f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(sK2(X0),X0) | v1_xboole_0(X0) | ~v1_zfmisc_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,sK1) | k1_tarski(X0) = k6_domain_1(sK1,X0)) ) | spl5_1),
% 0.20/0.49    inference(resolution,[],[f47,f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.49    inference(flattening,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    spl5_11 | ~spl5_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f90,f83,f111])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    spl5_7 <=> r2_hidden(sK3(sK0),sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    r1_tarski(k1_tarski(sK3(sK0)),sK0) | ~spl5_7),
% 0.20/0.49    inference(resolution,[],[f85,f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    r2_hidden(sK3(sK0),sK0) | ~spl5_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f83])).
% 0.20/0.49  fof(f109,plain,(
% 0.20/0.49    spl5_10 | spl5_1 | ~spl5_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f62,f50,f45,f106])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    sK1 = k6_domain_1(sK1,sK2(sK1)) | (spl5_1 | ~spl5_2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f61,f52])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    sK1 = k6_domain_1(sK1,sK2(sK1)) | ~v1_zfmisc_1(sK1) | spl5_1),
% 0.20/0.49    inference(resolution,[],[f47,f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ( ! [X0] : (v1_xboole_0(X0) | k6_domain_1(X0,sK2(X0)) = X0 | ~v1_zfmisc_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    spl5_8 | ~spl5_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f76,f67,f94])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    spl5_4 <=> r1_tarski(sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    sK1 = k2_xboole_0(sK0,sK1) | ~spl5_4),
% 0.20/0.49    inference(resolution,[],[f69,f36])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    r1_tarski(sK0,sK1) | ~spl5_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f67])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    spl5_7 | spl5_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f64,f55,f83])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    spl5_3 <=> v1_xboole_0(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    r2_hidden(sK3(sK0),sK0) | spl5_3),
% 0.20/0.49    inference(resolution,[],[f57,f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ~v1_xboole_0(sK0) | spl5_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f55])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    ~spl5_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f25,f72])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    sK0 != sK1),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (X0 != X1 & r1_tarski(X0,X1) & v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.49    inference(flattening,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : ((X0 != X1 & r1_tarski(X0,X1)) & (v1_zfmisc_1(X1) & ~v1_xboole_0(X1))) & ~v1_xboole_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,negated_conjecture,(
% 0.20/0.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.20/0.49    inference(negated_conjecture,[],[f12])).
% 0.20/0.49  fof(f12,conjecture,(
% 0.20/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    spl5_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f24,f67])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    r1_tarski(sK0,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ~spl5_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f26,f55])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ~v1_xboole_0(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    spl5_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f23,f50])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    v1_zfmisc_1(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ~spl5_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f22,f45])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ~v1_xboole_0(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (5587)------------------------------
% 0.20/0.49  % (5587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (5587)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (5587)Memory used [KB]: 10746
% 0.20/0.49  % (5587)Time elapsed: 0.104 s
% 0.20/0.49  % (5587)------------------------------
% 0.20/0.49  % (5587)------------------------------
% 0.20/0.50  % (5589)Refutation not found, incomplete strategy% (5589)------------------------------
% 0.20/0.50  % (5589)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (5566)Success in time 0.142 s
%------------------------------------------------------------------------------
