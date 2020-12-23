%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 120 expanded)
%              Number of leaves         :   18 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :  228 ( 398 expanded)
%              Number of equality atoms :   10 (  17 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f119,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f35,f40,f45,f49,f53,f57,f61,f68,f74,f87,f118])).

fof(f118,plain,
    ( ~ spl2_1
    | spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_10
    | ~ spl2_12 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | ~ spl2_1
    | spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_10
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f116,f44])).

fof(f44,plain,
    ( ~ v1_xboole_0(sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl2_4
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f116,plain,
    ( v1_xboole_0(sK0)
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_10
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f115,f29])).

fof(f29,plain,
    ( v1_zfmisc_1(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl2_1
  <=> v1_zfmisc_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f115,plain,
    ( ~ v1_zfmisc_1(sK0)
    | v1_xboole_0(sK0)
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_10
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f114,f48])).

fof(f48,plain,
    ( ! [X0] : ~ v1_xboole_0(k1_tarski(X0))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl2_5
  <=> ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f114,plain,
    ( v1_xboole_0(k1_tarski(sK1))
    | ~ v1_zfmisc_1(sK0)
    | v1_xboole_0(sK0)
    | ~ spl2_6
    | ~ spl2_10
    | ~ spl2_12 ),
    inference(subsumption_resolution,[],[f108,f73])).

fof(f73,plain,
    ( v1_subset_1(k1_tarski(sK1),sK0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl2_10
  <=> v1_subset_1(k1_tarski(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f108,plain,
    ( ~ v1_subset_1(k1_tarski(sK1),sK0)
    | v1_xboole_0(k1_tarski(sK1))
    | ~ v1_zfmisc_1(sK0)
    | v1_xboole_0(sK0)
    | ~ spl2_6
    | ~ spl2_12 ),
    inference(resolution,[],[f52,f86])).

fof(f86,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl2_12
  <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f52,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_subset_1(X1,X0)
        | v1_xboole_0(X1)
        | ~ v1_zfmisc_1(X0)
        | v1_xboole_0(X0) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( v1_xboole_0(X1)
        | ~ v1_subset_1(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_zfmisc_1(X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f87,plain,
    ( spl2_12
    | ~ spl2_3
    | spl2_4
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f82,f65,f59,f42,f37,f84])).

fof(f37,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f59,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f65,plain,
    ( spl2_9
  <=> k6_domain_1(sK0,sK1) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f82,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    | ~ spl2_3
    | spl2_4
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f81,f44])).

fof(f81,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0)
    | ~ spl2_3
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f76,f39])).

fof(f39,plain,
    ( m1_subset_1(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f76,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(superposition,[],[f60,f67])).

fof(f67,plain,
    ( k6_domain_1(sK0,sK1) = k1_tarski(sK1)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f65])).

fof(f60,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f59])).

fof(f74,plain,
    ( spl2_10
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f69,f65,f32,f71])).

fof(f32,plain,
    ( spl2_2
  <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f69,plain,
    ( v1_subset_1(k1_tarski(sK1),sK0)
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(backward_demodulation,[],[f34,f67])).

fof(f34,plain,
    ( v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f68,plain,
    ( spl2_9
    | ~ spl2_3
    | spl2_4
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f63,f55,f42,f37,f65])).

fof(f55,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( k6_domain_1(X0,X1) = k1_tarski(X1)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f63,plain,
    ( k6_domain_1(sK0,sK1) = k1_tarski(sK1)
    | ~ spl2_3
    | spl2_4
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f62,f44])).

fof(f62,plain,
    ( k6_domain_1(sK0,sK1) = k1_tarski(sK1)
    | v1_xboole_0(sK0)
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(resolution,[],[f56,f39])).

fof(f56,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,X0)
        | k6_domain_1(X0,X1) = k1_tarski(X1)
        | v1_xboole_0(X0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f55])).

fof(f61,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f25,f59])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f57,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f24,f55])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f53,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f23,f51])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( v1_subset_1(X1,X0)
           => v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tex_2)).

fof(f49,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f22,f47])).

fof(f22,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f45,plain,(
    ~ spl2_4 ),
    inference(avatar_split_clause,[],[f18,f42])).

fof(f18,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( v1_zfmisc_1(sK0)
    & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
    & m1_subset_1(sK1,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v1_zfmisc_1(X0)
            & v1_subset_1(k6_domain_1(X0,X1),X0)
            & m1_subset_1(X1,X0) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( v1_zfmisc_1(sK0)
          & v1_subset_1(k6_domain_1(sK0,X1),sK0)
          & m1_subset_1(X1,sK0) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( v1_zfmisc_1(sK0)
        & v1_subset_1(k6_domain_1(sK0,X1),sK0)
        & m1_subset_1(X1,sK0) )
   => ( v1_zfmisc_1(sK0)
      & v1_subset_1(k6_domain_1(sK0,sK1),sK0)
      & m1_subset_1(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X0)
          & v1_subset_1(k6_domain_1(X0,X1),X0)
          & m1_subset_1(X1,X0) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,X0)
           => ~ ( v1_zfmisc_1(X0)
                & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ~ ( v1_zfmisc_1(X0)
              & v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

fof(f40,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f19,f37])).

fof(f19,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f35,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f20,f32])).

fof(f20,plain,(
    v1_subset_1(k6_domain_1(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f30,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f21,f27])).

fof(f21,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:37:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.40  % (22951)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.40  % (22954)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.41  % (22956)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.41  % (22956)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f119,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(avatar_sat_refutation,[],[f30,f35,f40,f45,f49,f53,f57,f61,f68,f74,f87,f118])).
% 0.20/0.41  fof(f118,plain,(
% 0.20/0.41    ~spl2_1 | spl2_4 | ~spl2_5 | ~spl2_6 | ~spl2_10 | ~spl2_12),
% 0.20/0.41    inference(avatar_contradiction_clause,[],[f117])).
% 0.20/0.41  fof(f117,plain,(
% 0.20/0.41    $false | (~spl2_1 | spl2_4 | ~spl2_5 | ~spl2_6 | ~spl2_10 | ~spl2_12)),
% 0.20/0.41    inference(subsumption_resolution,[],[f116,f44])).
% 0.20/0.41  fof(f44,plain,(
% 0.20/0.41    ~v1_xboole_0(sK0) | spl2_4),
% 0.20/0.41    inference(avatar_component_clause,[],[f42])).
% 0.20/0.41  fof(f42,plain,(
% 0.20/0.41    spl2_4 <=> v1_xboole_0(sK0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.41  fof(f116,plain,(
% 0.20/0.41    v1_xboole_0(sK0) | (~spl2_1 | ~spl2_5 | ~spl2_6 | ~spl2_10 | ~spl2_12)),
% 0.20/0.41    inference(subsumption_resolution,[],[f115,f29])).
% 0.20/0.41  fof(f29,plain,(
% 0.20/0.41    v1_zfmisc_1(sK0) | ~spl2_1),
% 0.20/0.41    inference(avatar_component_clause,[],[f27])).
% 0.20/0.41  fof(f27,plain,(
% 0.20/0.41    spl2_1 <=> v1_zfmisc_1(sK0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.41  fof(f115,plain,(
% 0.20/0.41    ~v1_zfmisc_1(sK0) | v1_xboole_0(sK0) | (~spl2_5 | ~spl2_6 | ~spl2_10 | ~spl2_12)),
% 0.20/0.41    inference(subsumption_resolution,[],[f114,f48])).
% 0.20/0.41  fof(f48,plain,(
% 0.20/0.41    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) ) | ~spl2_5),
% 0.20/0.41    inference(avatar_component_clause,[],[f47])).
% 0.20/0.41  fof(f47,plain,(
% 0.20/0.41    spl2_5 <=> ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.41  fof(f114,plain,(
% 0.20/0.41    v1_xboole_0(k1_tarski(sK1)) | ~v1_zfmisc_1(sK0) | v1_xboole_0(sK0) | (~spl2_6 | ~spl2_10 | ~spl2_12)),
% 0.20/0.41    inference(subsumption_resolution,[],[f108,f73])).
% 0.20/0.41  fof(f73,plain,(
% 0.20/0.41    v1_subset_1(k1_tarski(sK1),sK0) | ~spl2_10),
% 0.20/0.41    inference(avatar_component_clause,[],[f71])).
% 0.20/0.41  fof(f71,plain,(
% 0.20/0.41    spl2_10 <=> v1_subset_1(k1_tarski(sK1),sK0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.41  fof(f108,plain,(
% 0.20/0.41    ~v1_subset_1(k1_tarski(sK1),sK0) | v1_xboole_0(k1_tarski(sK1)) | ~v1_zfmisc_1(sK0) | v1_xboole_0(sK0) | (~spl2_6 | ~spl2_12)),
% 0.20/0.41    inference(resolution,[],[f52,f86])).
% 0.20/0.41  fof(f86,plain,(
% 0.20/0.41    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) | ~spl2_12),
% 0.20/0.41    inference(avatar_component_clause,[],[f84])).
% 0.20/0.41  fof(f84,plain,(
% 0.20/0.41    spl2_12 <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.20/0.41  fof(f52,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) ) | ~spl2_6),
% 0.20/0.41    inference(avatar_component_clause,[],[f51])).
% 0.20/0.41  fof(f51,plain,(
% 0.20/0.41    spl2_6 <=> ! [X1,X0] : (v1_xboole_0(X1) | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.41  fof(f87,plain,(
% 0.20/0.41    spl2_12 | ~spl2_3 | spl2_4 | ~spl2_8 | ~spl2_9),
% 0.20/0.41    inference(avatar_split_clause,[],[f82,f65,f59,f42,f37,f84])).
% 0.20/0.41  fof(f37,plain,(
% 0.20/0.41    spl2_3 <=> m1_subset_1(sK1,sK0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.41  fof(f59,plain,(
% 0.20/0.41    spl2_8 <=> ! [X1,X0] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.41  fof(f65,plain,(
% 0.20/0.41    spl2_9 <=> k6_domain_1(sK0,sK1) = k1_tarski(sK1)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.41  fof(f82,plain,(
% 0.20/0.41    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) | (~spl2_3 | spl2_4 | ~spl2_8 | ~spl2_9)),
% 0.20/0.41    inference(subsumption_resolution,[],[f81,f44])).
% 0.20/0.41  fof(f81,plain,(
% 0.20/0.41    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) | v1_xboole_0(sK0) | (~spl2_3 | ~spl2_8 | ~spl2_9)),
% 0.20/0.41    inference(subsumption_resolution,[],[f76,f39])).
% 0.20/0.41  fof(f39,plain,(
% 0.20/0.41    m1_subset_1(sK1,sK0) | ~spl2_3),
% 0.20/0.41    inference(avatar_component_clause,[],[f37])).
% 0.20/0.41  fof(f76,plain,(
% 0.20/0.41    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,sK0) | v1_xboole_0(sK0) | (~spl2_8 | ~spl2_9)),
% 0.20/0.41    inference(superposition,[],[f60,f67])).
% 0.20/0.41  fof(f67,plain,(
% 0.20/0.41    k6_domain_1(sK0,sK1) = k1_tarski(sK1) | ~spl2_9),
% 0.20/0.41    inference(avatar_component_clause,[],[f65])).
% 0.20/0.41  fof(f60,plain,(
% 0.20/0.41    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) ) | ~spl2_8),
% 0.20/0.41    inference(avatar_component_clause,[],[f59])).
% 0.20/0.41  fof(f74,plain,(
% 0.20/0.41    spl2_10 | ~spl2_2 | ~spl2_9),
% 0.20/0.41    inference(avatar_split_clause,[],[f69,f65,f32,f71])).
% 0.20/0.41  fof(f32,plain,(
% 0.20/0.41    spl2_2 <=> v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.41  fof(f69,plain,(
% 0.20/0.41    v1_subset_1(k1_tarski(sK1),sK0) | (~spl2_2 | ~spl2_9)),
% 0.20/0.41    inference(backward_demodulation,[],[f34,f67])).
% 0.20/0.41  fof(f34,plain,(
% 0.20/0.41    v1_subset_1(k6_domain_1(sK0,sK1),sK0) | ~spl2_2),
% 0.20/0.41    inference(avatar_component_clause,[],[f32])).
% 0.20/0.41  fof(f68,plain,(
% 0.20/0.41    spl2_9 | ~spl2_3 | spl2_4 | ~spl2_7),
% 0.20/0.41    inference(avatar_split_clause,[],[f63,f55,f42,f37,f65])).
% 0.20/0.41  fof(f55,plain,(
% 0.20/0.41    spl2_7 <=> ! [X1,X0] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.41  fof(f63,plain,(
% 0.20/0.41    k6_domain_1(sK0,sK1) = k1_tarski(sK1) | (~spl2_3 | spl2_4 | ~spl2_7)),
% 0.20/0.41    inference(subsumption_resolution,[],[f62,f44])).
% 0.20/0.41  fof(f62,plain,(
% 0.20/0.41    k6_domain_1(sK0,sK1) = k1_tarski(sK1) | v1_xboole_0(sK0) | (~spl2_3 | ~spl2_7)),
% 0.20/0.41    inference(resolution,[],[f56,f39])).
% 0.20/0.41  fof(f56,plain,(
% 0.20/0.41    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)) ) | ~spl2_7),
% 0.20/0.41    inference(avatar_component_clause,[],[f55])).
% 0.20/0.41  fof(f61,plain,(
% 0.20/0.41    spl2_8),
% 0.20/0.41    inference(avatar_split_clause,[],[f25,f59])).
% 0.20/0.41  fof(f25,plain,(
% 0.20/0.41    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f14])).
% 0.20/0.41  fof(f14,plain,(
% 0.20/0.41    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.41    inference(flattening,[],[f13])).
% 0.20/0.41  fof(f13,plain,(
% 0.20/0.41    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.41    inference(ennf_transformation,[],[f2])).
% 0.20/0.41  fof(f2,axiom,(
% 0.20/0.41    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.20/0.41  fof(f57,plain,(
% 0.20/0.41    spl2_7),
% 0.20/0.41    inference(avatar_split_clause,[],[f24,f55])).
% 0.20/0.41  fof(f24,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f12])).
% 0.20/0.41  fof(f12,plain,(
% 0.20/0.41    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.41    inference(flattening,[],[f11])).
% 0.20/0.41  fof(f11,plain,(
% 0.20/0.41    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.41    inference(ennf_transformation,[],[f3])).
% 0.20/0.41  fof(f3,axiom,(
% 0.20/0.41    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.41  fof(f53,plain,(
% 0.20/0.41    spl2_6),
% 0.20/0.41    inference(avatar_split_clause,[],[f23,f51])).
% 0.20/0.41  fof(f23,plain,(
% 0.20/0.41    ( ! [X0,X1] : (v1_xboole_0(X1) | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.41    inference(cnf_transformation,[],[f10])).
% 0.20/0.41  fof(f10,plain,(
% 0.20/0.41    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.20/0.41    inference(flattening,[],[f9])).
% 0.20/0.41  fof(f9,plain,(
% 0.20/0.41    ! [X0] : (! [X1] : ((v1_xboole_0(X1) | ~v1_subset_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.20/0.41    inference(ennf_transformation,[],[f4])).
% 0.20/0.41  fof(f4,axiom,(
% 0.20/0.41    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) => v1_xboole_0(X1))))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tex_2)).
% 0.20/0.41  fof(f49,plain,(
% 0.20/0.41    spl2_5),
% 0.20/0.41    inference(avatar_split_clause,[],[f22,f47])).
% 0.20/0.41  fof(f22,plain,(
% 0.20/0.41    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.20/0.41    inference(cnf_transformation,[],[f1])).
% 0.20/0.41  fof(f1,axiom,(
% 0.20/0.41    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.20/0.41  fof(f45,plain,(
% 0.20/0.41    ~spl2_4),
% 0.20/0.41    inference(avatar_split_clause,[],[f18,f42])).
% 0.20/0.41  fof(f18,plain,(
% 0.20/0.41    ~v1_xboole_0(sK0)),
% 0.20/0.41    inference(cnf_transformation,[],[f17])).
% 0.20/0.41  fof(f17,plain,(
% 0.20/0.41    (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0)) & ~v1_xboole_0(sK0)),
% 0.20/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f16,f15])).
% 0.20/0.41  fof(f15,plain,(
% 0.20/0.41    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0)) => (? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) & ~v1_xboole_0(sK0))),
% 0.20/0.41    introduced(choice_axiom,[])).
% 0.20/0.41  fof(f16,plain,(
% 0.20/0.41    ? [X1] : (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,X1),sK0) & m1_subset_1(X1,sK0)) => (v1_zfmisc_1(sK0) & v1_subset_1(k6_domain_1(sK0,sK1),sK0) & m1_subset_1(sK1,sK0))),
% 0.20/0.41    introduced(choice_axiom,[])).
% 0.20/0.41  fof(f8,plain,(
% 0.20/0.41    ? [X0] : (? [X1] : (v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.20/0.41    inference(flattening,[],[f7])).
% 0.20/0.41  fof(f7,plain,(
% 0.20/0.41    ? [X0] : (? [X1] : ((v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0)) & m1_subset_1(X1,X0)) & ~v1_xboole_0(X0))),
% 0.20/0.41    inference(ennf_transformation,[],[f6])).
% 0.20/0.41  fof(f6,negated_conjecture,(
% 0.20/0.41    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.20/0.41    inference(negated_conjecture,[],[f5])).
% 0.20/0.41  fof(f5,conjecture,(
% 0.20/0.41    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,X0) => ~(v1_zfmisc_1(X0) & v1_subset_1(k6_domain_1(X0,X1),X0))))),
% 0.20/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).
% 0.20/0.41  fof(f40,plain,(
% 0.20/0.41    spl2_3),
% 0.20/0.41    inference(avatar_split_clause,[],[f19,f37])).
% 0.20/0.41  fof(f19,plain,(
% 0.20/0.41    m1_subset_1(sK1,sK0)),
% 0.20/0.41    inference(cnf_transformation,[],[f17])).
% 0.20/0.41  fof(f35,plain,(
% 0.20/0.41    spl2_2),
% 0.20/0.41    inference(avatar_split_clause,[],[f20,f32])).
% 0.20/0.41  fof(f20,plain,(
% 0.20/0.41    v1_subset_1(k6_domain_1(sK0,sK1),sK0)),
% 0.20/0.41    inference(cnf_transformation,[],[f17])).
% 0.20/0.41  fof(f30,plain,(
% 0.20/0.41    spl2_1),
% 0.20/0.41    inference(avatar_split_clause,[],[f21,f27])).
% 0.20/0.41  fof(f21,plain,(
% 0.20/0.41    v1_zfmisc_1(sK0)),
% 0.20/0.41    inference(cnf_transformation,[],[f17])).
% 0.20/0.41  % SZS output end Proof for theBenchmark
% 0.20/0.41  % (22956)------------------------------
% 0.20/0.41  % (22956)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (22956)Termination reason: Refutation
% 0.20/0.41  
% 0.20/0.41  % (22956)Memory used [KB]: 6140
% 0.20/0.41  % (22956)Time elapsed: 0.005 s
% 0.20/0.41  % (22956)------------------------------
% 0.20/0.41  % (22956)------------------------------
% 0.20/0.41  % (22945)Success in time 0.065 s
%------------------------------------------------------------------------------
