%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 124 expanded)
%              Number of leaves         :   15 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :  199 ( 405 expanded)
%              Number of equality atoms :   31 (  66 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f142,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f54,f59,f68,f79,f91,f104,f116,f130,f141])).

fof(f141,plain,
    ( ~ spl7_1
    | ~ spl7_7
    | ~ spl7_9
    | spl7_12 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_7
    | ~ spl7_9
    | spl7_12 ),
    inference(subsumption_resolution,[],[f139,f78])).

fof(f78,plain,
    ( r2_hidden(sK2,k9_relat_1(sK3,sK0))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl7_7
  <=> r2_hidden(sK2,k9_relat_1(sK3,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f139,plain,
    ( ~ r2_hidden(sK2,k9_relat_1(sK3,sK0))
    | ~ spl7_1
    | ~ spl7_9
    | spl7_12 ),
    inference(resolution,[],[f129,f92])).

fof(f92,plain,
    ( ! [X2,X3] :
        ( sP5(X2,X3,sK3)
        | ~ r2_hidden(X2,k9_relat_1(sK3,X3)) )
    | ~ spl7_1
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f42,f85])).

fof(f85,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl7_9
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f42,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(sK3)
        | sP5(X2,X3,sK3)
        | ~ r2_hidden(X2,k9_relat_1(sK3,X3)) )
    | ~ spl7_1 ),
    inference(resolution,[],[f39,f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sP5(X3,X1,X0)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

fof(f39,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl7_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f129,plain,
    ( ~ sP5(sK2,sK0,sK3)
    | spl7_12 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl7_12
  <=> sP5(sK2,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f130,plain,
    ( ~ spl7_12
    | spl7_11 ),
    inference(avatar_split_clause,[],[f120,f113,f127])).

fof(f113,plain,
    ( spl7_11
  <=> r2_hidden(sK6(sK3,sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f120,plain,
    ( ~ sP5(sK2,sK0,sK3)
    | spl7_11 ),
    inference(resolution,[],[f115,f23])).

fof(f23,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK6(X0,X1,X3),X1)
      | ~ sP5(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f115,plain,
    ( ~ r2_hidden(sK6(sK3,sK0,sK2),sK0)
    | spl7_11 ),
    inference(avatar_component_clause,[],[f113])).

fof(f116,plain,
    ( ~ spl7_11
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f108,f101,f113])).

fof(f101,plain,
    ( spl7_10
  <=> sK2 = k1_funct_1(sK3,sK6(sK3,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f108,plain,
    ( ~ r2_hidden(sK6(sK3,sK0,sK2),sK0)
    | ~ spl7_10 ),
    inference(trivial_inequality_removal,[],[f106])).

fof(f106,plain,
    ( sK2 != sK2
    | ~ r2_hidden(sK6(sK3,sK0,sK2),sK0)
    | ~ spl7_10 ),
    inference(superposition,[],[f15,f103])).

fof(f103,plain,
    ( sK2 = k1_funct_1(sK3,sK6(sK3,sK0,sK2))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f101])).

fof(f15,plain,(
    ! [X4] :
      ( sK2 != k1_funct_1(sK3,X4)
      | ~ r2_hidden(X4,sK0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X2
          | ~ r2_hidden(X4,X0) )
      & r2_hidden(X2,k2_relset_1(X0,X1,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X2
          | ~ r2_hidden(X4,X0) )
      & r2_hidden(X2,k2_relset_1(X0,X1,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ~ ( k1_funct_1(X3,X4) = X2
                  & r2_hidden(X4,X0) )
            & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ~ ( k1_funct_1(X3,X4) = X2
                & r2_hidden(X4,X0) )
          & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).

fof(f104,plain,
    ( spl7_10
    | ~ spl7_1
    | ~ spl7_7
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f96,f84,f76,f37,f101])).

fof(f96,plain,
    ( sK2 = k1_funct_1(sK3,sK6(sK3,sK0,sK2))
    | ~ spl7_1
    | ~ spl7_7
    | ~ spl7_9 ),
    inference(resolution,[],[f93,f78])).

fof(f93,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | k1_funct_1(sK3,sK6(sK3,X1,X0)) = X0 )
    | ~ spl7_1
    | ~ spl7_9 ),
    inference(resolution,[],[f92,f24])).

fof(f24,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | k1_funct_1(X0,sK6(X0,X1,X3)) = X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f91,plain,
    ( ~ spl7_3
    | spl7_9 ),
    inference(avatar_contradiction_clause,[],[f90])).

fof(f90,plain,
    ( $false
    | ~ spl7_3
    | spl7_9 ),
    inference(subsumption_resolution,[],[f89,f29])).

fof(f29,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f89,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl7_3
    | spl7_9 ),
    inference(resolution,[],[f88,f53])).

fof(f53,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl7_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f88,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl7_9 ),
    inference(resolution,[],[f86,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f86,plain,
    ( ~ v1_relat_1(sK3)
    | spl7_9 ),
    inference(avatar_component_clause,[],[f84])).

fof(f79,plain,
    ( spl7_7
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f69,f65,f56,f76])).

fof(f56,plain,
    ( spl7_4
  <=> r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f65,plain,
    ( spl7_5
  <=> k2_relset_1(sK0,sK1,sK3) = k9_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f69,plain,
    ( r2_hidden(sK2,k9_relat_1(sK3,sK0))
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(superposition,[],[f58,f67])).

fof(f67,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k9_relat_1(sK3,sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f65])).

fof(f58,plain,
    ( r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f68,plain,
    ( spl7_5
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f63,f51,f65])).

fof(f63,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k9_relat_1(sK3,sK0)
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f61,f60])).

fof(f60,plain,
    ( ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)
    | ~ spl7_3 ),
    inference(resolution,[],[f53,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f61,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k7_relset_1(sK0,sK1,sK3,sK0)
    | ~ spl7_3 ),
    inference(resolution,[],[f53,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f59,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f19,f56])).

fof(f19,plain,(
    r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f54,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f18,f51])).

fof(f18,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f9])).

fof(f40,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f16,f37])).

fof(f16,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n011.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 10:00:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.46  % (2543)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.47  % (2531)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (2538)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.48  % (2529)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.48  % (2541)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (2530)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.48  % (2532)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (2529)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f142,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f40,f54,f59,f68,f79,f91,f104,f116,f130,f141])).
% 0.20/0.48  fof(f141,plain,(
% 0.20/0.48    ~spl7_1 | ~spl7_7 | ~spl7_9 | spl7_12),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f140])).
% 0.20/0.48  fof(f140,plain,(
% 0.20/0.48    $false | (~spl7_1 | ~spl7_7 | ~spl7_9 | spl7_12)),
% 0.20/0.48    inference(subsumption_resolution,[],[f139,f78])).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    r2_hidden(sK2,k9_relat_1(sK3,sK0)) | ~spl7_7),
% 0.20/0.48    inference(avatar_component_clause,[],[f76])).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    spl7_7 <=> r2_hidden(sK2,k9_relat_1(sK3,sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.48  fof(f139,plain,(
% 0.20/0.48    ~r2_hidden(sK2,k9_relat_1(sK3,sK0)) | (~spl7_1 | ~spl7_9 | spl7_12)),
% 0.20/0.48    inference(resolution,[],[f129,f92])).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    ( ! [X2,X3] : (sP5(X2,X3,sK3) | ~r2_hidden(X2,k9_relat_1(sK3,X3))) ) | (~spl7_1 | ~spl7_9)),
% 0.20/0.48    inference(subsumption_resolution,[],[f42,f85])).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    v1_relat_1(sK3) | ~spl7_9),
% 0.20/0.48    inference(avatar_component_clause,[],[f84])).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    spl7_9 <=> v1_relat_1(sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X2,X3] : (~v1_relat_1(sK3) | sP5(X2,X3,sK3) | ~r2_hidden(X2,k9_relat_1(sK3,X3))) ) | ~spl7_1),
% 0.20/0.48    inference(resolution,[],[f39,f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X0,X3,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | sP5(X3,X1,X0) | ~r2_hidden(X3,k9_relat_1(X0,X1))) )),
% 0.20/0.48    inference(equality_resolution,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | sP5(X3,X1,X0) | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    v1_funct_1(sK3) | ~spl7_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    spl7_1 <=> v1_funct_1(sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.48  fof(f129,plain,(
% 0.20/0.48    ~sP5(sK2,sK0,sK3) | spl7_12),
% 0.20/0.48    inference(avatar_component_clause,[],[f127])).
% 0.20/0.48  fof(f127,plain,(
% 0.20/0.48    spl7_12 <=> sP5(sK2,sK0,sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.20/0.48  fof(f130,plain,(
% 0.20/0.48    ~spl7_12 | spl7_11),
% 0.20/0.48    inference(avatar_split_clause,[],[f120,f113,f127])).
% 0.20/0.48  fof(f113,plain,(
% 0.20/0.48    spl7_11 <=> r2_hidden(sK6(sK3,sK0,sK2),sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.20/0.48  fof(f120,plain,(
% 0.20/0.48    ~sP5(sK2,sK0,sK3) | spl7_11),
% 0.20/0.48    inference(resolution,[],[f115,f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ( ! [X0,X3,X1] : (r2_hidden(sK6(X0,X1,X3),X1) | ~sP5(X3,X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    ~r2_hidden(sK6(sK3,sK0,sK2),sK0) | spl7_11),
% 0.20/0.48    inference(avatar_component_clause,[],[f113])).
% 0.20/0.48  fof(f116,plain,(
% 0.20/0.48    ~spl7_11 | ~spl7_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f108,f101,f113])).
% 0.20/0.48  fof(f101,plain,(
% 0.20/0.48    spl7_10 <=> sK2 = k1_funct_1(sK3,sK6(sK3,sK0,sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.20/0.48  fof(f108,plain,(
% 0.20/0.48    ~r2_hidden(sK6(sK3,sK0,sK2),sK0) | ~spl7_10),
% 0.20/0.48    inference(trivial_inequality_removal,[],[f106])).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    sK2 != sK2 | ~r2_hidden(sK6(sK3,sK0,sK2),sK0) | ~spl7_10),
% 0.20/0.48    inference(superposition,[],[f15,f103])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    sK2 = k1_funct_1(sK3,sK6(sK3,sK0,sK2)) | ~spl7_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f101])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ( ! [X4] : (sK2 != k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,plain,(
% 0.20/0.48    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.20/0.48    inference(flattening,[],[f8])).
% 0.20/0.48  fof(f8,plain,(
% 0.20/0.48    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 0.20/0.48    inference(negated_conjecture,[],[f6])).
% 0.20/0.48  fof(f6,conjecture,(
% 0.20/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_funct_2)).
% 0.20/0.48  fof(f104,plain,(
% 0.20/0.48    spl7_10 | ~spl7_1 | ~spl7_7 | ~spl7_9),
% 0.20/0.48    inference(avatar_split_clause,[],[f96,f84,f76,f37,f101])).
% 0.20/0.48  fof(f96,plain,(
% 0.20/0.48    sK2 = k1_funct_1(sK3,sK6(sK3,sK0,sK2)) | (~spl7_1 | ~spl7_7 | ~spl7_9)),
% 0.20/0.48    inference(resolution,[],[f93,f78])).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | k1_funct_1(sK3,sK6(sK3,X1,X0)) = X0) ) | (~spl7_1 | ~spl7_9)),
% 0.20/0.48    inference(resolution,[],[f92,f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ( ! [X0,X3,X1] : (~sP5(X3,X1,X0) | k1_funct_1(X0,sK6(X0,X1,X3)) = X3) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    ~spl7_3 | spl7_9),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f90])).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    $false | (~spl7_3 | spl7_9)),
% 0.20/0.48    inference(subsumption_resolution,[],[f89,f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl7_3 | spl7_9)),
% 0.20/0.48    inference(resolution,[],[f88,f53])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f51])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    spl7_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl7_9),
% 0.20/0.48    inference(resolution,[],[f86,f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    ~v1_relat_1(sK3) | spl7_9),
% 0.20/0.48    inference(avatar_component_clause,[],[f84])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    spl7_7 | ~spl7_4 | ~spl7_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f69,f65,f56,f76])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    spl7_4 <=> r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    spl7_5 <=> k2_relset_1(sK0,sK1,sK3) = k9_relat_1(sK3,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    r2_hidden(sK2,k9_relat_1(sK3,sK0)) | (~spl7_4 | ~spl7_5)),
% 0.20/0.48    inference(superposition,[],[f58,f67])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    k2_relset_1(sK0,sK1,sK3) = k9_relat_1(sK3,sK0) | ~spl7_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f65])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3)) | ~spl7_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f56])).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    spl7_5 | ~spl7_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f63,f51,f65])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    k2_relset_1(sK0,sK1,sK3) = k9_relat_1(sK3,sK0) | ~spl7_3),
% 0.20/0.48    inference(forward_demodulation,[],[f61,f60])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) ) | ~spl7_3),
% 0.20/0.48    inference(resolution,[],[f53,f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    k2_relset_1(sK0,sK1,sK3) = k7_relset_1(sK0,sK1,sK3,sK0) | ~spl7_3),
% 0.20/0.48    inference(resolution,[],[f53,f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    spl7_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f19,f56])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    r2_hidden(sK2,k2_relset_1(sK0,sK1,sK3))),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    spl7_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f18,f51])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    spl7_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f16,f37])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    v1_funct_1(sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (2529)------------------------------
% 0.20/0.48  % (2529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (2529)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (2529)Memory used [KB]: 10618
% 0.20/0.48  % (2529)Time elapsed: 0.065 s
% 0.20/0.48  % (2529)------------------------------
% 0.20/0.48  % (2529)------------------------------
% 0.20/0.48  % (2522)Success in time 0.134 s
%------------------------------------------------------------------------------
