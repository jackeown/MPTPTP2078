%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 150 expanded)
%              Number of leaves         :   19 (  57 expanded)
%              Depth                    :    8
%              Number of atoms          :  245 ( 549 expanded)
%              Number of equality atoms :   49 ( 122 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f122,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f37,f42,f47,f52,f62,f67,f72,f78,f86,f89,f97,f104,f113,f121])).

fof(f121,plain,
    ( ~ spl4_3
    | spl4_5
    | ~ spl4_10
    | ~ spl4_13
    | ~ spl4_14 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | ~ spl4_3
    | spl4_5
    | ~ spl4_10
    | ~ spl4_13
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f119,f41])).

fof(f41,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl4_3
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f119,plain,
    ( ~ r2_hidden(sK2,sK0)
    | spl4_5
    | ~ spl4_10
    | ~ spl4_13
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f115,f51])).

fof(f51,plain,
    ( sK2 != sK3
    | spl4_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl4_5
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f115,plain,
    ( sK2 = sK3
    | ~ r2_hidden(sK2,sK0)
    | ~ spl4_10
    | ~ spl4_13
    | ~ spl4_14 ),
    inference(superposition,[],[f106,f112])).

fof(f112,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl4_14
  <=> sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f106,plain,
    ( ! [X1] :
        ( k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X1)) = X1
        | ~ r2_hidden(X1,sK0) )
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(superposition,[],[f81,f101])).

fof(f101,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl4_13
  <=> sK0 = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f81,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl4_10
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f113,plain,
    ( spl4_14
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f108,f99,f80,f69,f44,f110])).

fof(f44,plain,
    ( spl4_4
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f69,plain,
    ( spl4_8
  <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f108,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f107,f46])).

fof(f46,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f107,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ r2_hidden(sK3,sK0)
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(superposition,[],[f106,f71])).

fof(f71,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f69])).

fof(f104,plain,
    ( spl4_13
    | ~ spl4_9
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f102,f94,f75,f99])).

fof(f75,plain,
    ( spl4_9
  <=> k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f94,plain,
    ( spl4_12
  <=> sK0 = k1_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f102,plain,
    ( sK0 = k1_relat_1(sK1)
    | ~ spl4_9
    | ~ spl4_12 ),
    inference(superposition,[],[f96,f77])).

fof(f77,plain,
    ( k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f75])).

fof(f96,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f94])).

fof(f97,plain,
    ( spl4_12
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f92,f64,f59,f29,f94])).

fof(f29,plain,
    ( spl4_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f59,plain,
    ( spl4_6
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f64,plain,
    ( spl4_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f92,plain,
    ( sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f91,f61])).

fof(f61,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f59])).

fof(f91,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | sK0 = k1_relset_1(sK0,sK0,sK1)
    | ~ spl4_1
    | ~ spl4_7 ),
    inference(resolution,[],[f53,f66])).

fof(f66,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f64])).

fof(f53,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v1_funct_2(sK1,X0,X0)
        | k1_relset_1(X0,X0,sK1) = X0 )
    | ~ spl4_1 ),
    inference(resolution,[],[f31,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

fof(f31,plain,
    ( v1_funct_1(sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f89,plain,
    ( ~ spl4_7
    | spl4_11 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | ~ spl4_7
    | spl4_11 ),
    inference(resolution,[],[f87,f66])).

fof(f87,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_11 ),
    inference(resolution,[],[f85,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f85,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl4_11
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f86,plain,
    ( spl4_10
    | ~ spl4_11
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f56,f34,f29,f83,f80])).

fof(f34,plain,
    ( spl4_2
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f56,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 )
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f54,f31])).

fof(f54,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK1)
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK1))
        | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0 )
    | ~ spl4_2 ),
    inference(resolution,[],[f36,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).

fof(f36,plain,
    ( v2_funct_1(sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f78,plain,
    ( spl4_9
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f73,f64,f75])).

fof(f73,plain,
    ( k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1)
    | ~ spl4_7 ),
    inference(resolution,[],[f66,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f72,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f17,f69])).

fof(f17,plain,(
    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
         => ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_2)).

fof(f67,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f21,f64])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f62,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f20,f59])).

fof(f20,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f52,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f18,f49])).

fof(f18,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f8])).

fof(f47,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f16,f44])).

fof(f16,plain,(
    r2_hidden(sK3,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f42,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f15,f39])).

fof(f15,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f37,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f22,f34])).

fof(f22,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f32,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f19,f29])).

fof(f19,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:50:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (22764)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.46  % (22764)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f122,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f32,f37,f42,f47,f52,f62,f67,f72,f78,f86,f89,f97,f104,f113,f121])).
% 0.21/0.46  fof(f121,plain,(
% 0.21/0.46    ~spl4_3 | spl4_5 | ~spl4_10 | ~spl4_13 | ~spl4_14),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f120])).
% 0.21/0.46  fof(f120,plain,(
% 0.21/0.46    $false | (~spl4_3 | spl4_5 | ~spl4_10 | ~spl4_13 | ~spl4_14)),
% 0.21/0.46    inference(subsumption_resolution,[],[f119,f41])).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    r2_hidden(sK2,sK0) | ~spl4_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    spl4_3 <=> r2_hidden(sK2,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.46  fof(f119,plain,(
% 0.21/0.46    ~r2_hidden(sK2,sK0) | (spl4_5 | ~spl4_10 | ~spl4_13 | ~spl4_14)),
% 0.21/0.46    inference(subsumption_resolution,[],[f115,f51])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    sK2 != sK3 | spl4_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f49])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    spl4_5 <=> sK2 = sK3),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.46  fof(f115,plain,(
% 0.21/0.46    sK2 = sK3 | ~r2_hidden(sK2,sK0) | (~spl4_10 | ~spl4_13 | ~spl4_14)),
% 0.21/0.46    inference(superposition,[],[f106,f112])).
% 0.21/0.46  fof(f112,plain,(
% 0.21/0.46    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~spl4_14),
% 0.21/0.46    inference(avatar_component_clause,[],[f110])).
% 0.21/0.46  fof(f110,plain,(
% 0.21/0.46    spl4_14 <=> sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.46  fof(f106,plain,(
% 0.21/0.46    ( ! [X1] : (k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X1)) = X1 | ~r2_hidden(X1,sK0)) ) | (~spl4_10 | ~spl4_13)),
% 0.21/0.46    inference(superposition,[],[f81,f101])).
% 0.21/0.46  fof(f101,plain,(
% 0.21/0.46    sK0 = k1_relat_1(sK1) | ~spl4_13),
% 0.21/0.46    inference(avatar_component_clause,[],[f99])).
% 0.21/0.46  fof(f99,plain,(
% 0.21/0.46    spl4_13 <=> sK0 = k1_relat_1(sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.46  fof(f81,plain,(
% 0.21/0.46    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) ) | ~spl4_10),
% 0.21/0.46    inference(avatar_component_clause,[],[f80])).
% 0.21/0.46  fof(f80,plain,(
% 0.21/0.46    spl4_10 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.46  fof(f113,plain,(
% 0.21/0.46    spl4_14 | ~spl4_4 | ~spl4_8 | ~spl4_10 | ~spl4_13),
% 0.21/0.46    inference(avatar_split_clause,[],[f108,f99,f80,f69,f44,f110])).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    spl4_4 <=> r2_hidden(sK3,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    spl4_8 <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.46  fof(f108,plain,(
% 0.21/0.46    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | (~spl4_4 | ~spl4_8 | ~spl4_10 | ~spl4_13)),
% 0.21/0.46    inference(subsumption_resolution,[],[f107,f46])).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    r2_hidden(sK3,sK0) | ~spl4_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f44])).
% 0.21/0.46  fof(f107,plain,(
% 0.21/0.46    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | ~r2_hidden(sK3,sK0) | (~spl4_8 | ~spl4_10 | ~spl4_13)),
% 0.21/0.46    inference(superposition,[],[f106,f71])).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~spl4_8),
% 0.21/0.46    inference(avatar_component_clause,[],[f69])).
% 0.21/0.46  fof(f104,plain,(
% 0.21/0.46    spl4_13 | ~spl4_9 | ~spl4_12),
% 0.21/0.46    inference(avatar_split_clause,[],[f102,f94,f75,f99])).
% 0.21/0.46  fof(f75,plain,(
% 0.21/0.46    spl4_9 <=> k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.46  fof(f94,plain,(
% 0.21/0.46    spl4_12 <=> sK0 = k1_relset_1(sK0,sK0,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.46  fof(f102,plain,(
% 0.21/0.46    sK0 = k1_relat_1(sK1) | (~spl4_9 | ~spl4_12)),
% 0.21/0.46    inference(superposition,[],[f96,f77])).
% 0.21/0.46  fof(f77,plain,(
% 0.21/0.46    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1) | ~spl4_9),
% 0.21/0.46    inference(avatar_component_clause,[],[f75])).
% 0.21/0.46  fof(f96,plain,(
% 0.21/0.46    sK0 = k1_relset_1(sK0,sK0,sK1) | ~spl4_12),
% 0.21/0.46    inference(avatar_component_clause,[],[f94])).
% 0.21/0.46  fof(f97,plain,(
% 0.21/0.46    spl4_12 | ~spl4_1 | ~spl4_6 | ~spl4_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f92,f64,f59,f29,f94])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    spl4_1 <=> v1_funct_1(sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    spl4_6 <=> v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    spl4_7 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.46  fof(f92,plain,(
% 0.21/0.46    sK0 = k1_relset_1(sK0,sK0,sK1) | (~spl4_1 | ~spl4_6 | ~spl4_7)),
% 0.21/0.46    inference(subsumption_resolution,[],[f91,f61])).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    v1_funct_2(sK1,sK0,sK0) | ~spl4_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f59])).
% 0.21/0.46  fof(f91,plain,(
% 0.21/0.46    ~v1_funct_2(sK1,sK0,sK0) | sK0 = k1_relset_1(sK0,sK0,sK1) | (~spl4_1 | ~spl4_7)),
% 0.21/0.46    inference(resolution,[],[f53,f66])).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f64])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(sK1,X0,X0) | k1_relset_1(X0,X0,sK1) = X0) ) | ~spl4_1),
% 0.21/0.46    inference(resolution,[],[f31,f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_funct_2(X1,X0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | k1_relset_1(X0,X0,X1) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 0.21/0.46    inference(flattening,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    v1_funct_1(sK1) | ~spl4_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f29])).
% 0.21/0.46  fof(f89,plain,(
% 0.21/0.46    ~spl4_7 | spl4_11),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f88])).
% 0.21/0.46  fof(f88,plain,(
% 0.21/0.46    $false | (~spl4_7 | spl4_11)),
% 0.21/0.46    inference(resolution,[],[f87,f66])).
% 0.21/0.46  fof(f87,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl4_11),
% 0.21/0.46    inference(resolution,[],[f85,f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.46  fof(f85,plain,(
% 0.21/0.46    ~v1_relat_1(sK1) | spl4_11),
% 0.21/0.46    inference(avatar_component_clause,[],[f83])).
% 0.21/0.46  fof(f83,plain,(
% 0.21/0.46    spl4_11 <=> v1_relat_1(sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.46  fof(f86,plain,(
% 0.21/0.46    spl4_10 | ~spl4_11 | ~spl4_1 | ~spl4_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f56,f34,f29,f83,f80])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    spl4_2 <=> v2_funct_1(sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_relat_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) ) | (~spl4_1 | ~spl4_2)),
% 0.21/0.46    inference(subsumption_resolution,[],[f54,f31])).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,X0)) = X0) ) | ~spl4_2),
% 0.21/0.46    inference(resolution,[],[f36,f23])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(flattening,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_funct_1)).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    v2_funct_1(sK1) | ~spl4_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f34])).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    spl4_9 | ~spl4_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f73,f64,f75])).
% 0.21/0.46  fof(f73,plain,(
% 0.21/0.46    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1) | ~spl4_7),
% 0.21/0.46    inference(resolution,[],[f66,f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.46  fof(f72,plain,(
% 0.21/0.46    spl4_8),
% 0.21/0.46    inference(avatar_split_clause,[],[f17,f69])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ? [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.21/0.46    inference(flattening,[],[f7])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & (k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0))) & v2_funct_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.21/0.46    inference(negated_conjecture,[],[f5])).
% 0.21/0.46  fof(f5,conjecture,(
% 0.21/0.46    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) => ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_funct_2)).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    spl4_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f21,f64])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    spl4_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f20,f59])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    v1_funct_2(sK1,sK0,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f52,plain,(
% 0.21/0.46    ~spl4_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f18,f49])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    sK2 != sK3),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f47,plain,(
% 0.21/0.46    spl4_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f16,f44])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    r2_hidden(sK3,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    spl4_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f15,f39])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    r2_hidden(sK2,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    spl4_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f22,f34])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    v2_funct_1(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    spl4_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f19,f29])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    v1_funct_1(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (22764)------------------------------
% 0.21/0.46  % (22764)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (22764)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (22764)Memory used [KB]: 10618
% 0.21/0.46  % (22764)Time elapsed: 0.011 s
% 0.21/0.46  % (22764)------------------------------
% 0.21/0.46  % (22764)------------------------------
% 0.21/0.47  % (22756)Success in time 0.106 s
%------------------------------------------------------------------------------
