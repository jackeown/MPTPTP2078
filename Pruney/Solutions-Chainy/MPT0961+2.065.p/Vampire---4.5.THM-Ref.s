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
% DateTime   : Thu Dec  3 13:00:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 125 expanded)
%              Number of leaves         :   15 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :  206 ( 350 expanded)
%              Number of equality atoms :   55 (  93 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f156,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f62,f69,f80,f85,f131,f133,f143,f155])).

fof(f155,plain,
    ( spl2_13
    | ~ spl2_15 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl2_13
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f153,f152])).

fof(f152,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl2_13
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f145,f130])).

fof(f130,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl2_13 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl2_13
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f145,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl2_15 ),
    inference(resolution,[],[f142,f43])).

fof(f43,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f142,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl2_15
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f153,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f148,f34])).

fof(f34,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f148,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl2_15 ),
    inference(resolution,[],[f142,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f143,plain,
    ( spl2_15
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f111,f71,f64,f141])).

fof(f64,plain,
    ( spl2_4
  <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f71,plain,
    ( spl2_6
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f111,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f110,f34])).

fof(f110,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0)))
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f103,f35])).

fof(f35,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f103,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))))
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(superposition,[],[f84,f72])).

fof(f72,plain,
    ( k1_xboole_0 = sK0
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f84,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f133,plain,
    ( spl2_8
    | ~ spl2_4
    | spl2_5 ),
    inference(avatar_split_clause,[],[f97,f67,f64,f78])).

fof(f78,plain,
    ( spl2_8
  <=> k1_xboole_0 = k2_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f67,plain,
    ( spl2_5
  <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f97,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | ~ spl2_4
    | spl2_5 ),
    inference(subsumption_resolution,[],[f96,f68])).

fof(f68,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f96,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f87,f86])).

fof(f86,plain,
    ( k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f84,f40])).

fof(f87,plain,
    ( k1_xboole_0 = k2_relat_1(sK0)
    | k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0)
    | v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ spl2_4 ),
    inference(resolution,[],[f84,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f131,plain,
    ( ~ spl2_13
    | spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f107,f71,f67,f129])).

fof(f107,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl2_5
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f106,f34])).

fof(f106,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | spl2_5
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f101,f35])).

fof(f101,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))
    | spl2_5
    | ~ spl2_6 ),
    inference(superposition,[],[f68,f72])).

fof(f85,plain,
    ( spl2_4
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f81,f60,f64])).

fof(f60,plain,
    ( spl2_3
  <=> r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f81,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))
    | ~ spl2_3 ),
    inference(resolution,[],[f61,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f61,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f80,plain,
    ( spl2_6
    | ~ spl2_8
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f58,f49,f78,f71])).

fof(f49,plain,
    ( spl2_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f58,plain,
    ( k1_xboole_0 != k2_relat_1(sK0)
    | k1_xboole_0 = sK0
    | ~ spl2_1 ),
    inference(resolution,[],[f50,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) != k1_xboole_0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k2_relat_1(X0) != k1_xboole_0
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k2_relat_1(X0) != k1_xboole_0
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k2_relat_1(X0) = k1_xboole_0
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f50,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f69,plain,
    ( ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f47,f67,f64])).

fof(f47,plain,
    ( ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    inference(subsumption_resolution,[],[f22,f24])).

fof(f24,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
          & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
          & v1_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f22,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) ),
    inference(cnf_transformation,[],[f14])).

fof(f62,plain,
    ( spl2_3
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f56,f49,f60])).

fof(f56,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl2_1 ),
    inference(resolution,[],[f50,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f51,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f23,f49])).

fof(f23,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:59:03 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (32111)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.48  % (32119)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.48  % (32103)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (32103)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f156,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f51,f62,f69,f80,f85,f131,f133,f143,f155])).
% 0.22/0.48  fof(f155,plain,(
% 0.22/0.48    spl2_13 | ~spl2_15),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f154])).
% 0.22/0.48  fof(f154,plain,(
% 0.22/0.48    $false | (spl2_13 | ~spl2_15)),
% 0.22/0.48    inference(subsumption_resolution,[],[f153,f152])).
% 0.22/0.48  fof(f152,plain,(
% 0.22/0.48    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl2_13 | ~spl2_15)),
% 0.22/0.48    inference(subsumption_resolution,[],[f145,f130])).
% 0.22/0.48  fof(f130,plain,(
% 0.22/0.48    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | spl2_13),
% 0.22/0.48    inference(avatar_component_clause,[],[f129])).
% 0.22/0.48  fof(f129,plain,(
% 0.22/0.48    spl2_13 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.48  fof(f145,plain,(
% 0.22/0.48    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl2_15),
% 0.22/0.48    inference(resolution,[],[f142,f43])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.22/0.48    inference(equality_resolution,[],[f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(flattening,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.48  fof(f142,plain,(
% 0.22/0.48    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl2_15),
% 0.22/0.48    inference(avatar_component_clause,[],[f141])).
% 0.22/0.48  fof(f141,plain,(
% 0.22/0.48    spl2_15 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.48  fof(f153,plain,(
% 0.22/0.48    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl2_15),
% 0.22/0.48    inference(forward_demodulation,[],[f148,f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.22/0.48  fof(f148,plain,(
% 0.22/0.48    k1_relat_1(k1_xboole_0) = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl2_15),
% 0.22/0.48    inference(resolution,[],[f142,f40])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.48  fof(f143,plain,(
% 0.22/0.48    spl2_15 | ~spl2_4 | ~spl2_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f111,f71,f64,f141])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    spl2_4 <=> m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    spl2_6 <=> k1_xboole_0 = sK0),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.48  fof(f111,plain,(
% 0.22/0.48    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl2_4 | ~spl2_6)),
% 0.22/0.48    inference(forward_demodulation,[],[f110,f34])).
% 0.22/0.48  fof(f110,plain,(
% 0.22/0.48    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k1_xboole_0))) | (~spl2_4 | ~spl2_6)),
% 0.22/0.48    inference(forward_demodulation,[],[f103,f35])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f103,plain,(
% 0.22/0.48    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)))) | (~spl2_4 | ~spl2_6)),
% 0.22/0.48    inference(superposition,[],[f84,f72])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    k1_xboole_0 = sK0 | ~spl2_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f71])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~spl2_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f64])).
% 0.22/0.48  fof(f133,plain,(
% 0.22/0.48    spl2_8 | ~spl2_4 | spl2_5),
% 0.22/0.48    inference(avatar_split_clause,[],[f97,f67,f64,f78])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    spl2_8 <=> k1_xboole_0 = k2_relat_1(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    spl2_5 <=> v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.48  fof(f97,plain,(
% 0.22/0.48    k1_xboole_0 = k2_relat_1(sK0) | (~spl2_4 | spl2_5)),
% 0.22/0.48    inference(subsumption_resolution,[],[f96,f68])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | spl2_5),
% 0.22/0.48    inference(avatar_component_clause,[],[f67])).
% 0.22/0.48  fof(f96,plain,(
% 0.22/0.48    k1_xboole_0 = k2_relat_1(sK0) | v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~spl2_4),
% 0.22/0.48    inference(subsumption_resolution,[],[f87,f86])).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    k1_relat_1(sK0) = k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) | ~spl2_4),
% 0.22/0.48    inference(resolution,[],[f84,f40])).
% 0.22/0.48  fof(f87,plain,(
% 0.22/0.48    k1_xboole_0 = k2_relat_1(sK0) | k1_relat_1(sK0) != k1_relset_1(k1_relat_1(sK0),k2_relat_1(sK0),sK0) | v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~spl2_4),
% 0.22/0.48    inference(resolution,[],[f84,f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f131,plain,(
% 0.22/0.48    ~spl2_13 | spl2_5 | ~spl2_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f107,f71,f67,f129])).
% 0.22/0.48  fof(f107,plain,(
% 0.22/0.48    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl2_5 | ~spl2_6)),
% 0.22/0.48    inference(forward_demodulation,[],[f106,f34])).
% 0.22/0.48  fof(f106,plain,(
% 0.22/0.48    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (spl2_5 | ~spl2_6)),
% 0.22/0.48    inference(forward_demodulation,[],[f101,f35])).
% 0.22/0.48  fof(f101,plain,(
% 0.22/0.48    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)) | (spl2_5 | ~spl2_6)),
% 0.22/0.48    inference(superposition,[],[f68,f72])).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    spl2_4 | ~spl2_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f81,f60,f64])).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    spl2_3 <=> r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) | ~spl2_3),
% 0.22/0.48    inference(resolution,[],[f61,f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.48    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | ~spl2_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f60])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    spl2_6 | ~spl2_8 | ~spl2_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f58,f49,f78,f71])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    spl2_1 <=> v1_relat_1(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    k1_xboole_0 != k2_relat_1(sK0) | k1_xboole_0 = sK0 | ~spl2_1),
% 0.22/0.48    inference(resolution,[],[f50,f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0] : (k1_xboole_0 = X0 | (k2_relat_1(X0) != k1_xboole_0 & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : ((k1_xboole_0 = X0 | (k2_relat_1(X0) != k1_xboole_0 & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ((k2_relat_1(X0) = k1_xboole_0 | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    v1_relat_1(sK0) | ~spl2_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f49])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    ~spl2_4 | ~spl2_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f47,f67,f64])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.22/0.49    inference(subsumption_resolution,[],[f22,f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    v1_funct_1(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ? [X0] : ((~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.22/0.49    inference(negated_conjecture,[],[f8])).
% 0.22/0.49  fof(f8,conjecture,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ~v1_funct_1(sK0) | ~v1_funct_2(sK0,k1_relat_1(sK0),k2_relat_1(sK0)) | ~m1_subset_1(sK0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))))),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    spl2_3 | ~spl2_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f56,f49,f60])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | ~spl2_1),
% 0.22/0.49    inference(resolution,[],[f50,f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    spl2_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f23,f49])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    v1_relat_1(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (32103)------------------------------
% 0.22/0.49  % (32103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (32103)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (32103)Memory used [KB]: 6140
% 0.22/0.49  % (32103)Time elapsed: 0.070 s
% 0.22/0.49  % (32103)------------------------------
% 0.22/0.49  % (32103)------------------------------
% 0.22/0.49  % (32102)Success in time 0.122 s
%------------------------------------------------------------------------------
