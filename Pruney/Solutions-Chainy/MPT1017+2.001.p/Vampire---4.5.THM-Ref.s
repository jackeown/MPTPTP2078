%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:34 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 126 expanded)
%              Number of leaves         :   15 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :  218 ( 518 expanded)
%              Number of equality atoms :   18 (  49 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f87,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f41,f49,f53,f57,f69,f73,f77,f81,f86])).

fof(f86,plain,
    ( ~ spl2_7
    | ~ spl2_8
    | spl2_9
    | ~ spl2_10 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | ~ spl2_7
    | ~ spl2_8
    | spl2_9
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f84,f76])).

fof(f76,plain,
    ( ~ v2_funct_2(sK1,sK0)
    | spl2_9 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl2_9
  <=> v2_funct_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f84,plain,
    ( v2_funct_2(sK1,sK0)
    | ~ spl2_7
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f83,f68])).

fof(f68,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl2_7
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f83,plain,
    ( ~ v1_relat_1(sK1)
    | v2_funct_2(sK1,sK0)
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(subsumption_resolution,[],[f82,f72])).

fof(f72,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl2_8
  <=> v5_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f82,plain,
    ( ~ v5_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | v2_funct_2(sK1,sK0)
    | ~ spl2_10 ),
    inference(superposition,[],[f30,f80])).

fof(f80,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl2_10
  <=> sK0 = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f30,plain,(
    ! [X1] :
      ( ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | v2_funct_2(X1,k2_relat_1(X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | k2_relat_1(X1) != X0
      | v2_funct_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f81,plain,
    ( spl2_10
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f62,f55,f51,f79])).

fof(f51,plain,
    ( spl2_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f55,plain,
    ( spl2_6
  <=> sK0 = k2_relset_1(sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f62,plain,
    ( sK0 = k2_relat_1(sK1)
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f60,f56])).

fof(f56,plain,
    ( sK0 = k2_relset_1(sK0,sK0,sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f55])).

fof(f60,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1)
    | ~ spl2_5 ),
    inference(resolution,[],[f52,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f52,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f77,plain,
    ( ~ spl2_9
    | ~ spl2_1
    | ~ spl2_2
    | spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f65,f51,f47,f39,f35,f75])).

fof(f35,plain,
    ( spl2_1
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f39,plain,
    ( spl2_2
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f47,plain,
    ( spl2_4
  <=> v3_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f65,plain,
    ( ~ v2_funct_2(sK1,sK0)
    | ~ spl2_1
    | ~ spl2_2
    | spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f64,f48])).

fof(f48,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f64,plain,
    ( ~ v2_funct_2(sK1,sK0)
    | v3_funct_2(sK1,sK0,sK0)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f63,f40])).

fof(f40,plain,
    ( v2_funct_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f63,plain,
    ( ~ v2_funct_1(sK1)
    | ~ v2_funct_2(sK1,sK0)
    | v3_funct_2(sK1,sK0,sK0)
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f61,f36])).

fof(f36,plain,
    ( v1_funct_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f61,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v2_funct_2(sK1,sK0)
    | v3_funct_2(sK1,sK0,sK0)
    | ~ spl2_5 ),
    inference(resolution,[],[f52,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | ~ v2_funct_2(X2,X1)
      | v3_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( v3_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v2_funct_2(X2,X1)
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( v3_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v2_funct_2(X2,X1)
      | ~ v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) )
       => ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_funct_2)).

fof(f73,plain,
    ( spl2_8
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f59,f51,f71])).

fof(f59,plain,
    ( v5_relat_1(sK1,sK0)
    | ~ spl2_5 ),
    inference(resolution,[],[f52,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f69,plain,
    ( spl2_7
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f58,f51,f67])).

fof(f58,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_5 ),
    inference(resolution,[],[f52,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f57,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f23,f55])).

fof(f23,plain,(
    sK0 = k2_relset_1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v3_funct_2(X1,X0,X0)
        | ~ v1_funct_2(X1,X0,X0)
        | ~ v1_funct_1(X1) )
      & k2_relset_1(X0,X0,X1) = X0
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        | ~ v3_funct_2(X1,X0,X0)
        | ~ v1_funct_2(X1,X0,X0)
        | ~ v1_funct_1(X1) )
      & k2_relset_1(X0,X0,X1) = X0
      & v2_funct_1(X1)
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( ( k2_relset_1(X0,X0,X1) = X0
            & v2_funct_1(X1) )
         => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v3_funct_2(X1,X0,X0)
            & v1_funct_2(X1,X0,X0)
            & v1_funct_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( ( k2_relset_1(X0,X0,X1) = X0
          & v2_funct_1(X1) )
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X1,X0,X0)
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_funct_2)).

fof(f53,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f21,f51])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f49,plain,(
    ~ spl2_4 ),
    inference(avatar_split_clause,[],[f33,f47])).

fof(f33,plain,(
    ~ v3_funct_2(sK1,sK0,sK0) ),
    inference(subsumption_resolution,[],[f32,f21])).

fof(f32,plain,
    ( ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f31,f20])).

fof(f20,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f31,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f18,f19])).

fof(f19,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f18,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v3_funct_2(sK1,sK0,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f41,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f22,f39])).

fof(f22,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f37,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f19,f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:45:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.45  % (5384)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.19/0.45  % (5384)Refutation found. Thanks to Tanya!
% 0.19/0.45  % SZS status Theorem for theBenchmark
% 0.19/0.46  % (5397)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.19/0.46  % SZS output start Proof for theBenchmark
% 0.19/0.46  fof(f87,plain,(
% 0.19/0.46    $false),
% 0.19/0.46    inference(avatar_sat_refutation,[],[f37,f41,f49,f53,f57,f69,f73,f77,f81,f86])).
% 0.19/0.46  fof(f86,plain,(
% 0.19/0.46    ~spl2_7 | ~spl2_8 | spl2_9 | ~spl2_10),
% 0.19/0.46    inference(avatar_contradiction_clause,[],[f85])).
% 0.19/0.46  fof(f85,plain,(
% 0.19/0.46    $false | (~spl2_7 | ~spl2_8 | spl2_9 | ~spl2_10)),
% 0.19/0.46    inference(subsumption_resolution,[],[f84,f76])).
% 0.19/0.46  fof(f76,plain,(
% 0.19/0.46    ~v2_funct_2(sK1,sK0) | spl2_9),
% 0.19/0.46    inference(avatar_component_clause,[],[f75])).
% 0.19/0.46  fof(f75,plain,(
% 0.19/0.46    spl2_9 <=> v2_funct_2(sK1,sK0)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.19/0.46  fof(f84,plain,(
% 0.19/0.46    v2_funct_2(sK1,sK0) | (~spl2_7 | ~spl2_8 | ~spl2_10)),
% 0.19/0.46    inference(subsumption_resolution,[],[f83,f68])).
% 0.19/0.46  fof(f68,plain,(
% 0.19/0.46    v1_relat_1(sK1) | ~spl2_7),
% 0.19/0.46    inference(avatar_component_clause,[],[f67])).
% 0.19/0.46  fof(f67,plain,(
% 0.19/0.46    spl2_7 <=> v1_relat_1(sK1)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.19/0.46  fof(f83,plain,(
% 0.19/0.46    ~v1_relat_1(sK1) | v2_funct_2(sK1,sK0) | (~spl2_8 | ~spl2_10)),
% 0.19/0.46    inference(subsumption_resolution,[],[f82,f72])).
% 0.19/0.46  fof(f72,plain,(
% 0.19/0.46    v5_relat_1(sK1,sK0) | ~spl2_8),
% 0.19/0.46    inference(avatar_component_clause,[],[f71])).
% 0.19/0.46  fof(f71,plain,(
% 0.19/0.46    spl2_8 <=> v5_relat_1(sK1,sK0)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.19/0.46  fof(f82,plain,(
% 0.19/0.46    ~v5_relat_1(sK1,sK0) | ~v1_relat_1(sK1) | v2_funct_2(sK1,sK0) | ~spl2_10),
% 0.19/0.46    inference(superposition,[],[f30,f80])).
% 0.19/0.46  fof(f80,plain,(
% 0.19/0.46    sK0 = k2_relat_1(sK1) | ~spl2_10),
% 0.19/0.46    inference(avatar_component_clause,[],[f79])).
% 0.19/0.46  fof(f79,plain,(
% 0.19/0.46    spl2_10 <=> sK0 = k2_relat_1(sK1)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.19/0.46  fof(f30,plain,(
% 0.19/0.46    ( ! [X1] : (~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1) | v2_funct_2(X1,k2_relat_1(X1))) )),
% 0.19/0.46    inference(equality_resolution,[],[f26])).
% 0.19/0.46  fof(f26,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | k2_relat_1(X1) != X0 | v2_funct_2(X1,X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f15])).
% 0.19/0.46  fof(f15,plain,(
% 0.19/0.46    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.19/0.46    inference(flattening,[],[f14])).
% 0.19/0.46  fof(f14,plain,(
% 0.19/0.46    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.19/0.46    inference(ennf_transformation,[],[f5])).
% 0.19/0.46  fof(f5,axiom,(
% 0.19/0.46    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 0.19/0.46  fof(f81,plain,(
% 0.19/0.46    spl2_10 | ~spl2_5 | ~spl2_6),
% 0.19/0.46    inference(avatar_split_clause,[],[f62,f55,f51,f79])).
% 0.19/0.46  fof(f51,plain,(
% 0.19/0.46    spl2_5 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.19/0.46  fof(f55,plain,(
% 0.19/0.46    spl2_6 <=> sK0 = k2_relset_1(sK0,sK0,sK1)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.19/0.46  fof(f62,plain,(
% 0.19/0.46    sK0 = k2_relat_1(sK1) | (~spl2_5 | ~spl2_6)),
% 0.19/0.46    inference(forward_demodulation,[],[f60,f56])).
% 0.19/0.46  fof(f56,plain,(
% 0.19/0.46    sK0 = k2_relset_1(sK0,sK0,sK1) | ~spl2_6),
% 0.19/0.46    inference(avatar_component_clause,[],[f55])).
% 0.19/0.46  fof(f60,plain,(
% 0.19/0.46    k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) | ~spl2_5),
% 0.19/0.46    inference(resolution,[],[f52,f25])).
% 0.19/0.46  fof(f25,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f13])).
% 0.19/0.46  fof(f13,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.46    inference(ennf_transformation,[],[f3])).
% 0.19/0.46  fof(f3,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.19/0.46  fof(f52,plain,(
% 0.19/0.46    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl2_5),
% 0.19/0.46    inference(avatar_component_clause,[],[f51])).
% 0.19/0.46  fof(f77,plain,(
% 0.19/0.46    ~spl2_9 | ~spl2_1 | ~spl2_2 | spl2_4 | ~spl2_5),
% 0.19/0.46    inference(avatar_split_clause,[],[f65,f51,f47,f39,f35,f75])).
% 0.19/0.46  fof(f35,plain,(
% 0.19/0.46    spl2_1 <=> v1_funct_1(sK1)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.19/0.46  fof(f39,plain,(
% 0.19/0.46    spl2_2 <=> v2_funct_1(sK1)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.19/0.46  fof(f47,plain,(
% 0.19/0.46    spl2_4 <=> v3_funct_2(sK1,sK0,sK0)),
% 0.19/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.19/0.46  fof(f65,plain,(
% 0.19/0.46    ~v2_funct_2(sK1,sK0) | (~spl2_1 | ~spl2_2 | spl2_4 | ~spl2_5)),
% 0.19/0.46    inference(subsumption_resolution,[],[f64,f48])).
% 0.19/0.46  fof(f48,plain,(
% 0.19/0.46    ~v3_funct_2(sK1,sK0,sK0) | spl2_4),
% 0.19/0.46    inference(avatar_component_clause,[],[f47])).
% 0.19/0.46  fof(f64,plain,(
% 0.19/0.46    ~v2_funct_2(sK1,sK0) | v3_funct_2(sK1,sK0,sK0) | (~spl2_1 | ~spl2_2 | ~spl2_5)),
% 0.19/0.46    inference(subsumption_resolution,[],[f63,f40])).
% 0.19/0.46  fof(f40,plain,(
% 0.19/0.46    v2_funct_1(sK1) | ~spl2_2),
% 0.19/0.46    inference(avatar_component_clause,[],[f39])).
% 0.19/0.46  fof(f63,plain,(
% 0.19/0.46    ~v2_funct_1(sK1) | ~v2_funct_2(sK1,sK0) | v3_funct_2(sK1,sK0,sK0) | (~spl2_1 | ~spl2_5)),
% 0.19/0.46    inference(subsumption_resolution,[],[f61,f36])).
% 0.19/0.46  fof(f36,plain,(
% 0.19/0.46    v1_funct_1(sK1) | ~spl2_1),
% 0.19/0.46    inference(avatar_component_clause,[],[f35])).
% 0.19/0.46  fof(f61,plain,(
% 0.19/0.46    ~v1_funct_1(sK1) | ~v2_funct_1(sK1) | ~v2_funct_2(sK1,sK0) | v3_funct_2(sK1,sK0,sK0) | ~spl2_5),
% 0.19/0.46    inference(resolution,[],[f52,f24])).
% 0.19/0.46  fof(f24,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | ~v2_funct_2(X2,X1) | v3_funct_2(X2,X0,X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f12])).
% 0.19/0.46  fof(f12,plain,(
% 0.19/0.46    ! [X0,X1,X2] : ((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v2_funct_2(X2,X1) | ~v2_funct_1(X2) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.46    inference(flattening,[],[f11])).
% 0.19/0.46  fof(f11,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (((v3_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v2_funct_2(X2,X1) | ~v2_funct_1(X2) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.46    inference(ennf_transformation,[],[f4])).
% 0.19/0.46  fof(f4,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v2_funct_2(X2,X1) & v2_funct_1(X2) & v1_funct_1(X2)) => (v3_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_funct_2)).
% 0.19/0.46  fof(f73,plain,(
% 0.19/0.46    spl2_8 | ~spl2_5),
% 0.19/0.46    inference(avatar_split_clause,[],[f59,f51,f71])).
% 0.19/0.46  fof(f59,plain,(
% 0.19/0.46    v5_relat_1(sK1,sK0) | ~spl2_5),
% 0.19/0.46    inference(resolution,[],[f52,f28])).
% 0.19/0.46  fof(f28,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f16])).
% 0.19/0.46  fof(f16,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.46    inference(ennf_transformation,[],[f8])).
% 0.19/0.46  fof(f8,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.19/0.46    inference(pure_predicate_removal,[],[f2])).
% 0.19/0.46  fof(f2,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.19/0.46  fof(f69,plain,(
% 0.19/0.46    spl2_7 | ~spl2_5),
% 0.19/0.46    inference(avatar_split_clause,[],[f58,f51,f67])).
% 0.19/0.46  fof(f58,plain,(
% 0.19/0.46    v1_relat_1(sK1) | ~spl2_5),
% 0.19/0.46    inference(resolution,[],[f52,f29])).
% 0.19/0.46  fof(f29,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f17])).
% 0.19/0.46  fof(f17,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.46    inference(ennf_transformation,[],[f1])).
% 0.19/0.46  fof(f1,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.19/0.46  fof(f57,plain,(
% 0.19/0.46    spl2_6),
% 0.19/0.46    inference(avatar_split_clause,[],[f23,f55])).
% 0.19/0.46  fof(f23,plain,(
% 0.19/0.46    sK0 = k2_relset_1(sK0,sK0,sK1)),
% 0.19/0.46    inference(cnf_transformation,[],[f10])).
% 0.19/0.46  fof(f10,plain,(
% 0.19/0.46    ? [X0,X1] : ((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) & k2_relset_1(X0,X0,X1) = X0 & v2_funct_1(X1) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.19/0.46    inference(flattening,[],[f9])).
% 0.19/0.46  fof(f9,plain,(
% 0.19/0.46    ? [X0,X1] : (((~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v3_funct_2(X1,X0,X0) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) & (k2_relset_1(X0,X0,X1) = X0 & v2_funct_1(X1))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.19/0.46    inference(ennf_transformation,[],[f7])).
% 0.19/0.46  fof(f7,negated_conjecture,(
% 0.19/0.46    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((k2_relset_1(X0,X0,X1) = X0 & v2_funct_1(X1)) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))))),
% 0.19/0.46    inference(negated_conjecture,[],[f6])).
% 0.19/0.46  fof(f6,conjecture,(
% 0.19/0.46    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((k2_relset_1(X0,X0,X1) = X0 & v2_funct_1(X1)) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v3_funct_2(X1,X0,X0) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_funct_2)).
% 0.19/0.46  fof(f53,plain,(
% 0.19/0.46    spl2_5),
% 0.19/0.46    inference(avatar_split_clause,[],[f21,f51])).
% 0.19/0.46  fof(f21,plain,(
% 0.19/0.46    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.46    inference(cnf_transformation,[],[f10])).
% 0.19/0.46  fof(f49,plain,(
% 0.19/0.46    ~spl2_4),
% 0.19/0.46    inference(avatar_split_clause,[],[f33,f47])).
% 0.19/0.46  fof(f33,plain,(
% 0.19/0.46    ~v3_funct_2(sK1,sK0,sK0)),
% 0.19/0.46    inference(subsumption_resolution,[],[f32,f21])).
% 0.19/0.46  fof(f32,plain,(
% 0.19/0.46    ~v3_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.46    inference(subsumption_resolution,[],[f31,f20])).
% 0.19/0.46  fof(f20,plain,(
% 0.19/0.46    v1_funct_2(sK1,sK0,sK0)),
% 0.19/0.46    inference(cnf_transformation,[],[f10])).
% 0.19/0.46  fof(f31,plain,(
% 0.19/0.46    ~v1_funct_2(sK1,sK0,sK0) | ~v3_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.46    inference(subsumption_resolution,[],[f18,f19])).
% 0.19/0.46  fof(f19,plain,(
% 0.19/0.46    v1_funct_1(sK1)),
% 0.19/0.46    inference(cnf_transformation,[],[f10])).
% 0.19/0.46  fof(f18,plain,(
% 0.19/0.46    ~v1_funct_1(sK1) | ~v1_funct_2(sK1,sK0,sK0) | ~v3_funct_2(sK1,sK0,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.19/0.46    inference(cnf_transformation,[],[f10])).
% 0.19/0.46  fof(f41,plain,(
% 0.19/0.46    spl2_2),
% 0.19/0.46    inference(avatar_split_clause,[],[f22,f39])).
% 0.19/0.46  fof(f22,plain,(
% 0.19/0.46    v2_funct_1(sK1)),
% 0.19/0.46    inference(cnf_transformation,[],[f10])).
% 0.19/0.46  fof(f37,plain,(
% 0.19/0.46    spl2_1),
% 0.19/0.46    inference(avatar_split_clause,[],[f19,f35])).
% 0.19/0.46  % SZS output end Proof for theBenchmark
% 0.19/0.46  % (5384)------------------------------
% 0.19/0.46  % (5384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (5384)Termination reason: Refutation
% 0.19/0.46  
% 0.19/0.46  % (5384)Memory used [KB]: 6140
% 0.19/0.46  % (5384)Time elapsed: 0.051 s
% 0.19/0.46  % (5384)------------------------------
% 0.19/0.46  % (5384)------------------------------
% 0.19/0.46  % (5383)Success in time 0.115 s
%------------------------------------------------------------------------------
