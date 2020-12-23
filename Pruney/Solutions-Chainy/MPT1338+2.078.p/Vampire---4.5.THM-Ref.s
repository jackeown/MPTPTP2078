%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  206 ( 445 expanded)
%              Number of leaves         :   44 ( 186 expanded)
%              Depth                    :   11
%              Number of atoms          :  668 (1465 expanded)
%              Number of equality atoms :  113 ( 308 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f418,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f68,f72,f76,f80,f90,f94,f100,f104,f111,f115,f121,f151,f155,f165,f175,f189,f196,f200,f210,f222,f230,f235,f253,f285,f324,f353,f372,f376,f396,f417])).

fof(f417,plain,
    ( ~ spl3_6
    | ~ spl3_8
    | ~ spl3_16
    | spl3_22
    | ~ spl3_28
    | ~ spl3_31
    | ~ spl3_48
    | ~ spl3_53 ),
    inference(avatar_contradiction_clause,[],[f416])).

fof(f416,plain,
    ( $false
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_16
    | spl3_22
    | ~ spl3_28
    | ~ spl3_31
    | ~ spl3_48
    | ~ spl3_53 ),
    inference(subsumption_resolution,[],[f415,f387])).

fof(f387,plain,
    ( k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_28
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f378,f221])).

fof(f221,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl3_28
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f378,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_53 ),
    inference(resolution,[],[f371,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f371,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_53 ),
    inference(avatar_component_clause,[],[f370])).

fof(f370,plain,
    ( spl3_53
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f415,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_16
    | spl3_22
    | ~ spl3_31
    | ~ spl3_48 ),
    inference(forward_demodulation,[],[f414,f348])).

fof(f348,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f347])).

fof(f347,plain,
    ( spl3_48
  <=> k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f414,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_16
    | spl3_22
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f413,f234])).

fof(f234,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl3_31
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f413,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_16
    | spl3_22 ),
    inference(forward_demodulation,[],[f412,f99])).

fof(f99,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl3_8
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f412,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2))
    | ~ spl3_6
    | ~ spl3_16
    | spl3_22 ),
    inference(forward_demodulation,[],[f411,f164])).

fof(f164,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl3_16
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f411,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_6
    | spl3_22 ),
    inference(forward_demodulation,[],[f188,f89])).

fof(f89,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl3_6
  <=> k2_struct_0(sK1) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f188,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | spl3_22 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl3_22
  <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f396,plain,
    ( ~ spl3_25
    | ~ spl3_48
    | ~ spl3_53
    | spl3_54 ),
    inference(avatar_contradiction_clause,[],[f395])).

fof(f395,plain,
    ( $false
    | ~ spl3_25
    | ~ spl3_48
    | ~ spl3_53
    | spl3_54 ),
    inference(subsumption_resolution,[],[f394,f377])).

fof(f377,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_48
    | spl3_54 ),
    inference(forward_demodulation,[],[f375,f348])).

fof(f375,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | spl3_54 ),
    inference(avatar_component_clause,[],[f374])).

fof(f374,plain,
    ( spl3_54
  <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f394,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_25
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f383,f209])).

fof(f209,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl3_25
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f383,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_53 ),
    inference(resolution,[],[f371,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f376,plain,
    ( ~ spl3_54
    | spl3_23
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f245,f233,f194,f374])).

fof(f194,plain,
    ( spl3_23
  <=> k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f245,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | spl3_23
    | ~ spl3_31 ),
    inference(superposition,[],[f195,f234])).

fof(f195,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | spl3_23 ),
    inference(avatar_component_clause,[],[f194])).

fof(f372,plain,
    ( spl3_53
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_33
    | ~ spl3_34
    | ~ spl3_40 ),
    inference(avatar_split_clause,[],[f313,f283,f251,f240,f66,f62,f370])).

fof(f62,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f66,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f240,plain,
    ( spl3_33
  <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f251,plain,
    ( spl3_34
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f283,plain,
    ( spl3_40
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f313,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_33
    | ~ spl3_34
    | ~ spl3_40 ),
    inference(forward_demodulation,[],[f312,f307])).

fof(f307,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_33
    | ~ spl3_34
    | ~ spl3_40 ),
    inference(subsumption_resolution,[],[f306,f67])).

fof(f67,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f306,plain,
    ( ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_1
    | ~ spl3_33
    | ~ spl3_34
    | ~ spl3_40 ),
    inference(subsumption_resolution,[],[f305,f241])).

fof(f241,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f240])).

fof(f305,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_1
    | ~ spl3_34
    | ~ spl3_40 ),
    inference(subsumption_resolution,[],[f304,f63])).

fof(f63,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f304,plain,
    ( ~ v1_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_34
    | ~ spl3_40 ),
    inference(subsumption_resolution,[],[f296,f252])).

fof(f252,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f251])).

fof(f296,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_40 ),
    inference(resolution,[],[f284,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f284,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f283])).

fof(f312,plain,
    ( m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_1
    | ~ spl3_34
    | ~ spl3_40 ),
    inference(subsumption_resolution,[],[f311,f63])).

fof(f311,plain,
    ( ~ v1_funct_1(sK2)
    | m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_34
    | ~ spl3_40 ),
    inference(subsumption_resolution,[],[f299,f252])).

fof(f299,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_40 ),
    inference(resolution,[],[f284,f48])).

% (7414)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f353,plain,
    ( spl3_48
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_33
    | ~ spl3_34
    | ~ spl3_40 ),
    inference(avatar_split_clause,[],[f307,f283,f251,f240,f66,f62,f347])).

fof(f324,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_struct_0(sK1) != u1_struct_0(sK1)
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_struct_0(sK1) != k2_relat_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f285,plain,
    ( spl3_40
    | ~ spl3_12
    | ~ spl3_16
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f248,f233,f163,f119,f283])).

fof(f119,plain,
    ( spl3_12
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f248,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_12
    | ~ spl3_16
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f246,f164])).

fof(f246,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
    | ~ spl3_12
    | ~ spl3_31 ),
    inference(superposition,[],[f120,f234])).

fof(f120,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f119])).

fof(f253,plain,
    ( spl3_34
    | ~ spl3_13
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f231,f228,f198,f173,f149,f251])).

fof(f149,plain,
    ( spl3_13
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f173,plain,
    ( spl3_19
  <=> v4_relat_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f198,plain,
    ( spl3_24
  <=> v1_partfun1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f228,plain,
    ( spl3_30
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f231,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_13
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f229,f203])).

fof(f203,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_13
    | ~ spl3_19
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f202,f150])).

fof(f150,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f149])).

fof(f202,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_19
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f201,f174])).

fof(f174,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f173])).

fof(f201,plain,
    ( ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_24 ),
    inference(resolution,[],[f199,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f199,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f198])).

% (7416)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f229,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f228])).

fof(f235,plain,
    ( spl3_31
    | ~ spl3_13
    | ~ spl3_19
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f203,f198,f173,f149,f233])).

fof(f230,plain,
    ( spl3_30
    | ~ spl3_9
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f178,f163,f102,f228])).

fof(f102,plain,
    ( spl3_9
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f178,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_9
    | ~ spl3_16 ),
    inference(superposition,[],[f103,f164])).

fof(f103,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f102])).

fof(f222,plain,
    ( spl3_28
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f147,f119,f66,f62,f220])).

fof(f147,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f83,f145])).

fof(f145,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f132,f54])).

fof(f54,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f132,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | v1_relat_1(sK2)
    | ~ spl3_12 ),
    inference(resolution,[],[f120,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f83,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f81,f63])).

fof(f81,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f67,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f210,plain,
    ( spl3_25
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f146,f119,f66,f62,f208])).

fof(f146,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f84,f145])).

fof(f84,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f82,f63])).

fof(f82,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f67,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f200,plain,
    ( spl3_24
    | ~ spl3_1
    | ~ spl3_9
    | spl3_10
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f144,f119,f109,f102,f62,f198])).

fof(f109,plain,
    ( spl3_10
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f144,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_9
    | spl3_10
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f143,f103])).

fof(f143,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_1
    | spl3_10
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f142,f63])).

fof(f142,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | spl3_10
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f130,f110])).

fof(f110,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f109])).

fof(f130,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_12 ),
    inference(resolution,[],[f120,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f196,plain,
    ( ~ spl3_23
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_16
    | spl3_21 ),
    inference(avatar_split_clause,[],[f192,f184,f163,f98,f88,f194])).

fof(f184,plain,
    ( spl3_21
  <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f192,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_16
    | spl3_21 ),
    inference(forward_demodulation,[],[f191,f99])).

fof(f191,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2))
    | ~ spl3_6
    | ~ spl3_16
    | spl3_21 ),
    inference(forward_demodulation,[],[f190,f164])).

fof(f190,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_6
    | spl3_21 ),
    inference(forward_demodulation,[],[f185,f89])).

fof(f185,plain,
    ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | spl3_21 ),
    inference(avatar_component_clause,[],[f184])).

fof(f189,plain,
    ( ~ spl3_21
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f35,f187,f184])).

fof(f35,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                    & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

fof(f175,plain,
    ( spl3_19
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f131,f119,f173])).

fof(f131,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_12 ),
    inference(resolution,[],[f120,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f165,plain,
    ( spl3_16
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_12
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f161,f153,f119,f98,f88,f163])).

fof(f153,plain,
    ( spl3_14
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f161,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_12
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f160,f129])).

fof(f129,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_12 ),
    inference(resolution,[],[f120,f52])).

fof(f160,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f159,f99])).

fof(f159,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_6
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f154,f89])).

fof(f154,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f153])).

fof(f155,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f39,f153])).

fof(f39,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f151,plain,
    ( spl3_13
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f145,f119,f149])).

fof(f121,plain,
    ( spl3_12
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f117,f113,f98,f88,f119])).

fof(f113,plain,
    ( spl3_11
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f117,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f116,f99])).

fof(f116,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f114,f89])).

fof(f114,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f113])).

fof(f115,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f38,f113])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f17])).

fof(f111,plain,
    ( ~ spl3_10
    | spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f107,f88,f74,f70,f109])).

fof(f70,plain,
    ( spl3_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f74,plain,
    ( spl3_4
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f107,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f106,f71])).

fof(f71,plain,
    ( ~ v2_struct_0(sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f106,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f105,f75])).

fof(f75,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f105,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_6 ),
    inference(superposition,[],[f56,f89])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f104,plain,
    ( spl3_9
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f96,f92,f88,f78,f102])).

fof(f78,plain,
    ( spl3_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f92,plain,
    ( spl3_7
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f96,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f95,f86])).

fof(f86,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f79,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f79,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f95,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f93,f89])).

fof(f93,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f92])).

fof(f100,plain,
    ( spl3_8
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f86,f78,f98])).

fof(f94,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f37,f92])).

fof(f37,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f90,plain,
    ( spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f85,f74,f88])).

fof(f85,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f75,f51])).

fof(f80,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f43,f78])).

fof(f43,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f76,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f42,f74])).

fof(f42,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f72,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f41,f70])).

fof(f41,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f68,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f40,f66])).

fof(f40,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f64,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f36,f62])).

fof(f36,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:23:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (7406)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.45  % (7406)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % (7413)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f418,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f64,f68,f72,f76,f80,f90,f94,f100,f104,f111,f115,f121,f151,f155,f165,f175,f189,f196,f200,f210,f222,f230,f235,f253,f285,f324,f353,f372,f376,f396,f417])).
% 0.21/0.45  fof(f417,plain,(
% 0.21/0.45    ~spl3_6 | ~spl3_8 | ~spl3_16 | spl3_22 | ~spl3_28 | ~spl3_31 | ~spl3_48 | ~spl3_53),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f416])).
% 0.21/0.45  fof(f416,plain,(
% 0.21/0.45    $false | (~spl3_6 | ~spl3_8 | ~spl3_16 | spl3_22 | ~spl3_28 | ~spl3_31 | ~spl3_48 | ~spl3_53)),
% 0.21/0.45    inference(subsumption_resolution,[],[f415,f387])).
% 0.21/0.45  fof(f387,plain,(
% 0.21/0.45    k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_28 | ~spl3_53)),
% 0.21/0.45    inference(forward_demodulation,[],[f378,f221])).
% 0.21/0.45  fof(f221,plain,(
% 0.21/0.45    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_28),
% 0.21/0.45    inference(avatar_component_clause,[],[f220])).
% 0.21/0.45  fof(f220,plain,(
% 0.21/0.45    spl3_28 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.45  fof(f378,plain,(
% 0.21/0.45    k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_53),
% 0.21/0.45    inference(resolution,[],[f371,f44])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.45  fof(f371,plain,(
% 0.21/0.45    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl3_53),
% 0.21/0.45    inference(avatar_component_clause,[],[f370])).
% 0.21/0.45  fof(f370,plain,(
% 0.21/0.45    spl3_53 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 0.21/0.45  fof(f415,plain,(
% 0.21/0.45    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_6 | ~spl3_8 | ~spl3_16 | spl3_22 | ~spl3_31 | ~spl3_48)),
% 0.21/0.45    inference(forward_demodulation,[],[f414,f348])).
% 0.21/0.45  fof(f348,plain,(
% 0.21/0.45    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_48),
% 0.21/0.45    inference(avatar_component_clause,[],[f347])).
% 0.21/0.45  fof(f347,plain,(
% 0.21/0.45    spl3_48 <=> k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.21/0.45  fof(f414,plain,(
% 0.21/0.45    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | (~spl3_6 | ~spl3_8 | ~spl3_16 | spl3_22 | ~spl3_31)),
% 0.21/0.45    inference(forward_demodulation,[],[f413,f234])).
% 0.21/0.45  fof(f234,plain,(
% 0.21/0.45    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_31),
% 0.21/0.45    inference(avatar_component_clause,[],[f233])).
% 0.21/0.45  fof(f233,plain,(
% 0.21/0.45    spl3_31 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.45  fof(f413,plain,(
% 0.21/0.45    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | (~spl3_6 | ~spl3_8 | ~spl3_16 | spl3_22)),
% 0.21/0.45    inference(forward_demodulation,[],[f412,f99])).
% 0.21/0.45  fof(f99,plain,(
% 0.21/0.45    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_8),
% 0.21/0.45    inference(avatar_component_clause,[],[f98])).
% 0.21/0.45  fof(f98,plain,(
% 0.21/0.45    spl3_8 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.45  fof(f412,plain,(
% 0.21/0.45    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)) | (~spl3_6 | ~spl3_16 | spl3_22)),
% 0.21/0.45    inference(forward_demodulation,[],[f411,f164])).
% 0.21/0.45  fof(f164,plain,(
% 0.21/0.45    k2_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_16),
% 0.21/0.45    inference(avatar_component_clause,[],[f163])).
% 0.21/0.45  fof(f163,plain,(
% 0.21/0.45    spl3_16 <=> k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.45  fof(f411,plain,(
% 0.21/0.45    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | (~spl3_6 | spl3_22)),
% 0.21/0.45    inference(forward_demodulation,[],[f188,f89])).
% 0.21/0.45  fof(f89,plain,(
% 0.21/0.45    k2_struct_0(sK1) = u1_struct_0(sK1) | ~spl3_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f88])).
% 0.21/0.45  fof(f88,plain,(
% 0.21/0.45    spl3_6 <=> k2_struct_0(sK1) = u1_struct_0(sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.45  fof(f188,plain,(
% 0.21/0.45    k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | spl3_22),
% 0.21/0.45    inference(avatar_component_clause,[],[f187])).
% 0.21/0.45  fof(f187,plain,(
% 0.21/0.45    spl3_22 <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.45  fof(f396,plain,(
% 0.21/0.45    ~spl3_25 | ~spl3_48 | ~spl3_53 | spl3_54),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f395])).
% 0.21/0.45  fof(f395,plain,(
% 0.21/0.45    $false | (~spl3_25 | ~spl3_48 | ~spl3_53 | spl3_54)),
% 0.21/0.45    inference(subsumption_resolution,[],[f394,f377])).
% 0.21/0.45  fof(f377,plain,(
% 0.21/0.45    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_48 | spl3_54)),
% 0.21/0.45    inference(forward_demodulation,[],[f375,f348])).
% 0.21/0.45  fof(f375,plain,(
% 0.21/0.45    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | spl3_54),
% 0.21/0.45    inference(avatar_component_clause,[],[f374])).
% 0.21/0.45  fof(f374,plain,(
% 0.21/0.45    spl3_54 <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 0.21/0.45  fof(f394,plain,(
% 0.21/0.45    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_25 | ~spl3_53)),
% 0.21/0.45    inference(forward_demodulation,[],[f383,f209])).
% 0.21/0.45  fof(f209,plain,(
% 0.21/0.45    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_25),
% 0.21/0.45    inference(avatar_component_clause,[],[f208])).
% 0.21/0.45  fof(f208,plain,(
% 0.21/0.45    spl3_25 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.45  fof(f383,plain,(
% 0.21/0.45    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_53),
% 0.21/0.45    inference(resolution,[],[f371,f52])).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.45  fof(f376,plain,(
% 0.21/0.45    ~spl3_54 | spl3_23 | ~spl3_31),
% 0.21/0.45    inference(avatar_split_clause,[],[f245,f233,f194,f374])).
% 0.21/0.45  fof(f194,plain,(
% 0.21/0.45    spl3_23 <=> k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.46  fof(f245,plain,(
% 0.21/0.46    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | (spl3_23 | ~spl3_31)),
% 0.21/0.46    inference(superposition,[],[f195,f234])).
% 0.21/0.46  fof(f195,plain,(
% 0.21/0.46    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | spl3_23),
% 0.21/0.46    inference(avatar_component_clause,[],[f194])).
% 0.21/0.46  fof(f372,plain,(
% 0.21/0.46    spl3_53 | ~spl3_1 | ~spl3_2 | ~spl3_33 | ~spl3_34 | ~spl3_40),
% 0.21/0.46    inference(avatar_split_clause,[],[f313,f283,f251,f240,f66,f62,f370])).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    spl3_1 <=> v1_funct_1(sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.46  fof(f66,plain,(
% 0.21/0.46    spl3_2 <=> v2_funct_1(sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.46  fof(f240,plain,(
% 0.21/0.46    spl3_33 <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.21/0.46  fof(f251,plain,(
% 0.21/0.46    spl3_34 <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.21/0.46  fof(f283,plain,(
% 0.21/0.46    spl3_40 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.21/0.46  fof(f313,plain,(
% 0.21/0.46    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_1 | ~spl3_2 | ~spl3_33 | ~spl3_34 | ~spl3_40)),
% 0.21/0.46    inference(forward_demodulation,[],[f312,f307])).
% 0.21/0.46  fof(f307,plain,(
% 0.21/0.46    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_33 | ~spl3_34 | ~spl3_40)),
% 0.21/0.46    inference(subsumption_resolution,[],[f306,f67])).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    v2_funct_1(sK2) | ~spl3_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f66])).
% 0.21/0.46  fof(f306,plain,(
% 0.21/0.46    ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_1 | ~spl3_33 | ~spl3_34 | ~spl3_40)),
% 0.21/0.46    inference(subsumption_resolution,[],[f305,f241])).
% 0.21/0.46  fof(f241,plain,(
% 0.21/0.46    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_33),
% 0.21/0.46    inference(avatar_component_clause,[],[f240])).
% 0.21/0.46  fof(f305,plain,(
% 0.21/0.46    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_1 | ~spl3_34 | ~spl3_40)),
% 0.21/0.46    inference(subsumption_resolution,[],[f304,f63])).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    v1_funct_1(sK2) | ~spl3_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f62])).
% 0.21/0.46  fof(f304,plain,(
% 0.21/0.46    ~v1_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_34 | ~spl3_40)),
% 0.21/0.46    inference(subsumption_resolution,[],[f296,f252])).
% 0.21/0.46  fof(f252,plain,(
% 0.21/0.46    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl3_34),
% 0.21/0.46    inference(avatar_component_clause,[],[f251])).
% 0.21/0.46  fof(f296,plain,(
% 0.21/0.46    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_40),
% 0.21/0.46    inference(resolution,[],[f284,f45])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_tops_2(X0,X1,X2) = k2_funct_1(X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.46    inference(flattening,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.46    inference(ennf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_tops_2(X0,X1,X2) = k2_funct_1(X2)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.21/0.46  fof(f284,plain,(
% 0.21/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl3_40),
% 0.21/0.46    inference(avatar_component_clause,[],[f283])).
% 0.21/0.46  fof(f312,plain,(
% 0.21/0.46    m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_1 | ~spl3_34 | ~spl3_40)),
% 0.21/0.46    inference(subsumption_resolution,[],[f311,f63])).
% 0.21/0.46  fof(f311,plain,(
% 0.21/0.46    ~v1_funct_1(sK2) | m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_34 | ~spl3_40)),
% 0.21/0.46    inference(subsumption_resolution,[],[f299,f252])).
% 0.21/0.46  fof(f299,plain,(
% 0.21/0.46    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl3_40),
% 0.21/0.46    inference(resolution,[],[f284,f48])).
% 0.21/0.47  % (7414)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.47    inference(flattening,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).
% 0.21/0.47  fof(f353,plain,(
% 0.21/0.47    spl3_48 | ~spl3_1 | ~spl3_2 | ~spl3_33 | ~spl3_34 | ~spl3_40),
% 0.21/0.47    inference(avatar_split_clause,[],[f307,f283,f251,f240,f66,f62,f347])).
% 0.21/0.47  fof(f324,plain,(
% 0.21/0.47    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_struct_0(sK1) != u1_struct_0(sK1) | k2_struct_0(sK0) != k1_relat_1(sK2) | k2_struct_0(sK1) != k2_relat_1(sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.21/0.47    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.47  fof(f285,plain,(
% 0.21/0.47    spl3_40 | ~spl3_12 | ~spl3_16 | ~spl3_31),
% 0.21/0.47    inference(avatar_split_clause,[],[f248,f233,f163,f119,f283])).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    spl3_12 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.47  fof(f248,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_12 | ~spl3_16 | ~spl3_31)),
% 0.21/0.47    inference(forward_demodulation,[],[f246,f164])).
% 0.21/0.47  fof(f246,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | (~spl3_12 | ~spl3_31)),
% 0.21/0.47    inference(superposition,[],[f120,f234])).
% 0.21/0.47  fof(f120,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f119])).
% 0.21/0.47  fof(f253,plain,(
% 0.21/0.47    spl3_34 | ~spl3_13 | ~spl3_19 | ~spl3_24 | ~spl3_30),
% 0.21/0.47    inference(avatar_split_clause,[],[f231,f228,f198,f173,f149,f251])).
% 0.21/0.47  fof(f149,plain,(
% 0.21/0.47    spl3_13 <=> v1_relat_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.47  fof(f173,plain,(
% 0.21/0.47    spl3_19 <=> v4_relat_1(sK2,k2_struct_0(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.47  fof(f198,plain,(
% 0.21/0.47    spl3_24 <=> v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.47  fof(f228,plain,(
% 0.21/0.47    spl3_30 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.47  fof(f231,plain,(
% 0.21/0.47    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_13 | ~spl3_19 | ~spl3_24 | ~spl3_30)),
% 0.21/0.47    inference(forward_demodulation,[],[f229,f203])).
% 0.21/0.47  fof(f203,plain,(
% 0.21/0.47    k2_struct_0(sK0) = k1_relat_1(sK2) | (~spl3_13 | ~spl3_19 | ~spl3_24)),
% 0.21/0.47    inference(subsumption_resolution,[],[f202,f150])).
% 0.21/0.47  fof(f150,plain,(
% 0.21/0.47    v1_relat_1(sK2) | ~spl3_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f149])).
% 0.21/0.47  fof(f202,plain,(
% 0.21/0.47    k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2) | (~spl3_19 | ~spl3_24)),
% 0.21/0.47    inference(subsumption_resolution,[],[f201,f174])).
% 0.21/0.47  fof(f174,plain,(
% 0.21/0.47    v4_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_19),
% 0.21/0.47    inference(avatar_component_clause,[],[f173])).
% 0.21/0.47  fof(f201,plain,(
% 0.21/0.47    ~v4_relat_1(sK2,k2_struct_0(sK0)) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl3_24),
% 0.21/0.47    inference(resolution,[],[f199,f58])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.21/0.47  fof(f199,plain,(
% 0.21/0.47    v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl3_24),
% 0.21/0.47    inference(avatar_component_clause,[],[f198])).
% 0.21/0.47  % (7416)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.47  fof(f229,plain,(
% 0.21/0.47    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~spl3_30),
% 0.21/0.47    inference(avatar_component_clause,[],[f228])).
% 0.21/0.47  fof(f235,plain,(
% 0.21/0.47    spl3_31 | ~spl3_13 | ~spl3_19 | ~spl3_24),
% 0.21/0.47    inference(avatar_split_clause,[],[f203,f198,f173,f149,f233])).
% 0.21/0.47  fof(f230,plain,(
% 0.21/0.47    spl3_30 | ~spl3_9 | ~spl3_16),
% 0.21/0.47    inference(avatar_split_clause,[],[f178,f163,f102,f228])).
% 0.21/0.47  fof(f102,plain,(
% 0.21/0.47    spl3_9 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.47  fof(f178,plain,(
% 0.21/0.47    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_9 | ~spl3_16)),
% 0.21/0.47    inference(superposition,[],[f103,f164])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f102])).
% 0.21/0.47  fof(f222,plain,(
% 0.21/0.47    spl3_28 | ~spl3_1 | ~spl3_2 | ~spl3_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f147,f119,f66,f62,f220])).
% 0.21/0.47  fof(f147,plain,(
% 0.21/0.47    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_12)),
% 0.21/0.47    inference(subsumption_resolution,[],[f83,f145])).
% 0.21/0.47  fof(f145,plain,(
% 0.21/0.47    v1_relat_1(sK2) | ~spl3_12),
% 0.21/0.47    inference(subsumption_resolution,[],[f132,f54])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | v1_relat_1(sK2) | ~spl3_12),
% 0.21/0.47    inference(resolution,[],[f120,f53])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f81,f63])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_2),
% 0.21/0.47    inference(resolution,[],[f67,f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.47  fof(f210,plain,(
% 0.21/0.47    spl3_25 | ~spl3_1 | ~spl3_2 | ~spl3_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f146,f119,f66,f62,f208])).
% 0.21/0.47  fof(f146,plain,(
% 0.21/0.47    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_12)),
% 0.21/0.47    inference(subsumption_resolution,[],[f84,f145])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f82,f63])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_2),
% 0.21/0.47    inference(resolution,[],[f67,f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f200,plain,(
% 0.21/0.47    spl3_24 | ~spl3_1 | ~spl3_9 | spl3_10 | ~spl3_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f144,f119,f109,f102,f62,f198])).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    spl3_10 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.47  fof(f144,plain,(
% 0.21/0.47    v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_1 | ~spl3_9 | spl3_10 | ~spl3_12)),
% 0.21/0.47    inference(subsumption_resolution,[],[f143,f103])).
% 0.21/0.47  fof(f143,plain,(
% 0.21/0.47    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_1 | spl3_10 | ~spl3_12)),
% 0.21/0.47    inference(subsumption_resolution,[],[f142,f63])).
% 0.21/0.47  fof(f142,plain,(
% 0.21/0.47    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0)) | (spl3_10 | ~spl3_12)),
% 0.21/0.47    inference(subsumption_resolution,[],[f130,f110])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    ~v1_xboole_0(k2_struct_0(sK1)) | spl3_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f109])).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    v1_xboole_0(k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl3_12),
% 0.21/0.47    inference(resolution,[],[f120,f55])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.47    inference(flattening,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.21/0.47  fof(f196,plain,(
% 0.21/0.47    ~spl3_23 | ~spl3_6 | ~spl3_8 | ~spl3_16 | spl3_21),
% 0.21/0.47    inference(avatar_split_clause,[],[f192,f184,f163,f98,f88,f194])).
% 0.21/0.47  fof(f184,plain,(
% 0.21/0.47    spl3_21 <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.47  fof(f192,plain,(
% 0.21/0.47    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | (~spl3_6 | ~spl3_8 | ~spl3_16 | spl3_21)),
% 0.21/0.47    inference(forward_demodulation,[],[f191,f99])).
% 0.21/0.47  fof(f191,plain,(
% 0.21/0.47    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)) | (~spl3_6 | ~spl3_16 | spl3_21)),
% 0.21/0.47    inference(forward_demodulation,[],[f190,f164])).
% 0.21/0.47  fof(f190,plain,(
% 0.21/0.47    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | (~spl3_6 | spl3_21)),
% 0.21/0.47    inference(forward_demodulation,[],[f185,f89])).
% 0.21/0.47  fof(f185,plain,(
% 0.21/0.47    k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | spl3_21),
% 0.21/0.47    inference(avatar_component_clause,[],[f184])).
% 0.21/0.47  fof(f189,plain,(
% 0.21/0.47    ~spl3_21 | ~spl3_22),
% 0.21/0.47    inference(avatar_split_clause,[],[f35,f187,f184])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.21/0.47    inference(negated_conjecture,[],[f13])).
% 0.21/0.47  fof(f13,conjecture,(
% 0.21/0.47    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).
% 0.21/0.47  fof(f175,plain,(
% 0.21/0.47    spl3_19 | ~spl3_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f131,f119,f173])).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    v4_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_12),
% 0.21/0.47    inference(resolution,[],[f120,f59])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.47    inference(pure_predicate_removal,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.47  fof(f165,plain,(
% 0.21/0.47    spl3_16 | ~spl3_6 | ~spl3_8 | ~spl3_12 | ~spl3_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f161,f153,f119,f98,f88,f163])).
% 0.21/0.47  fof(f153,plain,(
% 0.21/0.47    spl3_14 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.47  fof(f161,plain,(
% 0.21/0.47    k2_struct_0(sK1) = k2_relat_1(sK2) | (~spl3_6 | ~spl3_8 | ~spl3_12 | ~spl3_14)),
% 0.21/0.47    inference(forward_demodulation,[],[f160,f129])).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_12),
% 0.21/0.47    inference(resolution,[],[f120,f52])).
% 0.21/0.47  fof(f160,plain,(
% 0.21/0.47    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_6 | ~spl3_8 | ~spl3_14)),
% 0.21/0.47    inference(forward_demodulation,[],[f159,f99])).
% 0.21/0.47  fof(f159,plain,(
% 0.21/0.47    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_6 | ~spl3_14)),
% 0.21/0.47    inference(forward_demodulation,[],[f154,f89])).
% 0.21/0.47  fof(f154,plain,(
% 0.21/0.47    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl3_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f153])).
% 0.21/0.47  fof(f155,plain,(
% 0.21/0.47    spl3_14),
% 0.21/0.47    inference(avatar_split_clause,[],[f39,f153])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f151,plain,(
% 0.21/0.47    spl3_13 | ~spl3_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f145,f119,f149])).
% 0.21/0.47  fof(f121,plain,(
% 0.21/0.47    spl3_12 | ~spl3_6 | ~spl3_8 | ~spl3_11),
% 0.21/0.47    inference(avatar_split_clause,[],[f117,f113,f98,f88,f119])).
% 0.21/0.47  fof(f113,plain,(
% 0.21/0.47    spl3_11 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_6 | ~spl3_8 | ~spl3_11)),
% 0.21/0.47    inference(forward_demodulation,[],[f116,f99])).
% 0.21/0.47  fof(f116,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_6 | ~spl3_11)),
% 0.21/0.47    inference(forward_demodulation,[],[f114,f89])).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f113])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    spl3_11),
% 0.21/0.47    inference(avatar_split_clause,[],[f38,f113])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    ~spl3_10 | spl3_3 | ~spl3_4 | ~spl3_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f107,f88,f74,f70,f109])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    spl3_3 <=> v2_struct_0(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    spl3_4 <=> l1_struct_0(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    ~v1_xboole_0(k2_struct_0(sK1)) | (spl3_3 | ~spl3_4 | ~spl3_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f106,f71])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    ~v2_struct_0(sK1) | spl3_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f70])).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    ~v1_xboole_0(k2_struct_0(sK1)) | v2_struct_0(sK1) | (~spl3_4 | ~spl3_6)),
% 0.21/0.47    inference(subsumption_resolution,[],[f105,f75])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    l1_struct_0(sK1) | ~spl3_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f74])).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    ~v1_xboole_0(k2_struct_0(sK1)) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl3_6),
% 0.21/0.47    inference(superposition,[],[f56,f89])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    spl3_9 | ~spl3_5 | ~spl3_6 | ~spl3_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f96,f92,f88,f78,f102])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    spl3_5 <=> l1_struct_0(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    spl3_7 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_5 | ~spl3_6 | ~spl3_7)),
% 0.21/0.47    inference(forward_demodulation,[],[f95,f86])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_5),
% 0.21/0.47    inference(resolution,[],[f79,f51])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    l1_struct_0(sK0) | ~spl3_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f78])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_6 | ~spl3_7)),
% 0.21/0.47    inference(forward_demodulation,[],[f93,f89])).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f92])).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    spl3_8 | ~spl3_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f86,f78,f98])).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    spl3_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f37,f92])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    spl3_6 | ~spl3_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f85,f74,f88])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    k2_struct_0(sK1) = u1_struct_0(sK1) | ~spl3_4),
% 0.21/0.47    inference(resolution,[],[f75,f51])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    spl3_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f43,f78])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    l1_struct_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    spl3_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f42,f74])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    l1_struct_0(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    ~spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f41,f70])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ~v2_struct_0(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f40,f66])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    v2_funct_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f36,f62])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    v1_funct_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (7406)------------------------------
% 0.21/0.47  % (7406)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (7406)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (7406)Memory used [KB]: 6396
% 0.21/0.47  % (7406)Time elapsed: 0.047 s
% 0.21/0.47  % (7406)------------------------------
% 0.21/0.47  % (7406)------------------------------
% 0.21/0.47  % (7405)Success in time 0.113 s
%------------------------------------------------------------------------------
