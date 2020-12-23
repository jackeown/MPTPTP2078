%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 219 expanded)
%              Number of leaves         :   26 ( 103 expanded)
%              Depth                    :    9
%              Number of atoms          :  329 (1021 expanded)
%              Number of equality atoms :   42 ( 149 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f179,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f45,f50,f55,f60,f65,f70,f80,f86,f113,f120,f126,f136,f148,f156,f160,f173,f178])).

fof(f178,plain,
    ( ~ spl3_2
    | ~ spl3_6
    | ~ spl3_20
    | spl3_21 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_20
    | spl3_21 ),
    inference(subsumption_resolution,[],[f176,f155])).

fof(f155,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl3_20
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f176,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_2
    | ~ spl3_6
    | spl3_21 ),
    inference(subsumption_resolution,[],[f175,f59])).

fof(f59,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl3_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f175,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_2
    | spl3_21 ),
    inference(subsumption_resolution,[],[f174,f39])).

fof(f39,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f174,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_21 ),
    inference(resolution,[],[f172,f29])).

fof(f29,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => v2_funct_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).

fof(f172,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | spl3_21 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl3_21
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f173,plain,
    ( ~ spl3_21
    | spl3_16
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f168,f145,f123,f170])).

fof(f123,plain,
    ( spl3_16
  <=> v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f145,plain,
    ( spl3_19
  <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f168,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | spl3_16
    | ~ spl3_19 ),
    inference(superposition,[],[f125,f147])).

fof(f147,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f145])).

fof(f125,plain,
    ( ~ v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f123])).

fof(f160,plain,
    ( spl3_18
    | ~ spl3_3
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f159,f83,f77,f42,f141])).

fof(f141,plain,
    ( spl3_18
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

% (11736)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
fof(f42,plain,
    ( spl3_3
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f77,plain,
    ( spl3_9
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f83,plain,
    ( spl3_10
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f159,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_3
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f158,f85])).

fof(f85,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f83])).

fof(f158,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f44,f79])).

fof(f79,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f77])).

fof(f44,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f156,plain,
    ( spl3_20
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f150,f133,f153])).

fof(f133,plain,
    ( spl3_17
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f150,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_17 ),
    inference(resolution,[],[f135,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f135,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f133])).

fof(f148,plain,
    ( ~ spl3_17
    | ~ spl3_18
    | spl3_19
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f139,f117,f57,f37,f145,f141,f133])).

fof(f117,plain,
    ( spl3_15
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f139,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f138,f59])).

fof(f138,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ spl3_2
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f137,f39])).

fof(f137,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ spl3_15 ),
    inference(resolution,[],[f119,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f119,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f117])).

fof(f136,plain,
    ( spl3_17
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f131,f83,f77,f47,f133])).

fof(f47,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f131,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f130,f85])).

fof(f130,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f49,f79])).

fof(f49,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f126,plain,
    ( ~ spl3_16
    | ~ spl3_10
    | spl3_14 ),
    inference(avatar_split_clause,[],[f121,f110,f83,f123])).

fof(f110,plain,
    ( spl3_14
  <=> v2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f121,plain,
    ( ~ v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_10
    | spl3_14 ),
    inference(forward_demodulation,[],[f112,f85])).

fof(f112,plain,
    ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f110])).

fof(f120,plain,
    ( spl3_15
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f115,f83,f77,f52,f117])).

fof(f52,plain,
    ( spl3_5
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f115,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f114,f79])).

fof(f114,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(superposition,[],[f54,f85])).

fof(f54,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f113,plain,
    ( ~ spl3_14
    | spl3_1
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f108,f77,f32,f110])).

fof(f32,plain,
    ( spl3_1
  <=> v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f108,plain,
    ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl3_1
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f34,f79])).

fof(f34,plain,
    ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f86,plain,
    ( spl3_10
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f81,f67,f83])).

fof(f67,plain,
    ( spl3_8
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f81,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_8 ),
    inference(resolution,[],[f69,f28])).

fof(f28,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f69,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f67])).

fof(f80,plain,
    ( spl3_9
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f75,f62,f77])).

fof(f62,plain,
    ( spl3_7
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f75,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f64,f28])).

fof(f64,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f70,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f19,f67])).

fof(f19,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f17,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                & v2_funct_1(X2)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1) )
   => ( ? [X2] :
          ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X2] :
        ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))
        & v2_funct_1(X2)
        & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
      & v2_funct_1(sK2)
      & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_tops_2)).

fof(f65,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f20,f62])).

fof(f20,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f60,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f21,f57])).

fof(f21,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f55,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f22,f52])).

fof(f22,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f50,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f23,f47])).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f18])).

fof(f45,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f24,f42])).

fof(f24,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f25,f37])).

fof(f25,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f35,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f26,f32])).

fof(f26,plain,(
    ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:29:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (11737)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.51  % (11747)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.52  % (11739)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (11740)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.52  % (11734)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.52  % (11739)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f179,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f35,f40,f45,f50,f55,f60,f65,f70,f80,f86,f113,f120,f126,f136,f148,f156,f160,f173,f178])).
% 0.22/0.53  fof(f178,plain,(
% 0.22/0.53    ~spl3_2 | ~spl3_6 | ~spl3_20 | spl3_21),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f177])).
% 0.22/0.53  fof(f177,plain,(
% 0.22/0.53    $false | (~spl3_2 | ~spl3_6 | ~spl3_20 | spl3_21)),
% 0.22/0.53    inference(subsumption_resolution,[],[f176,f155])).
% 0.22/0.53  fof(f155,plain,(
% 0.22/0.53    v1_relat_1(sK2) | ~spl3_20),
% 0.22/0.53    inference(avatar_component_clause,[],[f153])).
% 0.22/0.53  fof(f153,plain,(
% 0.22/0.53    spl3_20 <=> v1_relat_1(sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.53  fof(f176,plain,(
% 0.22/0.53    ~v1_relat_1(sK2) | (~spl3_2 | ~spl3_6 | spl3_21)),
% 0.22/0.53    inference(subsumption_resolution,[],[f175,f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    v1_funct_1(sK2) | ~spl3_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    spl3_6 <=> v1_funct_1(sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.53  fof(f175,plain,(
% 0.22/0.53    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_2 | spl3_21)),
% 0.22/0.53    inference(subsumption_resolution,[],[f174,f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    v2_funct_1(sK2) | ~spl3_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    spl3_2 <=> v2_funct_1(sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.53  fof(f174,plain,(
% 0.22/0.53    ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_21),
% 0.22/0.53    inference(resolution,[],[f172,f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => v2_funct_1(k2_funct_1(X0))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).
% 0.22/0.53  fof(f172,plain,(
% 0.22/0.53    ~v2_funct_1(k2_funct_1(sK2)) | spl3_21),
% 0.22/0.53    inference(avatar_component_clause,[],[f170])).
% 0.22/0.53  fof(f170,plain,(
% 0.22/0.53    spl3_21 <=> v2_funct_1(k2_funct_1(sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.53  fof(f173,plain,(
% 0.22/0.53    ~spl3_21 | spl3_16 | ~spl3_19),
% 0.22/0.53    inference(avatar_split_clause,[],[f168,f145,f123,f170])).
% 0.22/0.53  fof(f123,plain,(
% 0.22/0.53    spl3_16 <=> v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.53  fof(f145,plain,(
% 0.22/0.53    spl3_19 <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.53  fof(f168,plain,(
% 0.22/0.53    ~v2_funct_1(k2_funct_1(sK2)) | (spl3_16 | ~spl3_19)),
% 0.22/0.53    inference(superposition,[],[f125,f147])).
% 0.22/0.53  fof(f147,plain,(
% 0.22/0.53    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_19),
% 0.22/0.53    inference(avatar_component_clause,[],[f145])).
% 0.22/0.53  fof(f125,plain,(
% 0.22/0.53    ~v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | spl3_16),
% 0.22/0.53    inference(avatar_component_clause,[],[f123])).
% 0.22/0.53  fof(f160,plain,(
% 0.22/0.53    spl3_18 | ~spl3_3 | ~spl3_9 | ~spl3_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f159,f83,f77,f42,f141])).
% 0.22/0.53  fof(f141,plain,(
% 0.22/0.53    spl3_18 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.53  % (11736)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    spl3_3 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    spl3_9 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    spl3_10 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.53  fof(f159,plain,(
% 0.22/0.53    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_3 | ~spl3_9 | ~spl3_10)),
% 0.22/0.53    inference(forward_demodulation,[],[f158,f85])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_10),
% 0.22/0.53    inference(avatar_component_clause,[],[f83])).
% 0.22/0.53  fof(f158,plain,(
% 0.22/0.53    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_3 | ~spl3_9)),
% 0.22/0.53    inference(forward_demodulation,[],[f44,f79])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f77])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl3_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f42])).
% 0.22/0.53  fof(f156,plain,(
% 0.22/0.53    spl3_20 | ~spl3_17),
% 0.22/0.53    inference(avatar_split_clause,[],[f150,f133,f153])).
% 0.22/0.53  fof(f133,plain,(
% 0.22/0.53    spl3_17 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.53  fof(f150,plain,(
% 0.22/0.53    v1_relat_1(sK2) | ~spl3_17),
% 0.22/0.53    inference(resolution,[],[f135,f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.53  fof(f135,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_17),
% 0.22/0.53    inference(avatar_component_clause,[],[f133])).
% 0.22/0.53  fof(f148,plain,(
% 0.22/0.53    ~spl3_17 | ~spl3_18 | spl3_19 | ~spl3_2 | ~spl3_6 | ~spl3_15),
% 0.22/0.53    inference(avatar_split_clause,[],[f139,f117,f57,f37,f145,f141,f133])).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    spl3_15 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.53  fof(f139,plain,(
% 0.22/0.53    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_2 | ~spl3_6 | ~spl3_15)),
% 0.22/0.53    inference(subsumption_resolution,[],[f138,f59])).
% 0.22/0.53  fof(f138,plain,(
% 0.22/0.53    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_1(sK2) | (~spl3_2 | ~spl3_15)),
% 0.22/0.53    inference(subsumption_resolution,[],[f137,f39])).
% 0.22/0.53  fof(f137,plain,(
% 0.22/0.53    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_1(sK2) | ~spl3_15),
% 0.22/0.53    inference(resolution,[],[f119,f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.53    inference(flattening,[],[f9])).
% 0.22/0.53  fof(f9,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_tops_2(X0,X1,X2) = k2_funct_1(X2)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.22/0.53  fof(f119,plain,(
% 0.22/0.53    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_15),
% 0.22/0.53    inference(avatar_component_clause,[],[f117])).
% 0.22/0.53  fof(f136,plain,(
% 0.22/0.53    spl3_17 | ~spl3_4 | ~spl3_9 | ~spl3_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f131,f83,f77,f47,f133])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.53  fof(f131,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_4 | ~spl3_9 | ~spl3_10)),
% 0.22/0.53    inference(forward_demodulation,[],[f130,f85])).
% 0.22/0.53  fof(f130,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_4 | ~spl3_9)),
% 0.22/0.53    inference(forward_demodulation,[],[f49,f79])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f47])).
% 0.22/0.53  fof(f126,plain,(
% 0.22/0.53    ~spl3_16 | ~spl3_10 | spl3_14),
% 0.22/0.53    inference(avatar_split_clause,[],[f121,f110,f83,f123])).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    spl3_14 <=> v2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.53  fof(f121,plain,(
% 0.22/0.53    ~v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | (~spl3_10 | spl3_14)),
% 0.22/0.53    inference(forward_demodulation,[],[f112,f85])).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | spl3_14),
% 0.22/0.53    inference(avatar_component_clause,[],[f110])).
% 0.22/0.53  fof(f120,plain,(
% 0.22/0.53    spl3_15 | ~spl3_5 | ~spl3_9 | ~spl3_10),
% 0.22/0.53    inference(avatar_split_clause,[],[f115,f83,f77,f52,f117])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    spl3_5 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.53  fof(f115,plain,(
% 0.22/0.53    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_5 | ~spl3_9 | ~spl3_10)),
% 0.22/0.53    inference(forward_demodulation,[],[f114,f79])).
% 0.22/0.53  fof(f114,plain,(
% 0.22/0.53    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) | (~spl3_5 | ~spl3_10)),
% 0.22/0.53    inference(superposition,[],[f54,f85])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f52])).
% 0.22/0.53  fof(f113,plain,(
% 0.22/0.53    ~spl3_14 | spl3_1 | ~spl3_9),
% 0.22/0.53    inference(avatar_split_clause,[],[f108,f77,f32,f110])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    spl3_1 <=> v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | (spl3_1 | ~spl3_9)),
% 0.22/0.53    inference(forward_demodulation,[],[f34,f79])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | spl3_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f32])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    spl3_10 | ~spl3_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f81,f67,f83])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    spl3_8 <=> l1_struct_0(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_8),
% 0.22/0.53    inference(resolution,[],[f69,f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    l1_struct_0(sK0) | ~spl3_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f67])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    spl3_9 | ~spl3_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f75,f62,f77])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    spl3_7 <=> l1_struct_0(sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_7),
% 0.22/0.53    inference(resolution,[],[f64,f28])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    l1_struct_0(sK1) | ~spl3_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f62])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    spl3_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f19,f67])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    l1_struct_0(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ((~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f17,f16,f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (~v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ? [X1] : (? [X2] : (~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ? [X2] : (~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f8,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (~v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f7])).
% 0.22/0.53  fof(f7,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : ((~v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,negated_conjecture,(
% 0.22/0.53    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 0.22/0.53    inference(negated_conjecture,[],[f5])).
% 0.22/0.53  fof(f5,conjecture,(
% 0.22/0.53    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_tops_2)).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    spl3_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f20,f62])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    l1_struct_0(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    spl3_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f21,f57])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    v1_funct_1(sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    spl3_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f22,f52])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    spl3_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f23,f47])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    spl3_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f24,f42])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    spl3_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f25,f37])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    v2_funct_1(sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ~spl3_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f26,f32])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (11739)------------------------------
% 0.22/0.53  % (11739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (11739)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (11739)Memory used [KB]: 6140
% 0.22/0.53  % (11739)Time elapsed: 0.044 s
% 0.22/0.53  % (11739)------------------------------
% 0.22/0.53  % (11739)------------------------------
% 0.22/0.53  % (11730)Success in time 0.17 s
%------------------------------------------------------------------------------
