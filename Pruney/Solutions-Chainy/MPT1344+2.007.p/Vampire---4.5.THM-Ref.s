%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 264 expanded)
%              Number of leaves         :   33 ( 128 expanded)
%              Depth                    :    8
%              Number of atoms          :  438 (1291 expanded)
%              Number of equality atoms :   93 ( 311 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f360,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f56,f61,f71,f76,f81,f86,f91,f104,f115,f121,f189,f217,f259,f265,f271,f289,f296,f317,f345,f359])).

fof(f359,plain,
    ( ~ spl4_13
    | spl4_22
    | ~ spl4_33
    | ~ spl4_35
    | ~ spl4_37 ),
    inference(avatar_contradiction_clause,[],[f358])).

fof(f358,plain,
    ( $false
    | ~ spl4_13
    | spl4_22
    | ~ spl4_33
    | ~ spl4_35
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f357,f330])).

fof(f330,plain,
    ( ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0)
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f329])).

fof(f329,plain,
    ( spl4_37
  <=> ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f357,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k10_relat_1(sK2,sK3)
    | ~ spl4_13
    | spl4_22
    | ~ spl4_33
    | ~ spl4_35 ),
    inference(forward_demodulation,[],[f356,f316])).

fof(f316,plain,
    ( ! [X1] : k10_relat_1(sK2,X1) = k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X1)
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f315])).

fof(f315,plain,
    ( spl4_35
  <=> ! [X1] : k10_relat_1(sK2,X1) = k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f356,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),sK3)
    | ~ spl4_13
    | spl4_22
    | ~ spl4_33 ),
    inference(forward_demodulation,[],[f355,f295])).

fof(f295,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f293])).

fof(f293,plain,
    ( spl4_33
  <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f355,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)
    | ~ spl4_13
    | spl4_22 ),
    inference(forward_demodulation,[],[f216,f120])).

fof(f120,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl4_13
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f216,plain,
    ( k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k7_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)
    | spl4_22 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl4_22
  <=> k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) = k7_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f345,plain,
    ( spl4_37
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f341,f262,f329])).

fof(f262,plain,
    ( spl4_30
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f341,plain,
    ( ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0)
    | ~ spl4_30 ),
    inference(resolution,[],[f264,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f264,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f262])).

fof(f317,plain,
    ( spl4_35
    | ~ spl4_11
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f313,f279,f102,f315])).

fof(f102,plain,
    ( spl4_11
  <=> ! [X0] : k10_relat_1(sK2,X0) = k9_relat_1(k2_funct_1(sK2),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f279,plain,
    ( spl4_32
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f313,plain,
    ( ! [X1] : k10_relat_1(sK2,X1) = k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X1)
    | ~ spl4_11
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f307,f103])).

fof(f103,plain,
    ( ! [X0] : k10_relat_1(sK2,X0) = k9_relat_1(k2_funct_1(sK2),X0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f102])).

fof(f307,plain,
    ( ! [X1] : k9_relat_1(k2_funct_1(sK2),X1) = k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X1)
    | ~ spl4_32 ),
    inference(resolution,[],[f281,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f281,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f279])).

fof(f296,plain,
    ( ~ spl4_30
    | ~ spl4_29
    | spl4_33
    | ~ spl4_2
    | ~ spl4_7
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f291,f268,f78,f53,f293,f256,f262])).

fof(f256,plain,
    ( spl4_29
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f53,plain,
    ( spl4_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f78,plain,
    ( spl4_7
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f268,plain,
    ( spl4_31
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f291,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl4_2
    | ~ spl4_7
    | ~ spl4_31 ),
    inference(subsumption_resolution,[],[f290,f80])).

fof(f80,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f78])).

fof(f290,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ spl4_2
    | ~ spl4_31 ),
    inference(subsumption_resolution,[],[f286,f55])).

fof(f55,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f53])).

fof(f286,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ spl4_31 ),
    inference(resolution,[],[f270,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f270,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f268])).

fof(f289,plain,
    ( ~ spl4_30
    | ~ spl4_29
    | spl4_32
    | ~ spl4_2
    | ~ spl4_7
    | ~ spl4_31 ),
    inference(avatar_split_clause,[],[f288,f268,f78,f53,f279,f256,f262])).

fof(f288,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl4_2
    | ~ spl4_7
    | ~ spl4_31 ),
    inference(subsumption_resolution,[],[f287,f80])).

fof(f287,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ spl4_2
    | ~ spl4_31 ),
    inference(subsumption_resolution,[],[f285,f55])).

fof(f285,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ spl4_31 ),
    inference(resolution,[],[f270,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f271,plain,
    ( spl4_31
    | ~ spl4_6
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f266,f118,f112,f73,f268])).

fof(f73,plain,
    ( spl4_6
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f112,plain,
    ( spl4_12
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f266,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl4_6
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f247,f114])).

fof(f114,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f112])).

fof(f247,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl4_6
    | ~ spl4_13 ),
    inference(superposition,[],[f75,f120])).

fof(f75,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f265,plain,
    ( spl4_30
    | ~ spl4_5
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f260,f118,f112,f68,f262])).

fof(f68,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f260,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl4_5
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f246,f114])).

fof(f246,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl4_5
    | ~ spl4_13 ),
    inference(superposition,[],[f70,f120])).

fof(f70,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f259,plain,
    ( spl4_29
    | ~ spl4_3
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f254,f118,f112,f58,f256])).

fof(f58,plain,
    ( spl4_3
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f254,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl4_3
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f245,f114])).

fof(f245,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl4_3
    | ~ spl4_13 ),
    inference(superposition,[],[f60,f120])).

fof(f60,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f217,plain,
    ( ~ spl4_22
    | spl4_1
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f207,f112,f48,f214])).

fof(f48,plain,
    ( spl4_1
  <=> k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) = k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f207,plain,
    ( k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k7_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)
    | spl4_1
    | ~ spl4_12 ),
    inference(superposition,[],[f50,f114])).

fof(f50,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f189,plain,
    ( spl4_10
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f188,f68,f98])).

fof(f98,plain,
    ( spl4_10
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f188,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f174,f45])).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f174,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ spl4_5 ),
    inference(resolution,[],[f70,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f121,plain,
    ( spl4_13
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f116,f88,f118])).

fof(f88,plain,
    ( spl4_9
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f116,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_9 ),
    inference(resolution,[],[f90,f40])).

fof(f40,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f90,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f88])).

fof(f115,plain,
    ( spl4_12
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f110,f83,f112])).

fof(f83,plain,
    ( spl4_8
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f110,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl4_8 ),
    inference(resolution,[],[f85,f40])).

fof(f85,plain,
    ( l1_struct_0(sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f83])).

fof(f104,plain,
    ( ~ spl4_10
    | ~ spl4_7
    | spl4_11
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f92,f53,f102,f78,f98])).

fof(f92,plain,
    ( ! [X0] :
        ( k10_relat_1(sK2,X0) = k9_relat_1(k2_funct_1(sK2),X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_2 ),
    inference(resolution,[],[f55,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

fof(f91,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f28,f88])).

fof(f28,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f26,f25,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X3)
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X3)
                & v2_funct_1(X2)
                & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),X3)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),X3)
            & v2_funct_1(X2)
            & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X3)
          & v2_funct_1(sK2)
          & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X3] :
        ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X3)
        & v2_funct_1(sK2)
        & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)
      & v2_funct_1(sK2)
      & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v2_funct_1(X2)
                        & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                     => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v2_funct_1(X2)
                      & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                   => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_tops_2)).

fof(f86,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f29,f83])).

fof(f29,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f81,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f30,f78])).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f31,f73])).

fof(f31,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f32,f68])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f34,f58])).

fof(f34,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f35,f53])).

fof(f35,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f51,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f36,f48])).

fof(f36,plain,(
    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:24:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (9979)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (9979)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f360,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f51,f56,f61,f71,f76,f81,f86,f91,f104,f115,f121,f189,f217,f259,f265,f271,f289,f296,f317,f345,f359])).
% 0.21/0.47  fof(f359,plain,(
% 0.21/0.47    ~spl4_13 | spl4_22 | ~spl4_33 | ~spl4_35 | ~spl4_37),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f358])).
% 0.21/0.47  fof(f358,plain,(
% 0.21/0.47    $false | (~spl4_13 | spl4_22 | ~spl4_33 | ~spl4_35 | ~spl4_37)),
% 0.21/0.47    inference(subsumption_resolution,[],[f357,f330])).
% 0.21/0.47  fof(f330,plain,(
% 0.21/0.47    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0)) ) | ~spl4_37),
% 0.21/0.47    inference(avatar_component_clause,[],[f329])).
% 0.21/0.47  fof(f329,plain,(
% 0.21/0.47    spl4_37 <=> ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.21/0.47  fof(f357,plain,(
% 0.21/0.47    k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k10_relat_1(sK2,sK3) | (~spl4_13 | spl4_22 | ~spl4_33 | ~spl4_35)),
% 0.21/0.47    inference(forward_demodulation,[],[f356,f316])).
% 0.21/0.47  fof(f316,plain,(
% 0.21/0.47    ( ! [X1] : (k10_relat_1(sK2,X1) = k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X1)) ) | ~spl4_35),
% 0.21/0.47    inference(avatar_component_clause,[],[f315])).
% 0.21/0.47  fof(f315,plain,(
% 0.21/0.47    spl4_35 <=> ! [X1] : k10_relat_1(sK2,X1) = k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.21/0.47  fof(f356,plain,(
% 0.21/0.47    k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),sK3) | (~spl4_13 | spl4_22 | ~spl4_33)),
% 0.21/0.47    inference(forward_demodulation,[],[f355,f295])).
% 0.21/0.47  fof(f295,plain,(
% 0.21/0.47    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl4_33),
% 0.21/0.47    inference(avatar_component_clause,[],[f293])).
% 0.21/0.47  fof(f293,plain,(
% 0.21/0.47    spl4_33 <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.21/0.47  fof(f355,plain,(
% 0.21/0.47    k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) | (~spl4_13 | spl4_22)),
% 0.21/0.47    inference(forward_demodulation,[],[f216,f120])).
% 0.21/0.47  fof(f120,plain,(
% 0.21/0.47    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl4_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f118])).
% 0.21/0.47  fof(f118,plain,(
% 0.21/0.47    spl4_13 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.47  fof(f216,plain,(
% 0.21/0.47    k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k7_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) | spl4_22),
% 0.21/0.47    inference(avatar_component_clause,[],[f214])).
% 0.21/0.47  fof(f214,plain,(
% 0.21/0.47    spl4_22 <=> k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) = k7_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.47  fof(f345,plain,(
% 0.21/0.47    spl4_37 | ~spl4_30),
% 0.21/0.47    inference(avatar_split_clause,[],[f341,f262,f329])).
% 0.21/0.47  fof(f262,plain,(
% 0.21/0.47    spl4_30 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.21/0.47  fof(f341,plain,(
% 0.21/0.47    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0)) ) | ~spl4_30),
% 0.21/0.47    inference(resolution,[],[f264,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.47  fof(f264,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl4_30),
% 0.21/0.47    inference(avatar_component_clause,[],[f262])).
% 0.21/0.47  fof(f317,plain,(
% 0.21/0.47    spl4_35 | ~spl4_11 | ~spl4_32),
% 0.21/0.47    inference(avatar_split_clause,[],[f313,f279,f102,f315])).
% 0.21/0.47  fof(f102,plain,(
% 0.21/0.47    spl4_11 <=> ! [X0] : k10_relat_1(sK2,X0) = k9_relat_1(k2_funct_1(sK2),X0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.47  fof(f279,plain,(
% 0.21/0.47    spl4_32 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.21/0.47  fof(f313,plain,(
% 0.21/0.47    ( ! [X1] : (k10_relat_1(sK2,X1) = k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X1)) ) | (~spl4_11 | ~spl4_32)),
% 0.21/0.47    inference(forward_demodulation,[],[f307,f103])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    ( ! [X0] : (k10_relat_1(sK2,X0) = k9_relat_1(k2_funct_1(sK2),X0)) ) | ~spl4_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f102])).
% 0.21/0.47  fof(f307,plain,(
% 0.21/0.47    ( ! [X1] : (k9_relat_1(k2_funct_1(sK2),X1) = k7_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2),X1)) ) | ~spl4_32),
% 0.21/0.47    inference(resolution,[],[f281,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.47  fof(f281,plain,(
% 0.21/0.47    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~spl4_32),
% 0.21/0.47    inference(avatar_component_clause,[],[f279])).
% 0.21/0.47  fof(f296,plain,(
% 0.21/0.47    ~spl4_30 | ~spl4_29 | spl4_33 | ~spl4_2 | ~spl4_7 | ~spl4_31),
% 0.21/0.47    inference(avatar_split_clause,[],[f291,f268,f78,f53,f293,f256,f262])).
% 0.21/0.47  fof(f256,plain,(
% 0.21/0.47    spl4_29 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    spl4_2 <=> v2_funct_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    spl4_7 <=> v1_funct_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.47  fof(f268,plain,(
% 0.21/0.47    spl4_31 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.21/0.47  fof(f291,plain,(
% 0.21/0.47    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl4_2 | ~spl4_7 | ~spl4_31)),
% 0.21/0.47    inference(subsumption_resolution,[],[f290,f80])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    v1_funct_1(sK2) | ~spl4_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f78])).
% 0.21/0.47  fof(f290,plain,(
% 0.21/0.47    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_1(sK2) | (~spl4_2 | ~spl4_31)),
% 0.21/0.47    inference(subsumption_resolution,[],[f286,f55])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    v2_funct_1(sK2) | ~spl4_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f53])).
% 0.21/0.47  fof(f286,plain,(
% 0.21/0.47    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_1(sK2) | ~spl4_31),
% 0.21/0.47    inference(resolution,[],[f270,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.47    inference(flattening,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.21/0.47  fof(f270,plain,(
% 0.21/0.47    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl4_31),
% 0.21/0.47    inference(avatar_component_clause,[],[f268])).
% 0.21/0.47  fof(f289,plain,(
% 0.21/0.47    ~spl4_30 | ~spl4_29 | spl4_32 | ~spl4_2 | ~spl4_7 | ~spl4_31),
% 0.21/0.47    inference(avatar_split_clause,[],[f288,f268,f78,f53,f279,f256,f262])).
% 0.21/0.47  fof(f288,plain,(
% 0.21/0.47    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl4_2 | ~spl4_7 | ~spl4_31)),
% 0.21/0.47    inference(subsumption_resolution,[],[f287,f80])).
% 0.21/0.47  fof(f287,plain,(
% 0.21/0.47    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_1(sK2) | (~spl4_2 | ~spl4_31)),
% 0.21/0.47    inference(subsumption_resolution,[],[f285,f55])).
% 0.21/0.47  fof(f285,plain,(
% 0.21/0.47    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_1(sK2) | ~spl4_31),
% 0.21/0.47    inference(resolution,[],[f270,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.47    inference(flattening,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.47  fof(f271,plain,(
% 0.21/0.47    spl4_31 | ~spl4_6 | ~spl4_12 | ~spl4_13),
% 0.21/0.47    inference(avatar_split_clause,[],[f266,f118,f112,f73,f268])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    spl4_6 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    spl4_12 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.47  fof(f266,plain,(
% 0.21/0.47    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl4_6 | ~spl4_12 | ~spl4_13)),
% 0.21/0.47    inference(forward_demodulation,[],[f247,f114])).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl4_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f112])).
% 0.21/0.47  fof(f247,plain,(
% 0.21/0.47    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) | (~spl4_6 | ~spl4_13)),
% 0.21/0.47    inference(superposition,[],[f75,f120])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl4_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f73])).
% 0.21/0.47  fof(f265,plain,(
% 0.21/0.47    spl4_30 | ~spl4_5 | ~spl4_12 | ~spl4_13),
% 0.21/0.47    inference(avatar_split_clause,[],[f260,f118,f112,f68,f262])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.47  fof(f260,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl4_5 | ~spl4_12 | ~spl4_13)),
% 0.21/0.47    inference(forward_demodulation,[],[f246,f114])).
% 0.21/0.47  fof(f246,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) | (~spl4_5 | ~spl4_13)),
% 0.21/0.47    inference(superposition,[],[f70,f120])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl4_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f68])).
% 0.21/0.47  fof(f259,plain,(
% 0.21/0.47    spl4_29 | ~spl4_3 | ~spl4_12 | ~spl4_13),
% 0.21/0.47    inference(avatar_split_clause,[],[f254,f118,f112,f58,f256])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    spl4_3 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.47  fof(f254,plain,(
% 0.21/0.47    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl4_3 | ~spl4_12 | ~spl4_13)),
% 0.21/0.47    inference(forward_demodulation,[],[f245,f114])).
% 0.21/0.47  fof(f245,plain,(
% 0.21/0.47    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2) | (~spl4_3 | ~spl4_13)),
% 0.21/0.47    inference(superposition,[],[f60,f120])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl4_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f58])).
% 0.21/0.47  fof(f217,plain,(
% 0.21/0.47    ~spl4_22 | spl4_1 | ~spl4_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f207,f112,f48,f214])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    spl4_1 <=> k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) = k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.47  fof(f207,plain,(
% 0.21/0.47    k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3) != k7_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK3) | (spl4_1 | ~spl4_12)),
% 0.21/0.47    inference(superposition,[],[f50,f114])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) | spl4_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f48])).
% 0.21/0.47  fof(f189,plain,(
% 0.21/0.47    spl4_10 | ~spl4_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f188,f68,f98])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    spl4_10 <=> v1_relat_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.47  fof(f188,plain,(
% 0.21/0.47    v1_relat_1(sK2) | ~spl4_5),
% 0.21/0.47    inference(subsumption_resolution,[],[f174,f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.47  fof(f174,plain,(
% 0.21/0.47    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | ~spl4_5),
% 0.21/0.47    inference(resolution,[],[f70,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.47  fof(f121,plain,(
% 0.21/0.47    spl4_13 | ~spl4_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f116,f88,f118])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    spl4_9 <=> l1_struct_0(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.47  fof(f116,plain,(
% 0.21/0.47    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl4_9),
% 0.21/0.47    inference(resolution,[],[f90,f40])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    l1_struct_0(sK0) | ~spl4_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f88])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    spl4_12 | ~spl4_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f110,f83,f112])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    spl4_8 <=> l1_struct_0(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl4_8),
% 0.21/0.47    inference(resolution,[],[f85,f40])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    l1_struct_0(sK1) | ~spl4_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f83])).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    ~spl4_10 | ~spl4_7 | spl4_11 | ~spl4_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f92,f53,f102,f78,f98])).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    ( ! [X0] : (k10_relat_1(sK2,X0) = k9_relat_1(k2_funct_1(sK2),X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl4_2),
% 0.21/0.47    inference(resolution,[],[f55,f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    spl4_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f28,f88])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    l1_struct_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    (((k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f26,f25,f24,f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ? [X1] : (? [X2] : (? [X3] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (? [X3] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ? [X2] : (? [X3] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X3) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ? [X3] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X3) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) => (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) != k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3))))))),
% 0.21/0.47    inference(negated_conjecture,[],[f9])).
% 0.21/0.47  fof(f9,conjecture,(
% 0.21/0.47    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k7_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_tops_2)).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    spl4_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f29,f83])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    l1_struct_0(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    spl4_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f30,f78])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    v1_funct_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    spl4_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f31,f73])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    spl4_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f32,f68])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f61,plain,(
% 0.21/0.47    spl4_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f34,f58])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    spl4_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f35,f53])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    v2_funct_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ~spl4_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f36,f48])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (9979)------------------------------
% 0.21/0.47  % (9979)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (9979)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (9979)Memory used [KB]: 6396
% 0.21/0.47  % (9979)Time elapsed: 0.051 s
% 0.21/0.47  % (9979)------------------------------
% 0.21/0.47  % (9979)------------------------------
% 0.21/0.47  % (9971)Success in time 0.115 s
%------------------------------------------------------------------------------
