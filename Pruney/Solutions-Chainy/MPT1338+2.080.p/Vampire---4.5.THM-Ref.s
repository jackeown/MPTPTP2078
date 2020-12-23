%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:12 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  211 ( 400 expanded)
%              Number of leaves         :   50 ( 175 expanded)
%              Depth                    :   14
%              Number of atoms          :  714 (1357 expanded)
%              Number of equality atoms :  146 ( 320 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f470,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f70,f75,f80,f85,f105,f110,f115,f120,f125,f145,f152,f179,f184,f198,f202,f209,f214,f233,f234,f235,f256,f294,f299,f317,f344,f361,f389,f407,f422,f448,f458,f459,f469])).

fof(f469,plain,
    ( ~ spl3_20
    | ~ spl3_50
    | spl3_52 ),
    inference(avatar_contradiction_clause,[],[f468])).

fof(f468,plain,
    ( $false
    | ~ spl3_20
    | ~ spl3_50
    | spl3_52 ),
    inference(subsumption_resolution,[],[f435,f447])).

fof(f447,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | spl3_52 ),
    inference(avatar_component_clause,[],[f445])).

fof(f445,plain,
    ( spl3_52
  <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f435,plain,
    ( k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_20
    | ~ spl3_50 ),
    inference(forward_demodulation,[],[f428,f193])).

fof(f193,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl3_20
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f428,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_50 ),
    inference(resolution,[],[f421,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f421,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_50 ),
    inference(avatar_component_clause,[],[f419])).

fof(f419,plain,
    ( spl3_50
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f459,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_struct_0(sK1) != u1_struct_0(sK1)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_funct_1(sK2) != k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f458,plain,
    ( spl3_54
    | ~ spl3_22
    | ~ spl3_50 ),
    inference(avatar_split_clause,[],[f434,f419,f206,f455])).

fof(f455,plain,
    ( spl3_54
  <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f206,plain,
    ( spl3_22
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f434,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_22
    | ~ spl3_50 ),
    inference(forward_demodulation,[],[f427,f208])).

fof(f208,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f206])).

fof(f427,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_50 ),
    inference(resolution,[],[f421,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f448,plain,
    ( ~ spl3_52
    | spl3_46
    | ~ spl3_48 ),
    inference(avatar_split_clause,[],[f410,f404,f386,f445])).

fof(f386,plain,
    ( spl3_46
  <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f404,plain,
    ( spl3_48
  <=> k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f410,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | spl3_46
    | ~ spl3_48 ),
    inference(superposition,[],[f388,f406])).

fof(f406,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f404])).

fof(f388,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | spl3_46 ),
    inference(avatar_component_clause,[],[f386])).

fof(f422,plain,
    ( spl3_50
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_25
    | ~ spl3_26
    | ~ spl3_33
    | ~ spl3_40 ),
    inference(avatar_split_clause,[],[f417,f341,f291,f224,f220,f149,f67,f62,f419])).

fof(f62,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f67,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f149,plain,
    ( spl3_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f220,plain,
    ( spl3_25
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f224,plain,
    ( spl3_26
  <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f291,plain,
    ( spl3_33
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f341,plain,
    ( spl3_40
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f417,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_25
    | ~ spl3_26
    | ~ spl3_33
    | ~ spl3_40 ),
    inference(forward_demodulation,[],[f416,f343])).

fof(f343,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f341])).

fof(f416,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_25
    | ~ spl3_26
    | ~ spl3_33 ),
    inference(subsumption_resolution,[],[f289,f293])).

fof(f293,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f291])).

fof(f289,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_25
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f288,f222])).

fof(f222,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f220])).

fof(f288,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_25
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f287,f226])).

fof(f226,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f224])).

fof(f287,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f286,f222])).

fof(f286,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f285,f222])).

fof(f285,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(resolution,[],[f96,f151])).

fof(f151,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f149])).

fof(f96,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ v1_funct_2(sK2,X6,X7)
        | k2_relset_1(X6,X7,sK2) != X7
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X7,X6))) )
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f90,f64])).

fof(f64,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f90,plain,
    ( ! [X6,X7] :
        ( ~ v1_funct_2(sK2,X6,X7)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ v1_funct_1(sK2)
        | k2_relset_1(X6,X7,sK2) != X7
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X7,X6))) )
    | ~ spl3_2 ),
    inference(resolution,[],[f69,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f69,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f407,plain,
    ( spl3_48
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_25
    | ~ spl3_26
    | ~ spl3_33
    | ~ spl3_40 ),
    inference(avatar_split_clause,[],[f397,f341,f291,f224,f220,f149,f67,f62,f404])).

fof(f397,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_25
    | ~ spl3_26
    | ~ spl3_33
    | ~ spl3_40 ),
    inference(forward_demodulation,[],[f396,f343])).

fof(f396,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_25
    | ~ spl3_26
    | ~ spl3_33 ),
    inference(subsumption_resolution,[],[f283,f293])).

fof(f283,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_25
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f282,f222])).

fof(f282,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_25
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f281,f226])).

fof(f281,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f280,f222])).

fof(f280,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f279,f222])).

fof(f279,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(resolution,[],[f93,f151])).

fof(f93,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | k2_relset_1(X0,X1,sK2) != X1
        | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) )
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f87,f64])).

fof(f87,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,sK2) != X1
        | ~ v1_funct_1(sK2)
        | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) )
    | ~ spl3_2 ),
    inference(resolution,[],[f69,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f389,plain,
    ( ~ spl3_46
    | ~ spl3_40
    | spl3_44 ),
    inference(avatar_split_clause,[],[f379,f358,f341,f386])).

fof(f358,plain,
    ( spl3_44
  <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f379,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | ~ spl3_40
    | spl3_44 ),
    inference(forward_demodulation,[],[f360,f343])).

fof(f360,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | spl3_44 ),
    inference(avatar_component_clause,[],[f358])).

fof(f361,plain,
    ( ~ spl3_44
    | spl3_16
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f249,f220,f172,f358])).

fof(f172,plain,
    ( spl3_16
  <=> k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f249,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | spl3_16
    | ~ spl3_25 ),
    inference(superposition,[],[f174,f222])).

fof(f174,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f172])).

fof(f344,plain,
    ( spl3_40
    | ~ spl3_18
    | ~ spl3_21
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f320,f314,f195,f181,f341])).

fof(f181,plain,
    ( spl3_18
  <=> v4_relat_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f195,plain,
    ( spl3_21
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f314,plain,
    ( spl3_35
  <=> v1_partfun1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f320,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_18
    | ~ spl3_21
    | ~ spl3_35 ),
    inference(subsumption_resolution,[],[f319,f196])).

fof(f196,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f195])).

fof(f319,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_18
    | ~ spl3_35 ),
    inference(subsumption_resolution,[],[f318,f183])).

fof(f183,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f181])).

fof(f318,plain,
    ( ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_35 ),
    inference(resolution,[],[f316,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f316,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f314])).

fof(f317,plain,
    ( spl3_35
    | ~ spl3_1
    | spl3_29
    | ~ spl3_33
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f312,f296,f291,f253,f62,f314])).

fof(f253,plain,
    ( spl3_29
  <=> v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f296,plain,
    ( spl3_34
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f312,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_1
    | spl3_29
    | ~ spl3_33
    | ~ spl3_34 ),
    inference(subsumption_resolution,[],[f311,f293])).

fof(f311,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_1
    | spl3_29
    | ~ spl3_34 ),
    inference(subsumption_resolution,[],[f302,f255])).

fof(f255,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | spl3_29 ),
    inference(avatar_component_clause,[],[f253])).

fof(f302,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_34 ),
    inference(resolution,[],[f298,f86])).

fof(f86,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1)
        | ~ v1_funct_2(sK2,X0,X1)
        | v1_partfun1(sK2,X0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f64,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f298,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f296])).

fof(f299,plain,
    ( spl3_34
    | ~ spl3_13
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f250,f220,f149,f296])).

fof(f250,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_13
    | ~ spl3_25 ),
    inference(superposition,[],[f151,f222])).

fof(f294,plain,
    ( spl3_33
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f244,f216,f117,f102,f291])).

fof(f102,plain,
    ( spl3_6
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f117,plain,
    ( spl3_9
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f216,plain,
    ( spl3_24
  <=> u1_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f244,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f242,f119])).

fof(f119,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f117])).

fof(f242,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_6
    | ~ spl3_24 ),
    inference(superposition,[],[f104,f218])).

fof(f218,plain,
    ( u1_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f216])).

fof(f104,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f102])).

fof(f256,plain,
    ( ~ spl3_29
    | spl3_12
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f251,f220,f142,f253])).

fof(f142,plain,
    ( spl3_12
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f251,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | spl3_12
    | ~ spl3_25 ),
    inference(superposition,[],[f144,f222])).

fof(f144,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f142])).

fof(f235,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_struct_0(sK1) != u1_struct_0(sK1)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f234,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_struct_0(sK1) != u1_struct_0(sK1)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f233,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_struct_0(sK1) != u1_struct_0(sK1)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | u1_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f214,plain,
    ( spl3_23
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f164,f149,f211])).

fof(f211,plain,
    ( spl3_23
  <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f164,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_13 ),
    inference(resolution,[],[f151,f53])).

fof(f209,plain,
    ( spl3_22
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f204,f195,f67,f62,f206])).

fof(f204,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_21 ),
    inference(subsumption_resolution,[],[f98,f196])).

fof(f98,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f92,f64])).

fof(f92,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f69,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f202,plain,
    ( ~ spl3_13
    | spl3_21 ),
    inference(avatar_contradiction_clause,[],[f201])).

fof(f201,plain,
    ( $false
    | ~ spl3_13
    | spl3_21 ),
    inference(subsumption_resolution,[],[f200,f48])).

fof(f48,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f200,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | ~ spl3_13
    | spl3_21 ),
    inference(resolution,[],[f199,f151])).

fof(f199,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl3_21 ),
    inference(resolution,[],[f197,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f197,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_21 ),
    inference(avatar_component_clause,[],[f195])).

fof(f198,plain,
    ( spl3_20
    | ~ spl3_21
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f97,f67,f62,f195,f191])).

fof(f97,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f91,f64])).

fof(f91,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f69,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f184,plain,
    ( spl3_18
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f162,f149,f181])).

fof(f162,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_13 ),
    inference(resolution,[],[f151,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f179,plain,
    ( ~ spl3_16
    | ~ spl3_17
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f170,f117,f107,f176,f172])).

fof(f176,plain,
    ( spl3_17
  <=> k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f107,plain,
    ( spl3_7
  <=> k2_struct_0(sK1) = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f170,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f169,f119])).

fof(f169,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f168,f109])).

fof(f109,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f107])).

fof(f168,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f167,f119])).

fof(f167,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f34,f109])).

fof(f34,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f16])).

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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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

fof(f152,plain,
    ( spl3_13
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f140,f117,f112,f107,f149])).

fof(f112,plain,
    ( spl3_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f140,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f134,f119])).

fof(f134,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f114,f109])).

fof(f114,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f112])).

fof(f145,plain,
    ( ~ spl3_12
    | spl3_3
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f133,f107,f77,f72,f142])).

fof(f72,plain,
    ( spl3_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f77,plain,
    ( spl3_4
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f133,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | spl3_3
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f132,f74])).

fof(f74,plain,
    ( ~ v2_struct_0(sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f132,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f131,f79])).

fof(f79,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f131,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_7 ),
    inference(superposition,[],[f45,f109])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f125,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f38,f122])).

fof(f122,plain,
    ( spl3_10
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f38,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f120,plain,
    ( spl3_9
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f100,f82,f117])).

fof(f82,plain,
    ( spl3_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f100,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f84,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f84,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f115,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f37,f112])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f16])).

fof(f110,plain,
    ( spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f99,f77,f107])).

fof(f99,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f79,f43])).

fof(f105,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f36,f102])).

fof(f36,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f85,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f42,f82])).

fof(f42,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f80,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f41,f77])).

fof(f41,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f75,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f40,f72])).

fof(f40,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f70,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f39,f67])).

fof(f39,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f65,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f35,f62])).

fof(f35,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:38:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (8402)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.47  % (8401)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.48  % (8409)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.48  % (8402)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (8410)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f470,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f65,f70,f75,f80,f85,f105,f110,f115,f120,f125,f145,f152,f179,f184,f198,f202,f209,f214,f233,f234,f235,f256,f294,f299,f317,f344,f361,f389,f407,f422,f448,f458,f459,f469])).
% 0.22/0.49  fof(f469,plain,(
% 0.22/0.49    ~spl3_20 | ~spl3_50 | spl3_52),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f468])).
% 0.22/0.49  fof(f468,plain,(
% 0.22/0.49    $false | (~spl3_20 | ~spl3_50 | spl3_52)),
% 0.22/0.49    inference(subsumption_resolution,[],[f435,f447])).
% 0.22/0.49  fof(f447,plain,(
% 0.22/0.49    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | spl3_52),
% 0.22/0.49    inference(avatar_component_clause,[],[f445])).
% 0.22/0.49  fof(f445,plain,(
% 0.22/0.49    spl3_52 <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 0.22/0.49  fof(f435,plain,(
% 0.22/0.49    k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_20 | ~spl3_50)),
% 0.22/0.49    inference(forward_demodulation,[],[f428,f193])).
% 0.22/0.49  fof(f193,plain,(
% 0.22/0.49    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_20),
% 0.22/0.49    inference(avatar_component_clause,[],[f191])).
% 0.22/0.49  fof(f191,plain,(
% 0.22/0.49    spl3_20 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.49  fof(f428,plain,(
% 0.22/0.49    k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_50),
% 0.22/0.49    inference(resolution,[],[f421,f52])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.49  fof(f421,plain,(
% 0.22/0.49    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl3_50),
% 0.22/0.49    inference(avatar_component_clause,[],[f419])).
% 0.22/0.49  fof(f419,plain,(
% 0.22/0.49    spl3_50 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 0.22/0.49  fof(f459,plain,(
% 0.22/0.49    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_struct_0(sK1) != u1_struct_0(sK1) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_funct_1(sK2) != k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k2_struct_0(sK0) != k1_relat_1(sK2) | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.22/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.49  fof(f458,plain,(
% 0.22/0.49    spl3_54 | ~spl3_22 | ~spl3_50),
% 0.22/0.49    inference(avatar_split_clause,[],[f434,f419,f206,f455])).
% 0.22/0.49  fof(f455,plain,(
% 0.22/0.49    spl3_54 <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 0.22/0.49  fof(f206,plain,(
% 0.22/0.49    spl3_22 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.22/0.49  fof(f434,plain,(
% 0.22/0.49    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_22 | ~spl3_50)),
% 0.22/0.49    inference(forward_demodulation,[],[f427,f208])).
% 0.22/0.49  fof(f208,plain,(
% 0.22/0.49    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_22),
% 0.22/0.49    inference(avatar_component_clause,[],[f206])).
% 0.22/0.49  fof(f427,plain,(
% 0.22/0.49    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_50),
% 0.22/0.49    inference(resolution,[],[f421,f53])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.49  fof(f448,plain,(
% 0.22/0.49    ~spl3_52 | spl3_46 | ~spl3_48),
% 0.22/0.49    inference(avatar_split_clause,[],[f410,f404,f386,f445])).
% 0.22/0.49  fof(f386,plain,(
% 0.22/0.49    spl3_46 <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.22/0.49  fof(f404,plain,(
% 0.22/0.49    spl3_48 <=> k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.22/0.49  fof(f410,plain,(
% 0.22/0.49    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (spl3_46 | ~spl3_48)),
% 0.22/0.49    inference(superposition,[],[f388,f406])).
% 0.22/0.49  fof(f406,plain,(
% 0.22/0.49    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_48),
% 0.22/0.49    inference(avatar_component_clause,[],[f404])).
% 0.22/0.49  fof(f388,plain,(
% 0.22/0.49    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | spl3_46),
% 0.22/0.49    inference(avatar_component_clause,[],[f386])).
% 0.22/0.49  fof(f422,plain,(
% 0.22/0.49    spl3_50 | ~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_25 | ~spl3_26 | ~spl3_33 | ~spl3_40),
% 0.22/0.49    inference(avatar_split_clause,[],[f417,f341,f291,f224,f220,f149,f67,f62,f419])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    spl3_1 <=> v1_funct_1(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    spl3_2 <=> v2_funct_1(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.49  fof(f149,plain,(
% 0.22/0.49    spl3_13 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.49  fof(f220,plain,(
% 0.22/0.49    spl3_25 <=> k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.22/0.49  fof(f224,plain,(
% 0.22/0.49    spl3_26 <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.22/0.49  fof(f291,plain,(
% 0.22/0.49    spl3_33 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.22/0.49  fof(f341,plain,(
% 0.22/0.49    spl3_40 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.22/0.49  fof(f417,plain,(
% 0.22/0.49    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_25 | ~spl3_26 | ~spl3_33 | ~spl3_40)),
% 0.22/0.49    inference(forward_demodulation,[],[f416,f343])).
% 0.22/0.49  fof(f343,plain,(
% 0.22/0.49    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_40),
% 0.22/0.49    inference(avatar_component_clause,[],[f341])).
% 0.22/0.49  fof(f416,plain,(
% 0.22/0.49    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_25 | ~spl3_26 | ~spl3_33)),
% 0.22/0.49    inference(subsumption_resolution,[],[f289,f293])).
% 0.22/0.49  fof(f293,plain,(
% 0.22/0.49    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~spl3_33),
% 0.22/0.49    inference(avatar_component_clause,[],[f291])).
% 0.22/0.49  fof(f289,plain,(
% 0.22/0.49    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_25 | ~spl3_26)),
% 0.22/0.49    inference(forward_demodulation,[],[f288,f222])).
% 0.22/0.49  fof(f222,plain,(
% 0.22/0.49    k2_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_25),
% 0.22/0.49    inference(avatar_component_clause,[],[f220])).
% 0.22/0.49  fof(f288,plain,(
% 0.22/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_25 | ~spl3_26)),
% 0.22/0.49    inference(subsumption_resolution,[],[f287,f226])).
% 0.22/0.49  fof(f226,plain,(
% 0.22/0.49    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_26),
% 0.22/0.49    inference(avatar_component_clause,[],[f224])).
% 0.22/0.49  fof(f287,plain,(
% 0.22/0.49    k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_25)),
% 0.22/0.49    inference(forward_demodulation,[],[f286,f222])).
% 0.22/0.49  fof(f286,plain,(
% 0.22/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_25)),
% 0.22/0.49    inference(forward_demodulation,[],[f285,f222])).
% 0.22/0.49  fof(f285,plain,(
% 0.22/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_1 | ~spl3_2 | ~spl3_13)),
% 0.22/0.49    inference(resolution,[],[f96,f151])).
% 0.22/0.49  fof(f151,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_13),
% 0.22/0.49    inference(avatar_component_clause,[],[f149])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    ( ! [X6,X7] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_2(sK2,X6,X7) | k2_relset_1(X6,X7,sK2) != X7 | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X7,X6)))) ) | (~spl3_1 | ~spl3_2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f90,f64])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    v1_funct_1(sK2) | ~spl3_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f62])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    ( ! [X6,X7] : (~v1_funct_2(sK2,X6,X7) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_1(sK2) | k2_relset_1(X6,X7,sK2) != X7 | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X7,X6)))) ) | ~spl3_2),
% 0.22/0.49    inference(resolution,[],[f69,f58])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.49    inference(flattening,[],[f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    v2_funct_1(sK2) | ~spl3_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f67])).
% 0.22/0.49  fof(f407,plain,(
% 0.22/0.49    spl3_48 | ~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_25 | ~spl3_26 | ~spl3_33 | ~spl3_40),
% 0.22/0.49    inference(avatar_split_clause,[],[f397,f341,f291,f224,f220,f149,f67,f62,f404])).
% 0.22/0.49  fof(f397,plain,(
% 0.22/0.49    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_25 | ~spl3_26 | ~spl3_33 | ~spl3_40)),
% 0.22/0.49    inference(forward_demodulation,[],[f396,f343])).
% 0.22/0.49  fof(f396,plain,(
% 0.22/0.49    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_25 | ~spl3_26 | ~spl3_33)),
% 0.22/0.49    inference(subsumption_resolution,[],[f283,f293])).
% 0.22/0.49  fof(f283,plain,(
% 0.22/0.49    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_25 | ~spl3_26)),
% 0.22/0.49    inference(forward_demodulation,[],[f282,f222])).
% 0.22/0.49  fof(f282,plain,(
% 0.22/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_25 | ~spl3_26)),
% 0.22/0.49    inference(subsumption_resolution,[],[f281,f226])).
% 0.22/0.49  fof(f281,plain,(
% 0.22/0.49    k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_25)),
% 0.22/0.49    inference(forward_demodulation,[],[f280,f222])).
% 0.22/0.49  fof(f280,plain,(
% 0.22/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13 | ~spl3_25)),
% 0.22/0.49    inference(forward_demodulation,[],[f279,f222])).
% 0.22/0.49  fof(f279,plain,(
% 0.22/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_13)),
% 0.22/0.49    inference(resolution,[],[f93,f151])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k2_relset_1(X0,X1,sK2) != X1 | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)) ) | (~spl3_1 | ~spl3_2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f87,f64])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1 | ~v1_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)) ) | ~spl3_2),
% 0.22/0.49    inference(resolution,[],[f69,f59])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.49    inference(flattening,[],[f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.49    inference(ennf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.22/0.49  fof(f389,plain,(
% 0.22/0.49    ~spl3_46 | ~spl3_40 | spl3_44),
% 0.22/0.49    inference(avatar_split_clause,[],[f379,f358,f341,f386])).
% 0.22/0.49  fof(f358,plain,(
% 0.22/0.49    spl3_44 <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 0.22/0.49  fof(f379,plain,(
% 0.22/0.49    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | (~spl3_40 | spl3_44)),
% 0.22/0.49    inference(forward_demodulation,[],[f360,f343])).
% 0.22/0.49  fof(f360,plain,(
% 0.22/0.49    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | spl3_44),
% 0.22/0.49    inference(avatar_component_clause,[],[f358])).
% 0.22/0.49  fof(f361,plain,(
% 0.22/0.49    ~spl3_44 | spl3_16 | ~spl3_25),
% 0.22/0.49    inference(avatar_split_clause,[],[f249,f220,f172,f358])).
% 0.22/0.49  fof(f172,plain,(
% 0.22/0.49    spl3_16 <=> k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.49  fof(f249,plain,(
% 0.22/0.49    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | (spl3_16 | ~spl3_25)),
% 0.22/0.49    inference(superposition,[],[f174,f222])).
% 0.22/0.49  fof(f174,plain,(
% 0.22/0.49    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | spl3_16),
% 0.22/0.49    inference(avatar_component_clause,[],[f172])).
% 0.22/0.49  fof(f344,plain,(
% 0.22/0.49    spl3_40 | ~spl3_18 | ~spl3_21 | ~spl3_35),
% 0.22/0.49    inference(avatar_split_clause,[],[f320,f314,f195,f181,f341])).
% 0.22/0.49  fof(f181,plain,(
% 0.22/0.49    spl3_18 <=> v4_relat_1(sK2,k2_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.49  fof(f195,plain,(
% 0.22/0.49    spl3_21 <=> v1_relat_1(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.49  fof(f314,plain,(
% 0.22/0.49    spl3_35 <=> v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.22/0.49  fof(f320,plain,(
% 0.22/0.49    k2_struct_0(sK0) = k1_relat_1(sK2) | (~spl3_18 | ~spl3_21 | ~spl3_35)),
% 0.22/0.49    inference(subsumption_resolution,[],[f319,f196])).
% 0.22/0.49  fof(f196,plain,(
% 0.22/0.49    v1_relat_1(sK2) | ~spl3_21),
% 0.22/0.49    inference(avatar_component_clause,[],[f195])).
% 0.22/0.49  fof(f319,plain,(
% 0.22/0.49    k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2) | (~spl3_18 | ~spl3_35)),
% 0.22/0.49    inference(subsumption_resolution,[],[f318,f183])).
% 0.22/0.49  fof(f183,plain,(
% 0.22/0.49    v4_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_18),
% 0.22/0.49    inference(avatar_component_clause,[],[f181])).
% 0.22/0.49  fof(f318,plain,(
% 0.22/0.49    ~v4_relat_1(sK2,k2_struct_0(sK0)) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl3_35),
% 0.22/0.49    inference(resolution,[],[f316,f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.22/0.49  fof(f316,plain,(
% 0.22/0.49    v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl3_35),
% 0.22/0.49    inference(avatar_component_clause,[],[f314])).
% 0.22/0.49  fof(f317,plain,(
% 0.22/0.49    spl3_35 | ~spl3_1 | spl3_29 | ~spl3_33 | ~spl3_34),
% 0.22/0.49    inference(avatar_split_clause,[],[f312,f296,f291,f253,f62,f314])).
% 0.22/0.49  fof(f253,plain,(
% 0.22/0.49    spl3_29 <=> v1_xboole_0(k2_relat_1(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.22/0.49  fof(f296,plain,(
% 0.22/0.49    spl3_34 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.22/0.49  fof(f312,plain,(
% 0.22/0.49    v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_1 | spl3_29 | ~spl3_33 | ~spl3_34)),
% 0.22/0.49    inference(subsumption_resolution,[],[f311,f293])).
% 0.22/0.49  fof(f311,plain,(
% 0.22/0.49    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_1 | spl3_29 | ~spl3_34)),
% 0.22/0.49    inference(subsumption_resolution,[],[f302,f255])).
% 0.22/0.49  fof(f255,plain,(
% 0.22/0.49    ~v1_xboole_0(k2_relat_1(sK2)) | spl3_29),
% 0.22/0.49    inference(avatar_component_clause,[],[f253])).
% 0.22/0.49  fof(f302,plain,(
% 0.22/0.49    v1_xboole_0(k2_relat_1(sK2)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_1 | ~spl3_34)),
% 0.22/0.49    inference(resolution,[],[f298,f86])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(sK2,X0,X1) | v1_partfun1(sK2,X0)) ) | ~spl3_1),
% 0.22/0.49    inference(resolution,[],[f64,f49])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.49    inference(flattening,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.22/0.49  fof(f298,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~spl3_34),
% 0.22/0.49    inference(avatar_component_clause,[],[f296])).
% 0.22/0.49  fof(f299,plain,(
% 0.22/0.49    spl3_34 | ~spl3_13 | ~spl3_25),
% 0.22/0.49    inference(avatar_split_clause,[],[f250,f220,f149,f296])).
% 0.22/0.49  fof(f250,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | (~spl3_13 | ~spl3_25)),
% 0.22/0.49    inference(superposition,[],[f151,f222])).
% 0.22/0.49  fof(f294,plain,(
% 0.22/0.49    spl3_33 | ~spl3_6 | ~spl3_9 | ~spl3_24),
% 0.22/0.49    inference(avatar_split_clause,[],[f244,f216,f117,f102,f291])).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    spl3_6 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.49  fof(f117,plain,(
% 0.22/0.49    spl3_9 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.49  fof(f216,plain,(
% 0.22/0.49    spl3_24 <=> u1_struct_0(sK1) = k2_relat_1(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.22/0.49  fof(f244,plain,(
% 0.22/0.49    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_6 | ~spl3_9 | ~spl3_24)),
% 0.22/0.49    inference(forward_demodulation,[],[f242,f119])).
% 0.22/0.49  fof(f119,plain,(
% 0.22/0.49    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f117])).
% 0.22/0.49  fof(f242,plain,(
% 0.22/0.49    v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_6 | ~spl3_24)),
% 0.22/0.49    inference(superposition,[],[f104,f218])).
% 0.22/0.49  fof(f218,plain,(
% 0.22/0.49    u1_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_24),
% 0.22/0.49    inference(avatar_component_clause,[],[f216])).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f102])).
% 0.22/0.49  fof(f256,plain,(
% 0.22/0.49    ~spl3_29 | spl3_12 | ~spl3_25),
% 0.22/0.49    inference(avatar_split_clause,[],[f251,f220,f142,f253])).
% 0.22/0.49  fof(f142,plain,(
% 0.22/0.49    spl3_12 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.49  fof(f251,plain,(
% 0.22/0.49    ~v1_xboole_0(k2_relat_1(sK2)) | (spl3_12 | ~spl3_25)),
% 0.22/0.49    inference(superposition,[],[f144,f222])).
% 0.22/0.49  fof(f144,plain,(
% 0.22/0.49    ~v1_xboole_0(k2_struct_0(sK1)) | spl3_12),
% 0.22/0.49    inference(avatar_component_clause,[],[f142])).
% 0.22/0.49  fof(f235,plain,(
% 0.22/0.49    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_struct_0(sK1) != u1_struct_0(sK1) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.22/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.49  fof(f234,plain,(
% 0.22/0.49    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_struct_0(sK1) != u1_struct_0(sK1) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.22/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.49  fof(f233,plain,(
% 0.22/0.49    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_struct_0(sK1) != u1_struct_0(sK1) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | u1_struct_0(sK1) = k2_relat_1(sK2)),
% 0.22/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.49  fof(f214,plain,(
% 0.22/0.49    spl3_23 | ~spl3_13),
% 0.22/0.49    inference(avatar_split_clause,[],[f164,f149,f211])).
% 0.22/0.49  fof(f211,plain,(
% 0.22/0.49    spl3_23 <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.49  fof(f164,plain,(
% 0.22/0.49    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_13),
% 0.22/0.49    inference(resolution,[],[f151,f53])).
% 0.22/0.49  fof(f209,plain,(
% 0.22/0.49    spl3_22 | ~spl3_1 | ~spl3_2 | ~spl3_21),
% 0.22/0.49    inference(avatar_split_clause,[],[f204,f195,f67,f62,f206])).
% 0.22/0.49  fof(f204,plain,(
% 0.22/0.49    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_21)),
% 0.22/0.49    inference(subsumption_resolution,[],[f98,f196])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f92,f64])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_2),
% 0.22/0.49    inference(resolution,[],[f69,f47])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.49  fof(f202,plain,(
% 0.22/0.49    ~spl3_13 | spl3_21),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f201])).
% 0.22/0.49  fof(f201,plain,(
% 0.22/0.49    $false | (~spl3_13 | spl3_21)),
% 0.22/0.49    inference(subsumption_resolution,[],[f200,f48])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.49  fof(f200,plain,(
% 0.22/0.49    ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | (~spl3_13 | spl3_21)),
% 0.22/0.49    inference(resolution,[],[f199,f151])).
% 0.22/0.49  fof(f199,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl3_21),
% 0.22/0.49    inference(resolution,[],[f197,f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.49  fof(f197,plain,(
% 0.22/0.49    ~v1_relat_1(sK2) | spl3_21),
% 0.22/0.49    inference(avatar_component_clause,[],[f195])).
% 0.22/0.49  fof(f198,plain,(
% 0.22/0.49    spl3_20 | ~spl3_21 | ~spl3_1 | ~spl3_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f97,f67,f62,f195,f191])).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2)),
% 0.22/0.49    inference(subsumption_resolution,[],[f91,f64])).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_2),
% 0.22/0.49    inference(resolution,[],[f69,f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f184,plain,(
% 0.22/0.49    spl3_18 | ~spl3_13),
% 0.22/0.49    inference(avatar_split_clause,[],[f162,f149,f181])).
% 0.22/0.49  fof(f162,plain,(
% 0.22/0.49    v4_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_13),
% 0.22/0.49    inference(resolution,[],[f151,f54])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.49  fof(f179,plain,(
% 0.22/0.49    ~spl3_16 | ~spl3_17 | ~spl3_7 | ~spl3_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f170,f117,f107,f176,f172])).
% 0.22/0.49  fof(f176,plain,(
% 0.22/0.49    spl3_17 <=> k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.49  fof(f107,plain,(
% 0.22/0.49    spl3_7 <=> k2_struct_0(sK1) = u1_struct_0(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.49  fof(f170,plain,(
% 0.22/0.49    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | (~spl3_7 | ~spl3_9)),
% 0.22/0.49    inference(forward_demodulation,[],[f169,f119])).
% 0.22/0.49  fof(f169,plain,(
% 0.22/0.49    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | (~spl3_7 | ~spl3_9)),
% 0.22/0.49    inference(forward_demodulation,[],[f168,f109])).
% 0.22/0.49  fof(f109,plain,(
% 0.22/0.49    k2_struct_0(sK1) = u1_struct_0(sK1) | ~spl3_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f107])).
% 0.22/0.49  fof(f168,plain,(
% 0.22/0.49    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | (~spl3_7 | ~spl3_9)),
% 0.22/0.49    inference(forward_demodulation,[],[f167,f119])).
% 0.22/0.49  fof(f167,plain,(
% 0.22/0.49    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~spl3_7),
% 0.22/0.49    inference(forward_demodulation,[],[f34,f109])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,negated_conjecture,(
% 0.22/0.49    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.22/0.49    inference(negated_conjecture,[],[f13])).
% 0.22/0.49  fof(f13,conjecture,(
% 0.22/0.49    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).
% 0.22/0.49  fof(f152,plain,(
% 0.22/0.49    spl3_13 | ~spl3_7 | ~spl3_8 | ~spl3_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f140,f117,f112,f107,f149])).
% 0.22/0.49  fof(f112,plain,(
% 0.22/0.49    spl3_8 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.49  fof(f140,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_7 | ~spl3_8 | ~spl3_9)),
% 0.22/0.49    inference(forward_demodulation,[],[f134,f119])).
% 0.22/0.49  fof(f134,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_7 | ~spl3_8)),
% 0.22/0.49    inference(forward_demodulation,[],[f114,f109])).
% 0.22/0.49  fof(f114,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f112])).
% 0.22/0.49  fof(f145,plain,(
% 0.22/0.49    ~spl3_12 | spl3_3 | ~spl3_4 | ~spl3_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f133,f107,f77,f72,f142])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    spl3_3 <=> v2_struct_0(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    spl3_4 <=> l1_struct_0(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.49  fof(f133,plain,(
% 0.22/0.49    ~v1_xboole_0(k2_struct_0(sK1)) | (spl3_3 | ~spl3_4 | ~spl3_7)),
% 0.22/0.49    inference(subsumption_resolution,[],[f132,f74])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    ~v2_struct_0(sK1) | spl3_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f72])).
% 0.22/0.49  fof(f132,plain,(
% 0.22/0.49    ~v1_xboole_0(k2_struct_0(sK1)) | v2_struct_0(sK1) | (~spl3_4 | ~spl3_7)),
% 0.22/0.49    inference(subsumption_resolution,[],[f131,f79])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    l1_struct_0(sK1) | ~spl3_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f77])).
% 0.22/0.49  fof(f131,plain,(
% 0.22/0.49    ~v1_xboole_0(k2_struct_0(sK1)) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl3_7),
% 0.22/0.49    inference(superposition,[],[f45,f109])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,axiom,(
% 0.22/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.49  fof(f125,plain,(
% 0.22/0.49    spl3_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f38,f122])).
% 0.22/0.49  fof(f122,plain,(
% 0.22/0.49    spl3_10 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f120,plain,(
% 0.22/0.49    spl3_9 | ~spl3_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f100,f82,f117])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    spl3_5 <=> l1_struct_0(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_5),
% 0.22/0.49    inference(resolution,[],[f84,f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    l1_struct_0(sK0) | ~spl3_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f82])).
% 0.22/0.49  fof(f115,plain,(
% 0.22/0.49    spl3_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f37,f112])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    spl3_7 | ~spl3_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f99,f77,f107])).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    k2_struct_0(sK1) = u1_struct_0(sK1) | ~spl3_4),
% 0.22/0.49    inference(resolution,[],[f79,f43])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    spl3_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f36,f102])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    spl3_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f42,f82])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    l1_struct_0(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    spl3_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f41,f77])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    l1_struct_0(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    ~spl3_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f40,f72])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ~v2_struct_0(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    spl3_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f39,f67])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    v2_funct_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    spl3_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f35,f62])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    v1_funct_1(sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (8402)------------------------------
% 0.22/0.49  % (8402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (8402)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (8402)Memory used [KB]: 11001
% 0.22/0.49  % (8402)Time elapsed: 0.062 s
% 0.22/0.49  % (8402)------------------------------
% 0.22/0.49  % (8402)------------------------------
% 0.22/0.49  % (8409)Refutation not found, incomplete strategy% (8409)------------------------------
% 0.22/0.49  % (8409)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (8398)Success in time 0.129 s
%------------------------------------------------------------------------------
