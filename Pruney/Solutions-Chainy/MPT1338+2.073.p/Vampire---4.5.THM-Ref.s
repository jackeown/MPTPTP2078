%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  284 ( 608 expanded)
%              Number of leaves         :   75 ( 287 expanded)
%              Depth                    :   13
%              Number of atoms          :  876 (2240 expanded)
%              Number of equality atoms :  182 ( 588 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f798,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f98,f103,f108,f113,f118,f135,f140,f176,f182,f188,f194,f200,f241,f242,f243,f244,f245,f251,f262,f269,f274,f282,f318,f346,f368,f377,f385,f424,f429,f434,f464,f466,f489,f495,f511,f517,f576,f582,f623,f628,f633,f710,f725,f746,f751,f788,f790,f791,f794,f795])).

fof(f795,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_struct_0(sK0) != u1_struct_0(sK0)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f794,plain,
    ( k4_relat_1(sK2) != k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_struct_0(sK0) != u1_struct_0(sK0)
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | k1_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != k2_relat_1(k4_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)))
    | k2_relat_1(sK2) != k2_relat_1(k4_relat_1(k4_relat_1(sK2)))
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK1) = k1_relat_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f791,plain,
    ( k4_relat_1(sK2) != k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | k2_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != k1_relat_1(k4_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)))
    | k1_relat_1(sK2) != k1_relat_1(k4_relat_1(k4_relat_1(sK2)))
    | k1_relat_1(sK2) = k2_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f790,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k4_relat_1(sK2) != k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_struct_0(sK0) != u1_struct_0(sK0)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f788,plain,
    ( spl3_96
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_38
    | ~ spl3_78
    | ~ spl3_79
    | ~ spl3_80 ),
    inference(avatar_split_clause,[],[f783,f630,f625,f620,f315,f100,f80,f785])).

fof(f785,plain,
    ( spl3_96
  <=> k4_relat_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_96])])).

fof(f80,plain,
    ( spl3_3
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f100,plain,
    ( spl3_7
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f315,plain,
    ( spl3_38
  <=> k4_relat_1(sK2) = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f620,plain,
    ( spl3_78
  <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).

fof(f625,plain,
    ( spl3_79
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_79])])).

fof(f630,plain,
    ( spl3_80
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_80])])).

fof(f783,plain,
    ( k4_relat_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_38
    | ~ spl3_78
    | ~ spl3_79
    | ~ spl3_80 ),
    inference(forward_demodulation,[],[f781,f317])).

fof(f317,plain,
    ( k4_relat_1(sK2) = k2_funct_1(sK2)
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f315])).

fof(f781,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_78
    | ~ spl3_79
    | ~ spl3_80 ),
    inference(unit_resulting_resolution,[],[f102,f82,f632,f627,f622,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f622,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_78 ),
    inference(avatar_component_clause,[],[f620])).

fof(f627,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_79 ),
    inference(avatar_component_clause,[],[f625])).

fof(f632,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_80 ),
    inference(avatar_component_clause,[],[f630])).

fof(f82,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f102,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f100])).

fof(f751,plain,
    ( spl3_94
    | ~ spl3_83 ),
    inference(avatar_split_clause,[],[f738,f645,f748])).

fof(f748,plain,
    ( spl3_94
  <=> k1_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) = k2_relat_1(k4_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_94])])).

fof(f645,plain,
    ( spl3_83
  <=> v1_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).

fof(f738,plain,
    ( k1_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) = k2_relat_1(k4_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)))
    | ~ spl3_83 ),
    inference(unit_resulting_resolution,[],[f646,f53])).

fof(f53,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f646,plain,
    ( v1_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | ~ spl3_83 ),
    inference(avatar_component_clause,[],[f645])).

fof(f746,plain,
    ( spl3_93
    | ~ spl3_83 ),
    inference(avatar_split_clause,[],[f739,f645,f743])).

fof(f743,plain,
    ( spl3_93
  <=> k2_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) = k1_relat_1(k4_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_93])])).

fof(f739,plain,
    ( k2_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) = k1_relat_1(k4_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)))
    | ~ spl3_83 ),
    inference(unit_resulting_resolution,[],[f646,f52])).

% (31501)Refutation not found, incomplete strategy% (31501)------------------------------
% (31501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f52,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

% (31501)Termination reason: Refutation not found, incomplete strategy

% (31501)Memory used [KB]: 10618
% (31501)Time elapsed: 0.087 s
% (31501)------------------------------
% (31501)------------------------------
fof(f725,plain,
    ( ~ spl3_91
    | ~ spl3_92
    | spl3_23
    | ~ spl3_47
    | ~ spl3_73 ),
    inference(avatar_split_clause,[],[f716,f579,f380,f212,f722,f718])).

fof(f718,plain,
    ( spl3_91
  <=> k1_relat_1(sK2) = k2_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_91])])).

fof(f722,plain,
    ( spl3_92
  <=> m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_92])])).

fof(f212,plain,
    ( spl3_23
  <=> k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f380,plain,
    ( spl3_47
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f579,plain,
    ( spl3_73
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).

fof(f716,plain,
    ( ~ m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | k1_relat_1(sK2) != k2_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | spl3_23
    | ~ spl3_47
    | ~ spl3_73 ),
    inference(forward_demodulation,[],[f715,f382])).

fof(f382,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f380])).

% (31494)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f715,plain,
    ( ~ m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2))))
    | k1_relat_1(sK2) != k2_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | spl3_23
    | ~ spl3_47
    | ~ spl3_73 ),
    inference(forward_demodulation,[],[f714,f581])).

fof(f581,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_73 ),
    inference(avatar_component_clause,[],[f579])).

fof(f714,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | ~ m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | spl3_23
    | ~ spl3_47
    | ~ spl3_73 ),
    inference(forward_demodulation,[],[f713,f581])).

fof(f713,plain,
    ( k2_struct_0(sK0) != k2_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | ~ m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | spl3_23
    | ~ spl3_47 ),
    inference(forward_demodulation,[],[f372,f382])).

fof(f372,plain,
    ( k2_struct_0(sK0) != k2_relat_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | spl3_23 ),
    inference(superposition,[],[f214,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f214,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl3_23 ),
    inference(avatar_component_clause,[],[f212])).

fof(f710,plain,
    ( ~ spl3_3
    | ~ spl3_7
    | ~ spl3_34
    | ~ spl3_38
    | ~ spl3_78
    | ~ spl3_79
    | ~ spl3_80
    | spl3_83 ),
    inference(avatar_contradiction_clause,[],[f709])).

fof(f709,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_34
    | ~ spl3_38
    | ~ spl3_78
    | ~ spl3_79
    | ~ spl3_80
    | spl3_83 ),
    inference(subsumption_resolution,[],[f708,f295])).

fof(f295,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl3_34
  <=> v1_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f708,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_38
    | ~ spl3_78
    | ~ spl3_79
    | ~ spl3_80
    | spl3_83 ),
    inference(forward_demodulation,[],[f707,f317])).

fof(f707,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_78
    | ~ spl3_79
    | ~ spl3_80
    | spl3_83 ),
    inference(subsumption_resolution,[],[f706,f102])).

fof(f706,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_3
    | ~ spl3_78
    | ~ spl3_79
    | ~ spl3_80
    | spl3_83 ),
    inference(subsumption_resolution,[],[f705,f632])).

fof(f705,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_3
    | ~ spl3_78
    | ~ spl3_79
    | spl3_83 ),
    inference(subsumption_resolution,[],[f704,f627])).

fof(f704,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_3
    | ~ spl3_78
    | spl3_83 ),
    inference(subsumption_resolution,[],[f703,f622])).

fof(f703,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_3
    | spl3_83 ),
    inference(subsumption_resolution,[],[f701,f82])).

fof(f701,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | spl3_83 ),
    inference(superposition,[],[f647,f68])).

fof(f647,plain,
    ( ~ v1_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | spl3_83 ),
    inference(avatar_component_clause,[],[f645])).

fof(f633,plain,
    ( spl3_80
    | ~ spl3_53
    | ~ spl3_73 ),
    inference(avatar_split_clause,[],[f590,f579,f426,f630])).

fof(f426,plain,
    ( spl3_53
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f590,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_53
    | ~ spl3_73 ),
    inference(backward_demodulation,[],[f428,f581])).

fof(f428,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_53 ),
    inference(avatar_component_clause,[],[f426])).

fof(f628,plain,
    ( spl3_79
    | ~ spl3_52
    | ~ spl3_73 ),
    inference(avatar_split_clause,[],[f589,f579,f421,f625])).

fof(f421,plain,
    ( spl3_52
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f589,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_52
    | ~ spl3_73 ),
    inference(backward_demodulation,[],[f423,f581])).

fof(f423,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_52 ),
    inference(avatar_component_clause,[],[f421])).

fof(f623,plain,
    ( spl3_78
    | ~ spl3_51
    | ~ spl3_73 ),
    inference(avatar_split_clause,[],[f588,f579,f416,f620])).

fof(f416,plain,
    ( spl3_51
  <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f588,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_51
    | ~ spl3_73 ),
    inference(backward_demodulation,[],[f418,f581])).

fof(f418,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_51 ),
    inference(avatar_component_clause,[],[f416])).

fof(f582,plain,
    ( spl3_73
    | ~ spl3_29
    | ~ spl3_32
    | ~ spl3_72 ),
    inference(avatar_split_clause,[],[f577,f569,f278,f257,f579])).

fof(f257,plain,
    ( spl3_29
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f278,plain,
    ( spl3_32
  <=> v4_relat_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f569,plain,
    ( spl3_72
  <=> v1_partfun1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).

fof(f577,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_29
    | ~ spl3_32
    | ~ spl3_72 ),
    inference(unit_resulting_resolution,[],[f259,f280,f571,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f571,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_72 ),
    inference(avatar_component_clause,[],[f569])).

fof(f280,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f278])).

fof(f259,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f257])).

fof(f576,plain,
    ( spl3_72
    | ~ spl3_7
    | ~ spl3_52
    | ~ spl3_53
    | spl3_54 ),
    inference(avatar_split_clause,[],[f575,f431,f426,f421,f100,f569])).

fof(f431,plain,
    ( spl3_54
  <=> v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f575,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_7
    | ~ spl3_52
    | ~ spl3_53
    | spl3_54 ),
    inference(subsumption_resolution,[],[f574,f433])).

fof(f433,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | spl3_54 ),
    inference(avatar_component_clause,[],[f431])).

fof(f574,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | v1_xboole_0(k2_relat_1(sK2))
    | ~ spl3_7
    | ~ spl3_52
    | ~ spl3_53 ),
    inference(subsumption_resolution,[],[f573,f102])).

fof(f573,plain,
    ( ~ v1_funct_1(sK2)
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | v1_xboole_0(k2_relat_1(sK2))
    | ~ spl3_52
    | ~ spl3_53 ),
    inference(subsumption_resolution,[],[f566,f428])).

fof(f566,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | v1_xboole_0(k2_relat_1(sK2))
    | ~ spl3_52 ),
    inference(resolution,[],[f59,f423])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_partfun1(X2,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f517,plain,
    ( spl3_64
    | ~ spl3_30
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f512,f294,f266,f514])).

fof(f514,plain,
    ( spl3_64
  <=> k2_relat_1(sK2) = k2_relat_1(k4_relat_1(k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f266,plain,
    ( spl3_30
  <=> k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f512,plain,
    ( k2_relat_1(sK2) = k2_relat_1(k4_relat_1(k4_relat_1(sK2)))
    | ~ spl3_30
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f504,f268])).

fof(f268,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f266])).

fof(f504,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(k4_relat_1(k4_relat_1(sK2)))
    | ~ spl3_34 ),
    inference(unit_resulting_resolution,[],[f295,f53])).

fof(f511,plain,
    ( spl3_63
    | ~ spl3_31
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f506,f294,f271,f508])).

fof(f508,plain,
    ( spl3_63
  <=> k1_relat_1(sK2) = k1_relat_1(k4_relat_1(k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).

fof(f271,plain,
    ( spl3_31
  <=> k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f506,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k4_relat_1(k4_relat_1(sK2)))
    | ~ spl3_31
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f505,f273])).

fof(f273,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f271])).

fof(f505,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(k4_relat_1(k4_relat_1(sK2)))
    | ~ spl3_34 ),
    inference(unit_resulting_resolution,[],[f295,f52])).

fof(f495,plain,
    ( spl3_61
    | ~ spl3_52
    | ~ spl3_60 ),
    inference(avatar_split_clause,[],[f487,f461,f421,f492])).

fof(f492,plain,
    ( spl3_61
  <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f461,plain,
    ( spl3_60
  <=> k4_relat_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f487,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ spl3_52
    | ~ spl3_60 ),
    inference(forward_demodulation,[],[f481,f463])).

fof(f463,plain,
    ( k4_relat_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_60 ),
    inference(avatar_component_clause,[],[f461])).

fof(f481,plain,
    ( m1_subset_1(k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ spl3_52 ),
    inference(unit_resulting_resolution,[],[f423,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_relset_1)).

fof(f489,plain,
    ( spl3_34
    | ~ spl3_52
    | ~ spl3_60 ),
    inference(avatar_contradiction_clause,[],[f488])).

fof(f488,plain,
    ( $false
    | spl3_34
    | ~ spl3_52
    | ~ spl3_60 ),
    inference(subsumption_resolution,[],[f487,f306])).

% (31491)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f306,plain,
    ( ! [X0,X1] : ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl3_34 ),
    inference(unit_resulting_resolution,[],[f57,f296,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f296,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | spl3_34 ),
    inference(avatar_component_clause,[],[f294])).

fof(f57,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f466,plain,
    ( spl3_51
    | ~ spl3_46
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f465,f380,f374,f416])).

fof(f374,plain,
    ( spl3_46
  <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f465,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_46
    | ~ spl3_47 ),
    inference(forward_demodulation,[],[f376,f382])).

fof(f376,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f374])).

fof(f464,plain,
    ( spl3_60
    | ~ spl3_45
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f399,f380,f365,f461])).

fof(f365,plain,
    ( spl3_45
  <=> k4_relat_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f399,plain,
    ( k4_relat_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_45
    | ~ spl3_47 ),
    inference(backward_demodulation,[],[f367,f382])).

fof(f367,plain,
    ( k4_relat_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f365])).

fof(f434,plain,
    ( ~ spl3_54
    | spl3_28
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f392,f380,f248,f431])).

fof(f248,plain,
    ( spl3_28
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f392,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | spl3_28
    | ~ spl3_47 ),
    inference(backward_demodulation,[],[f250,f382])).

fof(f250,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | spl3_28 ),
    inference(avatar_component_clause,[],[f248])).

fof(f429,plain,
    ( spl3_53
    | ~ spl3_27
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f391,f380,f232,f426])).

fof(f232,plain,
    ( spl3_27
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f391,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_27
    | ~ spl3_47 ),
    inference(backward_demodulation,[],[f234,f382])).

fof(f234,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f232])).

fof(f424,plain,
    ( spl3_52
    | ~ spl3_26
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f390,f380,f227,f421])).

fof(f227,plain,
    ( spl3_26
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f390,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_26
    | ~ spl3_47 ),
    inference(backward_demodulation,[],[f229,f382])).

fof(f229,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f227])).

fof(f385,plain,
    ( spl3_47
    | ~ spl3_25
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f384,f227,f222,f380])).

fof(f222,plain,
    ( spl3_25
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f384,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_25
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f371,f229])).

fof(f371,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_25 ),
    inference(superposition,[],[f224,f64])).

fof(f224,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f222])).

fof(f377,plain,
    ( spl3_46
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f369,f227,f374])).

fof(f369,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_26 ),
    inference(unit_resulting_resolution,[],[f229,f64])).

fof(f368,plain,
    ( spl3_45
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f363,f227,f365])).

fof(f363,plain,
    ( k4_relat_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_26 ),
    inference(unit_resulting_resolution,[],[f229,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

fof(f346,plain,
    ( ~ spl3_40
    | ~ spl3_41
    | spl3_24 ),
    inference(avatar_split_clause,[],[f332,f217,f343,f339])).

fof(f339,plain,
    ( spl3_40
  <=> m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f343,plain,
    ( spl3_41
  <=> k2_struct_0(sK1) = k1_relat_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f217,plain,
    ( spl3_24
  <=> k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f332,plain,
    ( k2_struct_0(sK1) != k1_relat_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | spl3_24 ),
    inference(superposition,[],[f219,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f219,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl3_24 ),
    inference(avatar_component_clause,[],[f217])).

fof(f318,plain,
    ( spl3_38
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f313,f257,f100,f80,f315])).

fof(f313,plain,
    ( k4_relat_1(sK2) = k2_funct_1(sK2)
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_29 ),
    inference(unit_resulting_resolution,[],[f259,f102,f82,f56])).

fof(f56,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f282,plain,
    ( spl3_32
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f276,f227,f278])).

fof(f276,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_26 ),
    inference(resolution,[],[f66,f229])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f274,plain,
    ( spl3_31
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f263,f257,f271])).

fof(f263,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))
    | ~ spl3_29 ),
    inference(unit_resulting_resolution,[],[f259,f53])).

fof(f269,plain,
    ( spl3_30
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f264,f257,f266])).

fof(f264,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2))
    | ~ spl3_29 ),
    inference(unit_resulting_resolution,[],[f259,f52])).

fof(f262,plain,
    ( spl3_29
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f261,f227,f257])).

fof(f261,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f255,f57])).

fof(f255,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | ~ spl3_26 ),
    inference(resolution,[],[f54,f229])).

% (31493)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f251,plain,
    ( ~ spl3_28
    | ~ spl3_8
    | spl3_9 ),
    inference(avatar_split_clause,[],[f246,f110,f105,f248])).

fof(f105,plain,
    ( spl3_8
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f110,plain,
    ( spl3_9
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f246,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | ~ spl3_8
    | spl3_9 ),
    inference(unit_resulting_resolution,[],[f112,f107,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f107,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f105])).

fof(f112,plain,
    ( ~ v2_struct_0(sK1)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f110])).

fof(f245,plain,
    ( spl3_27
    | ~ spl3_11
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f240,f197,f132,f232])).

fof(f132,plain,
    ( spl3_11
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f197,plain,
    ( spl3_22
  <=> v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f240,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_11
    | ~ spl3_22 ),
    inference(backward_demodulation,[],[f199,f134])).

fof(f134,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f132])).

fof(f199,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f197])).

fof(f244,plain,
    ( spl3_26
    | ~ spl3_11
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f239,f191,f132,f227])).

fof(f191,plain,
    ( spl3_21
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f239,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_11
    | ~ spl3_21 ),
    inference(backward_demodulation,[],[f193,f134])).

fof(f193,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f191])).

fof(f243,plain,
    ( spl3_25
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f238,f185,f132,f222])).

fof(f185,plain,
    ( spl3_20
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f238,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(backward_demodulation,[],[f187,f134])).

fof(f187,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f185])).

fof(f242,plain,
    ( ~ spl3_24
    | ~ spl3_11
    | spl3_19 ),
    inference(avatar_split_clause,[],[f237,f179,f132,f217])).

fof(f179,plain,
    ( spl3_19
  <=> k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f237,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_11
    | spl3_19 ),
    inference(backward_demodulation,[],[f181,f134])).

fof(f181,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl3_19 ),
    inference(avatar_component_clause,[],[f179])).

fof(f241,plain,
    ( ~ spl3_23
    | ~ spl3_11
    | spl3_18 ),
    inference(avatar_split_clause,[],[f236,f173,f132,f212])).

fof(f173,plain,
    ( spl3_18
  <=> k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f236,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_11
    | spl3_18 ),
    inference(backward_demodulation,[],[f175,f134])).

fof(f175,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl3_18 ),
    inference(avatar_component_clause,[],[f173])).

fof(f200,plain,
    ( spl3_22
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f195,f105,f95,f197])).

fof(f95,plain,
    ( spl3_6
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f195,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f130,f107])).

fof(f130,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | ~ spl3_6 ),
    inference(superposition,[],[f97,f51])).

fof(f51,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f97,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f194,plain,
    ( spl3_21
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f189,f105,f90,f191])).

fof(f90,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f189,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f129,f107])).

% (31500)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f129,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | ~ spl3_5 ),
    inference(superposition,[],[f92,f51])).

fof(f92,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f188,plain,
    ( spl3_20
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f183,f105,f85,f185])).

% (31493)Refutation not found, incomplete strategy% (31493)------------------------------
% (31493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31493)Termination reason: Refutation not found, incomplete strategy

% (31493)Memory used [KB]: 6012
% (31493)Time elapsed: 0.002 s
% (31493)------------------------------
% (31493)------------------------------
fof(f85,plain,
    ( spl3_4
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f183,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f128,f107])).

fof(f128,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ l1_struct_0(sK1)
    | ~ spl3_4 ),
    inference(superposition,[],[f87,f51])).

fof(f87,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f182,plain,
    ( ~ spl3_19
    | spl3_1
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f177,f105,f71,f179])).

fof(f71,plain,
    ( spl3_1
  <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f177,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl3_1
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f127,f107])).

fof(f127,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ l1_struct_0(sK1)
    | spl3_1 ),
    inference(superposition,[],[f73,f51])).

fof(f73,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f176,plain,
    ( ~ spl3_18
    | spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f171,f105,f75,f173])).

fof(f75,plain,
    ( spl3_2
  <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f171,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl3_2
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f126,f107])).

fof(f126,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ l1_struct_0(sK1)
    | spl3_2 ),
    inference(superposition,[],[f77,f51])).

fof(f77,plain,
    ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f140,plain,
    ( spl3_12
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f119,f105,f137])).

fof(f137,plain,
    ( spl3_12
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f119,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f107,f51])).

fof(f135,plain,
    ( spl3_11
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f120,f115,f132])).

fof(f115,plain,
    ( spl3_10
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f120,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f117,f51])).

fof(f117,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f115])).

fof(f118,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f42,f115])).

fof(f42,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
      | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) )
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f39,f38,f37])).

% (31483)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f37,plain,
    ( ? [X0] :
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
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))
              | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) )
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))
            | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) )
          & v2_funct_1(X2)
          & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X2] :
        ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))
          | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) )
        & v2_funct_1(X2)
        & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
        | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) )
      & v2_funct_1(sK2)
      & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

% (31489)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f15,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

fof(f113,plain,(
    ~ spl3_9 ),
    inference(avatar_split_clause,[],[f43,f110])).

fof(f43,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f108,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f44,f105])).

fof(f44,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f103,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f45,f100])).

fof(f45,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f98,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f46,f95])).

fof(f46,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f93,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f47,f90])).

fof(f47,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f88,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f48,f85])).

fof(f48,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f83,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f49,f80])).

fof(f49,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f78,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f50,f75,f71])).

fof(f50,plain,
    ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:54:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (31488)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (31495)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (31497)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.48  % (31481)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (31487)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (31482)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (31497)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (31486)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (31482)Refutation not found, incomplete strategy% (31482)------------------------------
% 0.21/0.50  % (31482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (31482)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (31482)Memory used [KB]: 10618
% 0.21/0.50  % (31482)Time elapsed: 0.036 s
% 0.21/0.50  % (31482)------------------------------
% 0.21/0.50  % (31482)------------------------------
% 0.21/0.50  % (31485)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (31501)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (31498)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f798,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f98,f103,f108,f113,f118,f135,f140,f176,f182,f188,f194,f200,f241,f242,f243,f244,f245,f251,f262,f269,f274,f282,f318,f346,f368,f377,f385,f424,f429,f434,f464,f466,f489,f495,f511,f517,f576,f582,f623,f628,f633,f710,f725,f746,f751,f788,f790,f791,f794,f795])).
% 0.21/0.50  fof(f795,plain,(
% 0.21/0.50    u1_struct_0(sK1) != k2_struct_0(sK1) | k2_struct_0(sK0) != u1_struct_0(sK0) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_struct_0(sK0) != k1_relat_1(sK2) | m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.21/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.50  fof(f794,plain,(
% 0.21/0.50    k4_relat_1(sK2) != k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_struct_0(sK0) != u1_struct_0(sK0) | k2_struct_0(sK0) != k1_relat_1(sK2) | k1_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != k2_relat_1(k4_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) | k2_relat_1(sK2) != k2_relat_1(k4_relat_1(k4_relat_1(sK2))) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_struct_0(sK1) = k1_relat_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.21/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.50  fof(f791,plain,(
% 0.21/0.50    k4_relat_1(sK2) != k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | k2_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != k1_relat_1(k4_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) | k1_relat_1(sK2) != k1_relat_1(k4_relat_1(k4_relat_1(sK2))) | k1_relat_1(sK2) = k2_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))),
% 0.21/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.50  fof(f790,plain,(
% 0.21/0.50    k2_struct_0(sK0) != k1_relat_1(sK2) | k4_relat_1(sK2) != k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_struct_0(sK0) != u1_struct_0(sK0) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))),
% 0.21/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.50  fof(f788,plain,(
% 0.21/0.50    spl3_96 | ~spl3_3 | ~spl3_7 | ~spl3_38 | ~spl3_78 | ~spl3_79 | ~spl3_80),
% 0.21/0.50    inference(avatar_split_clause,[],[f783,f630,f625,f620,f315,f100,f80,f785])).
% 0.21/0.50  fof(f785,plain,(
% 0.21/0.50    spl3_96 <=> k4_relat_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_96])])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    spl3_3 <=> v2_funct_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    spl3_7 <=> v1_funct_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.50  fof(f315,plain,(
% 0.21/0.50    spl3_38 <=> k4_relat_1(sK2) = k2_funct_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.21/0.50  fof(f620,plain,(
% 0.21/0.50    spl3_78 <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).
% 0.21/0.50  fof(f625,plain,(
% 0.21/0.50    spl3_79 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_79])])).
% 0.21/0.50  fof(f630,plain,(
% 0.21/0.50    spl3_80 <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_80])])).
% 0.21/0.50  fof(f783,plain,(
% 0.21/0.50    k4_relat_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_3 | ~spl3_7 | ~spl3_38 | ~spl3_78 | ~spl3_79 | ~spl3_80)),
% 0.21/0.50    inference(forward_demodulation,[],[f781,f317])).
% 0.21/0.50  fof(f317,plain,(
% 0.21/0.50    k4_relat_1(sK2) = k2_funct_1(sK2) | ~spl3_38),
% 0.21/0.50    inference(avatar_component_clause,[],[f315])).
% 0.21/0.50  fof(f781,plain,(
% 0.21/0.50    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_3 | ~spl3_7 | ~spl3_78 | ~spl3_79 | ~spl3_80)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f102,f82,f632,f627,f622,f68])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.50    inference(flattening,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_tops_2(X0,X1,X2) = k2_funct_1(X2)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.21/0.50  fof(f622,plain,(
% 0.21/0.50    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_78),
% 0.21/0.50    inference(avatar_component_clause,[],[f620])).
% 0.21/0.50  fof(f627,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl3_79),
% 0.21/0.50    inference(avatar_component_clause,[],[f625])).
% 0.21/0.50  fof(f632,plain,(
% 0.21/0.50    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl3_80),
% 0.21/0.50    inference(avatar_component_clause,[],[f630])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    v2_funct_1(sK2) | ~spl3_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f80])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    v1_funct_1(sK2) | ~spl3_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f100])).
% 0.21/0.50  fof(f751,plain,(
% 0.21/0.50    spl3_94 | ~spl3_83),
% 0.21/0.50    inference(avatar_split_clause,[],[f738,f645,f748])).
% 0.21/0.50  fof(f748,plain,(
% 0.21/0.50    spl3_94 <=> k1_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) = k2_relat_1(k4_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_94])])).
% 0.21/0.50  fof(f645,plain,(
% 0.21/0.50    spl3_83 <=> v1_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).
% 0.21/0.50  fof(f738,plain,(
% 0.21/0.50    k1_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) = k2_relat_1(k4_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) | ~spl3_83),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f646,f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.21/0.50  fof(f646,plain,(
% 0.21/0.50    v1_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | ~spl3_83),
% 0.21/0.50    inference(avatar_component_clause,[],[f645])).
% 0.21/0.50  fof(f746,plain,(
% 0.21/0.50    spl3_93 | ~spl3_83),
% 0.21/0.50    inference(avatar_split_clause,[],[f739,f645,f743])).
% 0.21/0.50  fof(f743,plain,(
% 0.21/0.50    spl3_93 <=> k2_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) = k1_relat_1(k4_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_93])])).
% 0.21/0.50  fof(f739,plain,(
% 0.21/0.50    k2_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) = k1_relat_1(k4_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) | ~spl3_83),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f646,f52])).
% 0.21/0.50  % (31501)Refutation not found, incomplete strategy% (31501)------------------------------
% 0.21/0.50  % (31501)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  % (31501)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (31501)Memory used [KB]: 10618
% 0.21/0.50  % (31501)Time elapsed: 0.087 s
% 0.21/0.50  % (31501)------------------------------
% 0.21/0.50  % (31501)------------------------------
% 0.21/0.50  fof(f725,plain,(
% 0.21/0.50    ~spl3_91 | ~spl3_92 | spl3_23 | ~spl3_47 | ~spl3_73),
% 0.21/0.50    inference(avatar_split_clause,[],[f716,f579,f380,f212,f722,f718])).
% 0.21/0.50  fof(f718,plain,(
% 0.21/0.50    spl3_91 <=> k1_relat_1(sK2) = k2_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_91])])).
% 0.21/0.50  fof(f722,plain,(
% 0.21/0.50    spl3_92 <=> m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_92])])).
% 0.21/0.51  fof(f212,plain,(
% 0.21/0.51    spl3_23 <=> k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.51  fof(f380,plain,(
% 0.21/0.51    spl3_47 <=> k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.21/0.51  fof(f579,plain,(
% 0.21/0.51    spl3_73 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).
% 0.21/0.51  fof(f716,plain,(
% 0.21/0.51    ~m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | k1_relat_1(sK2) != k2_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | (spl3_23 | ~spl3_47 | ~spl3_73)),
% 0.21/0.51    inference(forward_demodulation,[],[f715,f382])).
% 0.21/0.51  fof(f382,plain,(
% 0.21/0.51    k2_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_47),
% 0.21/0.51    inference(avatar_component_clause,[],[f380])).
% 0.21/0.51  % (31494)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  fof(f715,plain,(
% 0.21/0.51    ~m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) | k1_relat_1(sK2) != k2_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | (spl3_23 | ~spl3_47 | ~spl3_73)),
% 0.21/0.51    inference(forward_demodulation,[],[f714,f581])).
% 0.21/0.51  fof(f581,plain,(
% 0.21/0.51    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_73),
% 0.21/0.51    inference(avatar_component_clause,[],[f579])).
% 0.21/0.51  fof(f714,plain,(
% 0.21/0.51    k1_relat_1(sK2) != k2_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | ~m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (spl3_23 | ~spl3_47 | ~spl3_73)),
% 0.21/0.51    inference(forward_demodulation,[],[f713,f581])).
% 0.21/0.51  fof(f713,plain,(
% 0.21/0.51    k2_struct_0(sK0) != k2_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | ~m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (spl3_23 | ~spl3_47)),
% 0.21/0.51    inference(forward_demodulation,[],[f372,f382])).
% 0.21/0.51  fof(f372,plain,(
% 0.21/0.51    k2_struct_0(sK0) != k2_relat_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | ~m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | spl3_23),
% 0.21/0.51    inference(superposition,[],[f214,f64])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.51  fof(f214,plain,(
% 0.21/0.51    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | spl3_23),
% 0.21/0.51    inference(avatar_component_clause,[],[f212])).
% 0.21/0.51  fof(f710,plain,(
% 0.21/0.51    ~spl3_3 | ~spl3_7 | ~spl3_34 | ~spl3_38 | ~spl3_78 | ~spl3_79 | ~spl3_80 | spl3_83),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f709])).
% 0.21/0.51  fof(f709,plain,(
% 0.21/0.51    $false | (~spl3_3 | ~spl3_7 | ~spl3_34 | ~spl3_38 | ~spl3_78 | ~spl3_79 | ~spl3_80 | spl3_83)),
% 0.21/0.51    inference(subsumption_resolution,[],[f708,f295])).
% 0.21/0.51  fof(f295,plain,(
% 0.21/0.51    v1_relat_1(k4_relat_1(sK2)) | ~spl3_34),
% 0.21/0.51    inference(avatar_component_clause,[],[f294])).
% 0.21/0.51  fof(f294,plain,(
% 0.21/0.51    spl3_34 <=> v1_relat_1(k4_relat_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.21/0.51  fof(f708,plain,(
% 0.21/0.51    ~v1_relat_1(k4_relat_1(sK2)) | (~spl3_3 | ~spl3_7 | ~spl3_38 | ~spl3_78 | ~spl3_79 | ~spl3_80 | spl3_83)),
% 0.21/0.51    inference(forward_demodulation,[],[f707,f317])).
% 0.21/0.51  fof(f707,plain,(
% 0.21/0.51    ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_3 | ~spl3_7 | ~spl3_78 | ~spl3_79 | ~spl3_80 | spl3_83)),
% 0.21/0.51    inference(subsumption_resolution,[],[f706,f102])).
% 0.21/0.51  fof(f706,plain,(
% 0.21/0.51    ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_3 | ~spl3_78 | ~spl3_79 | ~spl3_80 | spl3_83)),
% 0.21/0.51    inference(subsumption_resolution,[],[f705,f632])).
% 0.21/0.51  fof(f705,plain,(
% 0.21/0.51    ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_3 | ~spl3_78 | ~spl3_79 | spl3_83)),
% 0.21/0.51    inference(subsumption_resolution,[],[f704,f627])).
% 0.21/0.51  fof(f704,plain,(
% 0.21/0.51    ~v1_relat_1(k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_3 | ~spl3_78 | spl3_83)),
% 0.21/0.51    inference(subsumption_resolution,[],[f703,f622])).
% 0.21/0.51  fof(f703,plain,(
% 0.21/0.51    ~v1_relat_1(k2_funct_1(sK2)) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_3 | spl3_83)),
% 0.21/0.51    inference(subsumption_resolution,[],[f701,f82])).
% 0.21/0.51  fof(f701,plain,(
% 0.21/0.51    ~v1_relat_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | spl3_83),
% 0.21/0.51    inference(superposition,[],[f647,f68])).
% 0.21/0.51  fof(f647,plain,(
% 0.21/0.51    ~v1_relat_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | spl3_83),
% 0.21/0.51    inference(avatar_component_clause,[],[f645])).
% 0.21/0.51  fof(f633,plain,(
% 0.21/0.51    spl3_80 | ~spl3_53 | ~spl3_73),
% 0.21/0.51    inference(avatar_split_clause,[],[f590,f579,f426,f630])).
% 0.21/0.51  fof(f426,plain,(
% 0.21/0.51    spl3_53 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 0.21/0.51  fof(f590,plain,(
% 0.21/0.51    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_53 | ~spl3_73)),
% 0.21/0.51    inference(backward_demodulation,[],[f428,f581])).
% 0.21/0.51  fof(f428,plain,(
% 0.21/0.51    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~spl3_53),
% 0.21/0.51    inference(avatar_component_clause,[],[f426])).
% 0.21/0.51  fof(f628,plain,(
% 0.21/0.51    spl3_79 | ~spl3_52 | ~spl3_73),
% 0.21/0.51    inference(avatar_split_clause,[],[f589,f579,f421,f625])).
% 0.21/0.51  fof(f421,plain,(
% 0.21/0.51    spl3_52 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 0.21/0.51  fof(f589,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_52 | ~spl3_73)),
% 0.21/0.51    inference(backward_demodulation,[],[f423,f581])).
% 0.21/0.51  fof(f423,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~spl3_52),
% 0.21/0.51    inference(avatar_component_clause,[],[f421])).
% 0.21/0.51  fof(f623,plain,(
% 0.21/0.51    spl3_78 | ~spl3_51 | ~spl3_73),
% 0.21/0.51    inference(avatar_split_clause,[],[f588,f579,f416,f620])).
% 0.21/0.51  fof(f416,plain,(
% 0.21/0.51    spl3_51 <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 0.21/0.51  fof(f588,plain,(
% 0.21/0.51    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_51 | ~spl3_73)),
% 0.21/0.51    inference(backward_demodulation,[],[f418,f581])).
% 0.21/0.51  fof(f418,plain,(
% 0.21/0.51    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_51),
% 0.21/0.51    inference(avatar_component_clause,[],[f416])).
% 0.21/0.51  fof(f582,plain,(
% 0.21/0.51    spl3_73 | ~spl3_29 | ~spl3_32 | ~spl3_72),
% 0.21/0.51    inference(avatar_split_clause,[],[f577,f569,f278,f257,f579])).
% 0.21/0.51  fof(f257,plain,(
% 0.21/0.51    spl3_29 <=> v1_relat_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.51  fof(f278,plain,(
% 0.21/0.51    spl3_32 <=> v4_relat_1(sK2,k2_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.51  fof(f569,plain,(
% 0.21/0.51    spl3_72 <=> v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).
% 0.21/0.51  fof(f577,plain,(
% 0.21/0.51    k2_struct_0(sK0) = k1_relat_1(sK2) | (~spl3_29 | ~spl3_32 | ~spl3_72)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f259,f280,f571,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.21/0.51  fof(f571,plain,(
% 0.21/0.51    v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl3_72),
% 0.21/0.51    inference(avatar_component_clause,[],[f569])).
% 0.21/0.51  fof(f280,plain,(
% 0.21/0.51    v4_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_32),
% 0.21/0.51    inference(avatar_component_clause,[],[f278])).
% 0.21/0.51  fof(f259,plain,(
% 0.21/0.51    v1_relat_1(sK2) | ~spl3_29),
% 0.21/0.51    inference(avatar_component_clause,[],[f257])).
% 0.21/0.51  fof(f576,plain,(
% 0.21/0.51    spl3_72 | ~spl3_7 | ~spl3_52 | ~spl3_53 | spl3_54),
% 0.21/0.51    inference(avatar_split_clause,[],[f575,f431,f426,f421,f100,f569])).
% 0.21/0.51  fof(f431,plain,(
% 0.21/0.51    spl3_54 <=> v1_xboole_0(k2_relat_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 0.21/0.51  fof(f575,plain,(
% 0.21/0.51    v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_7 | ~spl3_52 | ~spl3_53 | spl3_54)),
% 0.21/0.51    inference(subsumption_resolution,[],[f574,f433])).
% 0.21/0.51  fof(f433,plain,(
% 0.21/0.51    ~v1_xboole_0(k2_relat_1(sK2)) | spl3_54),
% 0.21/0.51    inference(avatar_component_clause,[],[f431])).
% 0.21/0.51  fof(f574,plain,(
% 0.21/0.51    v1_partfun1(sK2,k2_struct_0(sK0)) | v1_xboole_0(k2_relat_1(sK2)) | (~spl3_7 | ~spl3_52 | ~spl3_53)),
% 0.21/0.51    inference(subsumption_resolution,[],[f573,f102])).
% 0.21/0.51  fof(f573,plain,(
% 0.21/0.51    ~v1_funct_1(sK2) | v1_partfun1(sK2,k2_struct_0(sK0)) | v1_xboole_0(k2_relat_1(sK2)) | (~spl3_52 | ~spl3_53)),
% 0.21/0.51    inference(subsumption_resolution,[],[f566,f428])).
% 0.21/0.51  fof(f566,plain,(
% 0.21/0.51    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | v1_partfun1(sK2,k2_struct_0(sK0)) | v1_xboole_0(k2_relat_1(sK2)) | ~spl3_52),
% 0.21/0.51    inference(resolution,[],[f59,f423])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_partfun1(X2,X0) | v1_xboole_0(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.51    inference(flattening,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.21/0.51  fof(f517,plain,(
% 0.21/0.51    spl3_64 | ~spl3_30 | ~spl3_34),
% 0.21/0.51    inference(avatar_split_clause,[],[f512,f294,f266,f514])).
% 0.21/0.51  fof(f514,plain,(
% 0.21/0.51    spl3_64 <=> k2_relat_1(sK2) = k2_relat_1(k4_relat_1(k4_relat_1(sK2)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).
% 0.21/0.51  fof(f266,plain,(
% 0.21/0.51    spl3_30 <=> k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.51  fof(f512,plain,(
% 0.21/0.51    k2_relat_1(sK2) = k2_relat_1(k4_relat_1(k4_relat_1(sK2))) | (~spl3_30 | ~spl3_34)),
% 0.21/0.51    inference(forward_demodulation,[],[f504,f268])).
% 0.21/0.51  fof(f268,plain,(
% 0.21/0.51    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2)) | ~spl3_30),
% 0.21/0.51    inference(avatar_component_clause,[],[f266])).
% 0.21/0.51  fof(f504,plain,(
% 0.21/0.51    k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(k4_relat_1(k4_relat_1(sK2))) | ~spl3_34),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f295,f53])).
% 0.21/0.51  fof(f511,plain,(
% 0.21/0.51    spl3_63 | ~spl3_31 | ~spl3_34),
% 0.21/0.51    inference(avatar_split_clause,[],[f506,f294,f271,f508])).
% 0.21/0.51  fof(f508,plain,(
% 0.21/0.51    spl3_63 <=> k1_relat_1(sK2) = k1_relat_1(k4_relat_1(k4_relat_1(sK2)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).
% 0.21/0.51  fof(f271,plain,(
% 0.21/0.51    spl3_31 <=> k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.51  fof(f506,plain,(
% 0.21/0.51    k1_relat_1(sK2) = k1_relat_1(k4_relat_1(k4_relat_1(sK2))) | (~spl3_31 | ~spl3_34)),
% 0.21/0.51    inference(forward_demodulation,[],[f505,f273])).
% 0.21/0.51  fof(f273,plain,(
% 0.21/0.51    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) | ~spl3_31),
% 0.21/0.51    inference(avatar_component_clause,[],[f271])).
% 0.21/0.51  fof(f505,plain,(
% 0.21/0.51    k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(k4_relat_1(k4_relat_1(sK2))) | ~spl3_34),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f295,f52])).
% 0.21/0.51  fof(f495,plain,(
% 0.21/0.51    spl3_61 | ~spl3_52 | ~spl3_60),
% 0.21/0.51    inference(avatar_split_clause,[],[f487,f461,f421,f492])).
% 0.21/0.51  fof(f492,plain,(
% 0.21/0.51    spl3_61 <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 0.21/0.51  fof(f461,plain,(
% 0.21/0.51    spl3_60 <=> k4_relat_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).
% 0.21/0.51  fof(f487,plain,(
% 0.21/0.51    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | (~spl3_52 | ~spl3_60)),
% 0.21/0.51    inference(forward_demodulation,[],[f481,f463])).
% 0.21/0.51  fof(f463,plain,(
% 0.21/0.51    k4_relat_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_60),
% 0.21/0.51    inference(avatar_component_clause,[],[f461])).
% 0.21/0.51  fof(f481,plain,(
% 0.21/0.51    m1_subset_1(k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | ~spl3_52),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f423,f65])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_relset_1)).
% 0.21/0.51  fof(f489,plain,(
% 0.21/0.51    spl3_34 | ~spl3_52 | ~spl3_60),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f488])).
% 0.21/0.51  fof(f488,plain,(
% 0.21/0.51    $false | (spl3_34 | ~spl3_52 | ~spl3_60)),
% 0.21/0.51    inference(subsumption_resolution,[],[f487,f306])).
% 0.21/0.51  % (31491)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.51  fof(f306,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl3_34),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f57,f296,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.51  fof(f296,plain,(
% 0.21/0.51    ~v1_relat_1(k4_relat_1(sK2)) | spl3_34),
% 0.21/0.51    inference(avatar_component_clause,[],[f294])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.51  fof(f466,plain,(
% 0.21/0.51    spl3_51 | ~spl3_46 | ~spl3_47),
% 0.21/0.51    inference(avatar_split_clause,[],[f465,f380,f374,f416])).
% 0.21/0.51  fof(f374,plain,(
% 0.21/0.51    spl3_46 <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.21/0.51  fof(f465,plain,(
% 0.21/0.51    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | (~spl3_46 | ~spl3_47)),
% 0.21/0.51    inference(forward_demodulation,[],[f376,f382])).
% 0.21/0.51  fof(f376,plain,(
% 0.21/0.51    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_46),
% 0.21/0.51    inference(avatar_component_clause,[],[f374])).
% 0.21/0.51  fof(f464,plain,(
% 0.21/0.51    spl3_60 | ~spl3_45 | ~spl3_47),
% 0.21/0.51    inference(avatar_split_clause,[],[f399,f380,f365,f461])).
% 0.21/0.51  fof(f365,plain,(
% 0.21/0.51    spl3_45 <=> k4_relat_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.21/0.51  fof(f399,plain,(
% 0.21/0.51    k4_relat_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | (~spl3_45 | ~spl3_47)),
% 0.21/0.51    inference(backward_demodulation,[],[f367,f382])).
% 0.21/0.51  fof(f367,plain,(
% 0.21/0.51    k4_relat_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_45),
% 0.21/0.51    inference(avatar_component_clause,[],[f365])).
% 0.21/0.51  fof(f434,plain,(
% 0.21/0.51    ~spl3_54 | spl3_28 | ~spl3_47),
% 0.21/0.51    inference(avatar_split_clause,[],[f392,f380,f248,f431])).
% 0.21/0.51  fof(f248,plain,(
% 0.21/0.51    spl3_28 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.51  fof(f392,plain,(
% 0.21/0.51    ~v1_xboole_0(k2_relat_1(sK2)) | (spl3_28 | ~spl3_47)),
% 0.21/0.51    inference(backward_demodulation,[],[f250,f382])).
% 0.21/0.51  fof(f250,plain,(
% 0.21/0.51    ~v1_xboole_0(k2_struct_0(sK1)) | spl3_28),
% 0.21/0.51    inference(avatar_component_clause,[],[f248])).
% 0.21/0.51  fof(f429,plain,(
% 0.21/0.51    spl3_53 | ~spl3_27 | ~spl3_47),
% 0.21/0.51    inference(avatar_split_clause,[],[f391,f380,f232,f426])).
% 0.21/0.51  fof(f232,plain,(
% 0.21/0.51    spl3_27 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.51  fof(f391,plain,(
% 0.21/0.51    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_27 | ~spl3_47)),
% 0.21/0.51    inference(backward_demodulation,[],[f234,f382])).
% 0.21/0.51  fof(f234,plain,(
% 0.21/0.51    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_27),
% 0.21/0.51    inference(avatar_component_clause,[],[f232])).
% 0.21/0.51  fof(f424,plain,(
% 0.21/0.51    spl3_52 | ~spl3_26 | ~spl3_47),
% 0.21/0.51    inference(avatar_split_clause,[],[f390,f380,f227,f421])).
% 0.21/0.51  fof(f227,plain,(
% 0.21/0.51    spl3_26 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.51  fof(f390,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | (~spl3_26 | ~spl3_47)),
% 0.21/0.51    inference(backward_demodulation,[],[f229,f382])).
% 0.21/0.51  fof(f229,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_26),
% 0.21/0.51    inference(avatar_component_clause,[],[f227])).
% 0.21/0.51  fof(f385,plain,(
% 0.21/0.51    spl3_47 | ~spl3_25 | ~spl3_26),
% 0.21/0.51    inference(avatar_split_clause,[],[f384,f227,f222,f380])).
% 0.21/0.51  fof(f222,plain,(
% 0.21/0.51    spl3_25 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.51  fof(f384,plain,(
% 0.21/0.51    k2_struct_0(sK1) = k2_relat_1(sK2) | (~spl3_25 | ~spl3_26)),
% 0.21/0.51    inference(subsumption_resolution,[],[f371,f229])).
% 0.21/0.51  fof(f371,plain,(
% 0.21/0.51    k2_struct_0(sK1) = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_25),
% 0.21/0.51    inference(superposition,[],[f224,f64])).
% 0.21/0.51  fof(f224,plain,(
% 0.21/0.51    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_25),
% 0.21/0.51    inference(avatar_component_clause,[],[f222])).
% 0.21/0.51  fof(f377,plain,(
% 0.21/0.51    spl3_46 | ~spl3_26),
% 0.21/0.51    inference(avatar_split_clause,[],[f369,f227,f374])).
% 0.21/0.51  fof(f369,plain,(
% 0.21/0.51    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_26),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f229,f64])).
% 0.21/0.51  fof(f368,plain,(
% 0.21/0.51    spl3_45 | ~spl3_26),
% 0.21/0.51    inference(avatar_split_clause,[],[f363,f227,f365])).
% 0.21/0.51  fof(f363,plain,(
% 0.21/0.51    k4_relat_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_26),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f229,f63])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k3_relset_1(X0,X1,X2) = k4_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k3_relset_1(X0,X1,X2) = k4_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k3_relset_1(X0,X1,X2) = k4_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).
% 0.21/0.51  fof(f346,plain,(
% 0.21/0.51    ~spl3_40 | ~spl3_41 | spl3_24),
% 0.21/0.51    inference(avatar_split_clause,[],[f332,f217,f343,f339])).
% 0.21/0.51  fof(f339,plain,(
% 0.21/0.51    spl3_40 <=> m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.21/0.51  fof(f343,plain,(
% 0.21/0.51    spl3_41 <=> k2_struct_0(sK1) = k1_relat_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.21/0.51  fof(f217,plain,(
% 0.21/0.51    spl3_24 <=> k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.51  fof(f332,plain,(
% 0.21/0.51    k2_struct_0(sK1) != k1_relat_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | ~m1_subset_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | spl3_24),
% 0.21/0.51    inference(superposition,[],[f219,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.51  fof(f219,plain,(
% 0.21/0.51    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | spl3_24),
% 0.21/0.51    inference(avatar_component_clause,[],[f217])).
% 0.21/0.51  fof(f318,plain,(
% 0.21/0.51    spl3_38 | ~spl3_3 | ~spl3_7 | ~spl3_29),
% 0.21/0.51    inference(avatar_split_clause,[],[f313,f257,f100,f80,f315])).
% 0.21/0.51  fof(f313,plain,(
% 0.21/0.51    k4_relat_1(sK2) = k2_funct_1(sK2) | (~spl3_3 | ~spl3_7 | ~spl3_29)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f259,f102,f82,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.21/0.51  fof(f282,plain,(
% 0.21/0.51    spl3_32 | ~spl3_26),
% 0.21/0.51    inference(avatar_split_clause,[],[f276,f227,f278])).
% 0.21/0.51  fof(f276,plain,(
% 0.21/0.51    v4_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_26),
% 0.21/0.51    inference(resolution,[],[f66,f229])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.51  fof(f274,plain,(
% 0.21/0.51    spl3_31 | ~spl3_29),
% 0.21/0.51    inference(avatar_split_clause,[],[f263,f257,f271])).
% 0.21/0.51  fof(f263,plain,(
% 0.21/0.51    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) | ~spl3_29),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f259,f53])).
% 0.21/0.51  fof(f269,plain,(
% 0.21/0.51    spl3_30 | ~spl3_29),
% 0.21/0.51    inference(avatar_split_clause,[],[f264,f257,f266])).
% 0.21/0.51  fof(f264,plain,(
% 0.21/0.51    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2)) | ~spl3_29),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f259,f52])).
% 0.21/0.51  fof(f262,plain,(
% 0.21/0.51    spl3_29 | ~spl3_26),
% 0.21/0.51    inference(avatar_split_clause,[],[f261,f227,f257])).
% 0.21/0.51  fof(f261,plain,(
% 0.21/0.51    v1_relat_1(sK2) | ~spl3_26),
% 0.21/0.51    inference(subsumption_resolution,[],[f255,f57])).
% 0.21/0.51  fof(f255,plain,(
% 0.21/0.51    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | ~spl3_26),
% 0.21/0.51    inference(resolution,[],[f54,f229])).
% 0.21/0.51  % (31493)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  fof(f251,plain,(
% 0.21/0.51    ~spl3_28 | ~spl3_8 | spl3_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f246,f110,f105,f248])).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    spl3_8 <=> l1_struct_0(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    spl3_9 <=> v2_struct_0(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.51  fof(f246,plain,(
% 0.21/0.51    ~v1_xboole_0(k2_struct_0(sK1)) | (~spl3_8 | spl3_9)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f112,f107,f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    l1_struct_0(sK1) | ~spl3_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f105])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    ~v2_struct_0(sK1) | spl3_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f110])).
% 0.21/0.51  fof(f245,plain,(
% 0.21/0.51    spl3_27 | ~spl3_11 | ~spl3_22),
% 0.21/0.51    inference(avatar_split_clause,[],[f240,f197,f132,f232])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    spl3_11 <=> k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.51  fof(f197,plain,(
% 0.21/0.51    spl3_22 <=> v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.51  fof(f240,plain,(
% 0.21/0.51    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_11 | ~spl3_22)),
% 0.21/0.51    inference(backward_demodulation,[],[f199,f134])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f132])).
% 0.21/0.51  fof(f199,plain,(
% 0.21/0.51    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_22),
% 0.21/0.51    inference(avatar_component_clause,[],[f197])).
% 0.21/0.51  fof(f244,plain,(
% 0.21/0.51    spl3_26 | ~spl3_11 | ~spl3_21),
% 0.21/0.51    inference(avatar_split_clause,[],[f239,f191,f132,f227])).
% 0.21/0.51  fof(f191,plain,(
% 0.21/0.51    spl3_21 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.51  fof(f239,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_11 | ~spl3_21)),
% 0.21/0.51    inference(backward_demodulation,[],[f193,f134])).
% 0.21/0.51  fof(f193,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_21),
% 0.21/0.51    inference(avatar_component_clause,[],[f191])).
% 0.21/0.51  fof(f243,plain,(
% 0.21/0.51    spl3_25 | ~spl3_11 | ~spl3_20),
% 0.21/0.51    inference(avatar_split_clause,[],[f238,f185,f132,f222])).
% 0.21/0.51  fof(f185,plain,(
% 0.21/0.51    spl3_20 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.51  fof(f238,plain,(
% 0.21/0.51    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_11 | ~spl3_20)),
% 0.21/0.51    inference(backward_demodulation,[],[f187,f134])).
% 0.21/0.51  fof(f187,plain,(
% 0.21/0.51    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_20),
% 0.21/0.51    inference(avatar_component_clause,[],[f185])).
% 0.21/0.51  fof(f242,plain,(
% 0.21/0.51    ~spl3_24 | ~spl3_11 | spl3_19),
% 0.21/0.51    inference(avatar_split_clause,[],[f237,f179,f132,f217])).
% 0.21/0.51  fof(f179,plain,(
% 0.21/0.51    spl3_19 <=> k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.51  fof(f237,plain,(
% 0.21/0.51    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | (~spl3_11 | spl3_19)),
% 0.21/0.51    inference(backward_demodulation,[],[f181,f134])).
% 0.21/0.51  fof(f181,plain,(
% 0.21/0.51    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | spl3_19),
% 0.21/0.51    inference(avatar_component_clause,[],[f179])).
% 0.21/0.51  fof(f241,plain,(
% 0.21/0.51    ~spl3_23 | ~spl3_11 | spl3_18),
% 0.21/0.51    inference(avatar_split_clause,[],[f236,f173,f132,f212])).
% 0.21/0.51  fof(f173,plain,(
% 0.21/0.51    spl3_18 <=> k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.51  fof(f236,plain,(
% 0.21/0.51    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | (~spl3_11 | spl3_18)),
% 0.21/0.51    inference(backward_demodulation,[],[f175,f134])).
% 0.21/0.51  fof(f175,plain,(
% 0.21/0.51    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | spl3_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f173])).
% 0.21/0.51  fof(f200,plain,(
% 0.21/0.51    spl3_22 | ~spl3_6 | ~spl3_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f195,f105,f95,f197])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    spl3_6 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.51  fof(f195,plain,(
% 0.21/0.51    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_6 | ~spl3_8)),
% 0.21/0.51    inference(subsumption_resolution,[],[f130,f107])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~l1_struct_0(sK1) | ~spl3_6),
% 0.21/0.51    inference(superposition,[],[f97,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f95])).
% 0.21/0.51  fof(f194,plain,(
% 0.21/0.51    spl3_21 | ~spl3_5 | ~spl3_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f189,f105,f90,f191])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.51  fof(f189,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_5 | ~spl3_8)),
% 0.21/0.51    inference(subsumption_resolution,[],[f129,f107])).
% 0.21/0.51  % (31500)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_struct_0(sK1) | ~spl3_5),
% 0.21/0.51    inference(superposition,[],[f92,f51])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f90])).
% 0.21/0.51  fof(f188,plain,(
% 0.21/0.51    spl3_20 | ~spl3_4 | ~spl3_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f183,f105,f85,f185])).
% 0.21/0.51  % (31493)Refutation not found, incomplete strategy% (31493)------------------------------
% 0.21/0.51  % (31493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31493)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31493)Memory used [KB]: 6012
% 0.21/0.51  % (31493)Time elapsed: 0.002 s
% 0.21/0.51  % (31493)------------------------------
% 0.21/0.51  % (31493)------------------------------
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    spl3_4 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.51  fof(f183,plain,(
% 0.21/0.51    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_8)),
% 0.21/0.51    inference(subsumption_resolution,[],[f128,f107])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | ~l1_struct_0(sK1) | ~spl3_4),
% 0.21/0.51    inference(superposition,[],[f87,f51])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl3_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f85])).
% 0.21/0.51  fof(f182,plain,(
% 0.21/0.51    ~spl3_19 | spl3_1 | ~spl3_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f177,f105,f71,f179])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    spl3_1 <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.51  fof(f177,plain,(
% 0.21/0.51    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | (spl3_1 | ~spl3_8)),
% 0.21/0.51    inference(subsumption_resolution,[],[f127,f107])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | ~l1_struct_0(sK1) | spl3_1),
% 0.21/0.51    inference(superposition,[],[f73,f51])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | spl3_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f71])).
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    ~spl3_18 | spl3_2 | ~spl3_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f171,f105,f75,f173])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    spl3_2 <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.51  fof(f171,plain,(
% 0.21/0.51    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | (spl3_2 | ~spl3_8)),
% 0.21/0.51    inference(subsumption_resolution,[],[f126,f107])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | ~l1_struct_0(sK1) | spl3_2),
% 0.21/0.51    inference(superposition,[],[f77,f51])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | spl3_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f75])).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    spl3_12 | ~spl3_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f119,f105,f137])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    spl3_12 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_8),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f107,f51])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    spl3_11 | ~spl3_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f120,f115,f132])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    spl3_10 <=> l1_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_10),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f117,f51])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    l1_struct_0(sK0) | ~spl3_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f115])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    spl3_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f42,f115])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    l1_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    (((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f39,f38,f37])).
% 0.21/0.51  % (31483)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ? [X1] : (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))) & v2_funct_1(X2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))) & v2_funct_1(X2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,negated_conjecture,(
% 0.21/0.51    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f15])).
% 0.21/0.51  % (31489)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.51  fof(f15,conjecture,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    ~spl3_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f43,f110])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ~v2_struct_0(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    spl3_8),
% 0.21/0.51    inference(avatar_split_clause,[],[f44,f105])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    l1_struct_0(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    spl3_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f45,f100])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    v1_funct_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    spl3_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f46,f95])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    spl3_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f47,f90])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    spl3_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f48,f85])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    spl3_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f49,f80])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    v2_funct_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ~spl3_1 | ~spl3_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f50,f75,f71])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.51    inference(cnf_transformation,[],[f40])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (31497)------------------------------
% 0.21/0.51  % (31497)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31497)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (31497)Memory used [KB]: 11257
% 0.21/0.51  % (31497)Time elapsed: 0.082 s
% 0.21/0.51  % (31497)------------------------------
% 0.21/0.51  % (31497)------------------------------
% 0.21/0.51  % (31491)Refutation not found, incomplete strategy% (31491)------------------------------
% 0.21/0.51  % (31491)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31491)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  % (31480)Success in time 0.151 s
%------------------------------------------------------------------------------
