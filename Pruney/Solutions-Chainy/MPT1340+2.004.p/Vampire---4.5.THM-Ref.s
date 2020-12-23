%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  289 ( 587 expanded)
%              Number of leaves         :   70 ( 290 expanded)
%              Depth                    :   12
%              Number of atoms          : 1046 (2298 expanded)
%              Number of equality atoms :  150 ( 369 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f582,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f98,f102,f106,f110,f114,f118,f122,f126,f133,f137,f150,f152,f162,f168,f196,f201,f205,f211,f215,f222,f238,f251,f269,f273,f301,f318,f321,f324,f395,f410,f413,f426,f428,f443,f455,f459,f476,f487,f488,f514,f536,f541,f555,f560,f568,f573,f579,f581])).

% (30749)Refutation not found, incomplete strategy% (30749)------------------------------
% (30749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30749)Termination reason: Refutation not found, incomplete strategy

fof(f581,plain,
    ( ~ spl3_52
    | ~ spl3_6
    | ~ spl3_48
    | ~ spl3_60 ),
    inference(avatar_split_clause,[],[f580,f577,f446,f112,f485])).

% (30749)Memory used [KB]: 10746
% (30749)Time elapsed: 0.094 s
% (30749)------------------------------
% (30749)------------------------------
fof(f485,plain,
    ( spl3_52
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f112,plain,
    ( spl3_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f446,plain,
    ( spl3_48
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f577,plain,
    ( spl3_60
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f580,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_48
    | ~ spl3_60 ),
    inference(resolution,[],[f578,f447])).

fof(f447,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f446])).

fof(f578,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) )
    | ~ spl3_60 ),
    inference(avatar_component_clause,[],[f577])).

fof(f579,plain,
    ( ~ spl3_6
    | ~ spl3_48
    | ~ spl3_52
    | spl3_60
    | spl3_59 ),
    inference(avatar_split_clause,[],[f574,f571,f577,f485,f446,f112])).

fof(f571,plain,
    ( spl3_59
  <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f574,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
        | ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
        | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
        | ~ v1_funct_1(sK2) )
    | spl3_59 ),
    inference(resolution,[],[f572,f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

fof(f572,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | spl3_59 ),
    inference(avatar_component_clause,[],[f571])).

fof(f573,plain,
    ( ~ spl3_59
    | spl3_57
    | ~ spl3_58 ),
    inference(avatar_split_clause,[],[f569,f565,f558,f571])).

fof(f558,plain,
    ( spl3_57
  <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f565,plain,
    ( spl3_58
  <=> sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f569,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | spl3_57
    | ~ spl3_58 ),
    inference(superposition,[],[f559,f566])).

fof(f566,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))
    | ~ spl3_58 ),
    inference(avatar_component_clause,[],[f565])).

fof(f559,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)),sK2)
    | spl3_57 ),
    inference(avatar_component_clause,[],[f558])).

fof(f568,plain,
    ( spl3_58
    | ~ spl3_50
    | ~ spl3_51
    | ~ spl3_53
    | ~ spl3_55 ),
    inference(avatar_split_clause,[],[f563,f539,f512,f473,f457,f565])).

fof(f457,plain,
    ( spl3_50
  <=> v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f473,plain,
    ( spl3_51
  <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f512,plain,
    ( spl3_53
  <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f539,plain,
    ( spl3_55
  <=> ! [X5,X6] :
        ( sK2 = k2_tops_2(X5,X6,k4_relat_1(sK2))
        | ~ v1_funct_2(k4_relat_1(sK2),X5,X6)
        | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | k2_relset_1(X5,X6,k4_relat_1(sK2)) != X6 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f563,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))
    | ~ spl3_51
    | ~ spl3_53
    | ~ spl3_55 ),
    inference(trivial_inequality_removal,[],[f562])).

fof(f562,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))
    | ~ spl3_51
    | ~ spl3_53
    | ~ spl3_55 ),
    inference(forward_demodulation,[],[f561,f513])).

fof(f513,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))
    | ~ spl3_53 ),
    inference(avatar_component_clause,[],[f512])).

fof(f561,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))
    | ~ spl3_51
    | ~ spl3_55 ),
    inference(resolution,[],[f540,f474])).

fof(f474,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_51 ),
    inference(avatar_component_clause,[],[f473])).

fof(f540,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ v1_funct_2(k4_relat_1(sK2),X5,X6)
        | sK2 = k2_tops_2(X5,X6,k4_relat_1(sK2))
        | k2_relset_1(X5,X6,k4_relat_1(sK2)) != X6 )
    | ~ spl3_55 ),
    inference(avatar_component_clause,[],[f539])).

fof(f560,plain,
    ( ~ spl3_57
    | spl3_47
    | ~ spl3_56 ),
    inference(avatar_split_clause,[],[f556,f550,f441,f558])).

fof(f441,plain,
    ( spl3_47
  <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f550,plain,
    ( spl3_56
  <=> k4_relat_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f556,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)),sK2)
    | spl3_47
    | ~ spl3_56 ),
    inference(superposition,[],[f442,f551])).

fof(f551,plain,
    ( k4_relat_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f550])).

fof(f442,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2)
    | spl3_47 ),
    inference(avatar_component_clause,[],[f441])).

fof(f555,plain,
    ( spl3_56
    | ~ spl3_48
    | ~ spl3_45
    | ~ spl3_52
    | ~ spl3_54 ),
    inference(avatar_split_clause,[],[f554,f534,f485,f416,f446,f550])).

fof(f416,plain,
    ( spl3_45
  <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f534,plain,
    ( spl3_54
  <=> ! [X1,X0] :
        ( k4_relat_1(sK2) = k2_tops_2(X0,X1,sK2)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,sK2) != X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f554,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k4_relat_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_45
    | ~ spl3_52
    | ~ spl3_54 ),
    inference(trivial_inequality_removal,[],[f553])).

fof(f553,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k4_relat_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_45
    | ~ spl3_52
    | ~ spl3_54 ),
    inference(forward_demodulation,[],[f543,f417])).

fof(f417,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f416])).

fof(f543,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k4_relat_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_52
    | ~ spl3_54 ),
    inference(resolution,[],[f535,f486])).

fof(f486,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_52 ),
    inference(avatar_component_clause,[],[f485])).

fof(f535,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | k4_relat_1(sK2) = k2_tops_2(X0,X1,sK2)
        | k2_relset_1(X0,X1,sK2) != X1 )
    | ~ spl3_54 ),
    inference(avatar_component_clause,[],[f534])).

fof(f541,plain,
    ( ~ spl3_21
    | spl3_55
    | ~ spl3_23
    | ~ spl3_34 ),
    inference(avatar_split_clause,[],[f537,f310,f220,f539,f209])).

fof(f209,plain,
    ( spl3_21
  <=> v1_funct_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f220,plain,
    ( spl3_23
  <=> sK2 = k2_funct_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f310,plain,
    ( spl3_34
  <=> v2_funct_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f537,plain,
    ( ! [X6,X5] :
        ( sK2 = k2_tops_2(X5,X6,k4_relat_1(sK2))
        | k2_relset_1(X5,X6,k4_relat_1(sK2)) != X6
        | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ v1_funct_2(k4_relat_1(sK2),X5,X6)
        | ~ v1_funct_1(k4_relat_1(sK2)) )
    | ~ spl3_23
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f531,f221])).

fof(f221,plain,
    ( sK2 = k2_funct_1(k4_relat_1(sK2))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f220])).

fof(f531,plain,
    ( ! [X6,X5] :
        ( k2_funct_1(k4_relat_1(sK2)) = k2_tops_2(X5,X6,k4_relat_1(sK2))
        | k2_relset_1(X5,X6,k4_relat_1(sK2)) != X6
        | ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ v1_funct_2(k4_relat_1(sK2),X5,X6)
        | ~ v1_funct_1(k4_relat_1(sK2)) )
    | ~ spl3_34 ),
    inference(resolution,[],[f88,f311])).

fof(f311,plain,
    ( v2_funct_1(k4_relat_1(sK2))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f310])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f536,plain,
    ( ~ spl3_6
    | spl3_54
    | ~ spl3_2
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f532,f194,f96,f534,f112])).

fof(f96,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f194,plain,
    ( spl3_20
  <=> k4_relat_1(sK2) = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f532,plain,
    ( ! [X0,X1] :
        ( k4_relat_1(sK2) = k2_tops_2(X0,X1,sK2)
        | k2_relset_1(X0,X1,sK2) != X1
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl3_2
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f529,f195])).

fof(f195,plain,
    ( k4_relat_1(sK2) = k2_funct_1(sK2)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f194])).

fof(f529,plain,
    ( ! [X0,X1] :
        ( k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
        | k2_relset_1(X0,X1,sK2) != X1
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl3_2 ),
    inference(resolution,[],[f88,f97])).

fof(f97,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f514,plain,
    ( spl3_53
    | ~ spl3_35
    | ~ spl3_51 ),
    inference(avatar_split_clause,[],[f510,f473,f313,f512])).

fof(f313,plain,
    ( spl3_35
  <=> k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f510,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))
    | ~ spl3_35
    | ~ spl3_51 ),
    inference(forward_demodulation,[],[f505,f322])).

fof(f322,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f313])).

fof(f505,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))
    | ~ spl3_51 ),
    inference(resolution,[],[f474,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f488,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f487,plain,
    ( spl3_52
    | ~ spl3_29
    | ~ spl3_44 ),
    inference(avatar_split_clause,[],[f465,f406,f263,f485])).

fof(f263,plain,
    ( spl3_29
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f406,plain,
    ( spl3_44
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f465,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_29
    | ~ spl3_44 ),
    inference(superposition,[],[f264,f407])).

fof(f407,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f406])).

fof(f264,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f263])).

fof(f476,plain,
    ( ~ spl3_6
    | ~ spl3_2
    | spl3_51
    | ~ spl3_48
    | ~ spl3_20
    | ~ spl3_29
    | ~ spl3_44
    | ~ spl3_45 ),
    inference(avatar_split_clause,[],[f471,f416,f406,f263,f194,f446,f473,f96,f112])).

fof(f471,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_20
    | ~ spl3_29
    | ~ spl3_44
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f470,f407])).

fof(f470,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_20
    | ~ spl3_29
    | ~ spl3_44
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f469,f195])).

fof(f469,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_29
    | ~ spl3_44
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f468,f407])).

fof(f468,plain,
    ( ~ v2_funct_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_29
    | ~ spl3_44
    | ~ spl3_45 ),
    inference(trivial_inequality_removal,[],[f467])).

fof(f467,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_29
    | ~ spl3_44
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f466,f417])).

fof(f466,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_29
    | ~ spl3_44 ),
    inference(forward_demodulation,[],[f460,f407])).

fof(f460,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_29 ),
    inference(resolution,[],[f264,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f459,plain,
    ( spl3_50
    | ~ spl3_42
    | ~ spl3_44 ),
    inference(avatar_split_clause,[],[f437,f406,f388,f457])).

fof(f388,plain,
    ( spl3_42
  <=> v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f437,plain,
    ( v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_42
    | ~ spl3_44 ),
    inference(superposition,[],[f389,f407])).

fof(f389,plain,
    ( v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f388])).

fof(f455,plain,
    ( spl3_48
    | ~ spl3_30
    | ~ spl3_44 ),
    inference(avatar_split_clause,[],[f436,f406,f267,f446])).

fof(f267,plain,
    ( spl3_30
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f436,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_30
    | ~ spl3_44 ),
    inference(superposition,[],[f268,f407])).

fof(f268,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f267])).

fof(f443,plain,
    ( ~ spl3_47
    | spl3_13
    | ~ spl3_25
    | ~ spl3_44 ),
    inference(avatar_split_clause,[],[f439,f406,f240,f148,f441])).

fof(f148,plain,
    ( spl3_13
  <=> r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f240,plain,
    ( spl3_25
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f439,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2)
    | spl3_13
    | ~ spl3_25
    | ~ spl3_44 ),
    inference(forward_demodulation,[],[f431,f241])).

fof(f241,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f240])).

fof(f431,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),sK2)
    | spl3_13
    | ~ spl3_44 ),
    inference(superposition,[],[f149,f407])).

fof(f149,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f148])).

fof(f428,plain,
    ( spl3_29
    | ~ spl3_14
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f427,f240,f155,f263])).

fof(f155,plain,
    ( spl3_14
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f427,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_14
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f156,f241])).

fof(f156,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f155])).

fof(f426,plain,
    ( spl3_27
    | ~ spl3_12
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f252,f240,f139,f246])).

fof(f246,plain,
    ( spl3_27
  <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f139,plain,
    ( spl3_12
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f252,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_12
    | ~ spl3_25 ),
    inference(superposition,[],[f140,f241])).

fof(f140,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f139])).

fof(f413,plain,
    ( ~ spl3_14
    | ~ spl3_43 ),
    inference(avatar_contradiction_clause,[],[f411])).

fof(f411,plain,
    ( $false
    | ~ spl3_14
    | ~ spl3_43 ),
    inference(subsumption_resolution,[],[f156,f404])).

fof(f404,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f403])).

fof(f403,plain,
    ( spl3_43
  <=> ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f410,plain,
    ( spl3_43
    | ~ spl3_19
    | ~ spl3_30
    | spl3_44
    | spl3_31
    | ~ spl3_6
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f399,f263,f112,f271,f406,f267,f190,f403])).

fof(f190,plain,
    ( spl3_19
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f271,plain,
    ( spl3_31
  <=> v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f399,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(sK2)
        | v1_xboole_0(k2_relat_1(sK2))
        | k2_struct_0(sK0) = k1_relat_1(sK2)
        | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
        | ~ v1_relat_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X1))) )
    | ~ spl3_29 ),
    inference(resolution,[],[f378,f264])).

fof(f378,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | v1_xboole_0(X2)
      | k1_relat_1(X0) = X1
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ),
    inference(resolution,[],[f303,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f303,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_relat_1(X0,X1)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_xboole_0(X2)
      | k1_relat_1(X0) = X1
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f79,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f395,plain,
    ( ~ spl3_6
    | ~ spl3_30
    | ~ spl3_2
    | spl3_42
    | ~ spl3_20
    | ~ spl3_27
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f394,f263,f246,f194,f388,f96,f267,f112])).

fof(f394,plain,
    ( v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_20
    | ~ spl3_27
    | ~ spl3_29 ),
    inference(forward_demodulation,[],[f393,f195])).

fof(f393,plain,
    ( ~ v2_funct_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_27
    | ~ spl3_29 ),
    inference(trivial_inequality_removal,[],[f392])).

fof(f392,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_27
    | ~ spl3_29 ),
    inference(forward_demodulation,[],[f380,f247])).

fof(f247,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f246])).

fof(f380,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_29 ),
    inference(resolution,[],[f86,f264])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | v1_funct_2(k2_funct_1(X2),X1,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f324,plain,(
    spl3_36 ),
    inference(avatar_contradiction_clause,[],[f323])).

fof(f323,plain,
    ( $false
    | spl3_36 ),
    inference(resolution,[],[f317,f65])).

fof(f65,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f317,plain,
    ( ~ v2_funct_1(k6_relat_1(k2_relat_1(sK2)))
    | spl3_36 ),
    inference(avatar_component_clause,[],[f316])).

fof(f316,plain,
    ( spl3_36
  <=> v2_funct_1(k6_relat_1(k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f321,plain,
    ( ~ spl3_19
    | spl3_35 ),
    inference(avatar_split_clause,[],[f320,f313,f190])).

fof(f320,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_35 ),
    inference(trivial_inequality_removal,[],[f319])).

fof(f319,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_35 ),
    inference(superposition,[],[f314,f68])).

fof(f68,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f314,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2))
    | spl3_35 ),
    inference(avatar_component_clause,[],[f313])).

fof(f318,plain,
    ( ~ spl3_19
    | ~ spl3_6
    | ~ spl3_22
    | ~ spl3_21
    | spl3_34
    | ~ spl3_35
    | ~ spl3_36
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f308,f299,f316,f313,f310,f209,f213,f112,f190])).

fof(f213,plain,
    ( spl3_22
  <=> v1_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f299,plain,
    ( spl3_33
  <=> k6_relat_1(k2_relat_1(sK2)) = k5_relat_1(k4_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f308,plain,
    ( ~ v2_funct_1(k6_relat_1(k2_relat_1(sK2)))
    | k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2))
    | v2_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_33 ),
    inference(superposition,[],[f76,f300])).

fof(f300,plain,
    ( k6_relat_1(k2_relat_1(sK2)) = k5_relat_1(k4_relat_1(sK2),sK2)
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f299])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(k5_relat_1(X1,X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

fof(f301,plain,
    ( ~ spl3_19
    | ~ spl3_6
    | spl3_33
    | ~ spl3_2
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f297,f194,f96,f299,f112,f190])).

fof(f297,plain,
    ( k6_relat_1(k2_relat_1(sK2)) = k5_relat_1(k4_relat_1(sK2),sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_2
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f295,f195])).

fof(f295,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f75,f97])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f273,plain,
    ( ~ spl3_31
    | spl3_16
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f256,f240,f166,f271])).

fof(f166,plain,
    ( spl3_16
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f256,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | spl3_16
    | ~ spl3_25 ),
    inference(superposition,[],[f167,f241])).

fof(f167,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | spl3_16 ),
    inference(avatar_component_clause,[],[f166])).

fof(f269,plain,
    ( spl3_30
    | ~ spl3_15
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f255,f240,f160,f267])).

fof(f160,plain,
    ( spl3_15
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f255,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_15
    | ~ spl3_25 ),
    inference(superposition,[],[f161,f241])).

fof(f161,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f160])).

fof(f251,plain,
    ( spl3_25
    | ~ spl3_12
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f249,f236,f139,f240])).

fof(f236,plain,
    ( spl3_24
  <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f249,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_12
    | ~ spl3_24 ),
    inference(superposition,[],[f140,f237])).

fof(f237,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f236])).

fof(f238,plain,
    ( spl3_24
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f234,f155,f236])).

fof(f234,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_14 ),
    inference(resolution,[],[f83,f156])).

fof(f222,plain,
    ( ~ spl3_19
    | ~ spl3_6
    | spl3_23
    | ~ spl3_2
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f218,f194,f96,f220,f112,f190])).

fof(f218,plain,
    ( sK2 = k2_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_2
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f216,f195])).

fof(f216,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f73,f97])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f215,plain,
    ( ~ spl3_19
    | ~ spl3_6
    | spl3_22
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f207,f194,f213,f112,f190])).

fof(f207,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_20 ),
    inference(superposition,[],[f70,f195])).

fof(f70,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f211,plain,
    ( ~ spl3_19
    | ~ spl3_6
    | spl3_21
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f206,f194,f209,f112,f190])).

fof(f206,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_20 ),
    inference(superposition,[],[f71,f195])).

fof(f71,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f205,plain,
    ( spl3_14
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f204,f135,f131,f104,f155])).

fof(f104,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f131,plain,
    ( spl3_10
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f135,plain,
    ( spl3_11
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f204,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f203,f136])).

fof(f136,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f135])).

fof(f203,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f105,f132])).

fof(f132,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f131])).

fof(f105,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f201,plain,
    ( ~ spl3_4
    | spl3_19 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | ~ spl3_4
    | spl3_19 ),
    inference(subsumption_resolution,[],[f105,f198])).

fof(f198,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl3_19 ),
    inference(resolution,[],[f191,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f191,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_19 ),
    inference(avatar_component_clause,[],[f190])).

fof(f196,plain,
    ( ~ spl3_19
    | ~ spl3_6
    | spl3_20
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f187,f96,f194,f112,f190])).

fof(f187,plain,
    ( k4_relat_1(sK2) = k2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f72,f97])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f168,plain,
    ( spl3_8
    | ~ spl3_7
    | ~ spl3_16
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f145,f131,f166,f116,f120])).

fof(f120,plain,
    ( spl3_8
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f116,plain,
    ( spl3_7
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f145,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_10 ),
    inference(superposition,[],[f69,f132])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f162,plain,
    ( spl3_15
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f158,f135,f131,f108,f160])).

fof(f108,plain,
    ( spl3_5
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f158,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f144,f136])).

fof(f144,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(superposition,[],[f109,f132])).

fof(f109,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f108])).

fof(f152,plain,
    ( spl3_12
    | ~ spl3_3
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f151,f135,f131,f100,f139])).

fof(f100,plain,
    ( spl3_3
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f151,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_3
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f142,f136])).

fof(f142,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(superposition,[],[f101,f132])).

fof(f101,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f100])).

fof(f150,plain,
    ( ~ spl3_13
    | spl3_1
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f146,f135,f131,f92,f148])).

fof(f92,plain,
    ( spl3_1
  <=> r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f146,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | spl3_1
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f141,f136])).

fof(f141,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | spl3_1
    | ~ spl3_10 ),
    inference(superposition,[],[f93,f132])).

fof(f93,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f137,plain,
    ( spl3_11
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f129,f124,f135])).

fof(f124,plain,
    ( spl3_9
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f129,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_9 ),
    inference(resolution,[],[f66,f125])).

fof(f125,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f124])).

fof(f66,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f133,plain,
    ( spl3_10
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f128,f116,f131])).

fof(f128,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f66,f117])).

fof(f117,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f116])).

fof(f126,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f55,f124])).

fof(f55,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f52,f51,f50])).

fof(f50,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
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
              ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2)
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2)
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X2] :
        ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2)
        & v2_funct_1(X2)
        & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
      & v2_funct_1(sK2)
      & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
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
                 => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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
               => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

fof(f122,plain,(
    ~ spl3_8 ),
    inference(avatar_split_clause,[],[f56,f120])).

fof(f56,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f118,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f57,f116])).

fof(f57,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f114,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f58,f112])).

fof(f58,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f110,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f59,f108])).

fof(f59,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f53])).

fof(f106,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f60,f104])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f53])).

fof(f102,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f61,f100])).

fof(f61,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f98,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f62,f96])).

fof(f62,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f94,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f63,f92])).

fof(f63,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:05:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.44  % (30748)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.45  % (30748)Refutation not found, incomplete strategy% (30748)------------------------------
% 0.20/0.45  % (30748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (30757)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.46  % (30748)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (30748)Memory used [KB]: 6524
% 0.20/0.46  % (30748)Time elapsed: 0.066 s
% 0.20/0.46  % (30748)------------------------------
% 0.20/0.46  % (30748)------------------------------
% 0.20/0.47  % (30755)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.47  % (30754)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (30750)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.48  % (30763)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.48  % (30759)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.49  % (30753)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (30762)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (30751)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (30749)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (30766)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.50  % (30765)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.50  % (30761)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.50  % (30754)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f582,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f94,f98,f102,f106,f110,f114,f118,f122,f126,f133,f137,f150,f152,f162,f168,f196,f201,f205,f211,f215,f222,f238,f251,f269,f273,f301,f318,f321,f324,f395,f410,f413,f426,f428,f443,f455,f459,f476,f487,f488,f514,f536,f541,f555,f560,f568,f573,f579,f581])).
% 0.20/0.50  % (30749)Refutation not found, incomplete strategy% (30749)------------------------------
% 0.20/0.50  % (30749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (30749)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  fof(f581,plain,(
% 0.20/0.50    ~spl3_52 | ~spl3_6 | ~spl3_48 | ~spl3_60),
% 0.20/0.50    inference(avatar_split_clause,[],[f580,f577,f446,f112,f485])).
% 0.20/0.50  % (30749)Memory used [KB]: 10746
% 0.20/0.50  % (30749)Time elapsed: 0.094 s
% 0.20/0.50  % (30749)------------------------------
% 0.20/0.50  % (30749)------------------------------
% 0.20/0.50  fof(f485,plain,(
% 0.20/0.50    spl3_52 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 0.20/0.50  fof(f112,plain,(
% 0.20/0.50    spl3_6 <=> v1_funct_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.50  fof(f446,plain,(
% 0.20/0.50    spl3_48 <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.20/0.50  fof(f577,plain,(
% 0.20/0.50    spl3_60 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).
% 0.20/0.50  fof(f580,plain,(
% 0.20/0.50    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_48 | ~spl3_60)),
% 0.20/0.50    inference(resolution,[],[f578,f447])).
% 0.20/0.50  fof(f447,plain,(
% 0.20/0.50    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl3_48),
% 0.20/0.50    inference(avatar_component_clause,[],[f446])).
% 0.20/0.50  fof(f578,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))) ) | ~spl3_60),
% 0.20/0.50    inference(avatar_component_clause,[],[f577])).
% 0.20/0.50  fof(f579,plain,(
% 0.20/0.50    ~spl3_6 | ~spl3_48 | ~spl3_52 | spl3_60 | spl3_59),
% 0.20/0.50    inference(avatar_split_clause,[],[f574,f571,f577,f485,f446,f112])).
% 0.20/0.50  fof(f571,plain,(
% 0.20/0.50    spl3_59 <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 0.20/0.50  fof(f574,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2)) ) | spl3_59),
% 0.20/0.50    inference(resolution,[],[f572,f89])).
% 0.20/0.50  fof(f89,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f49])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.50    inference(flattening,[],[f48])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f13])).
% 0.20/0.50  fof(f13,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).
% 0.20/0.50  fof(f572,plain,(
% 0.20/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | spl3_59),
% 0.20/0.50    inference(avatar_component_clause,[],[f571])).
% 0.20/0.50  fof(f573,plain,(
% 0.20/0.50    ~spl3_59 | spl3_57 | ~spl3_58),
% 0.20/0.50    inference(avatar_split_clause,[],[f569,f565,f558,f571])).
% 0.20/0.50  fof(f558,plain,(
% 0.20/0.50    spl3_57 <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 0.20/0.50  fof(f565,plain,(
% 0.20/0.50    spl3_58 <=> sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 0.20/0.50  fof(f569,plain,(
% 0.20/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | (spl3_57 | ~spl3_58)),
% 0.20/0.50    inference(superposition,[],[f559,f566])).
% 0.20/0.50  fof(f566,plain,(
% 0.20/0.50    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) | ~spl3_58),
% 0.20/0.50    inference(avatar_component_clause,[],[f565])).
% 0.20/0.50  fof(f559,plain,(
% 0.20/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)),sK2) | spl3_57),
% 0.20/0.50    inference(avatar_component_clause,[],[f558])).
% 0.20/0.50  fof(f568,plain,(
% 0.20/0.50    spl3_58 | ~spl3_50 | ~spl3_51 | ~spl3_53 | ~spl3_55),
% 0.20/0.50    inference(avatar_split_clause,[],[f563,f539,f512,f473,f457,f565])).
% 0.20/0.50  fof(f457,plain,(
% 0.20/0.50    spl3_50 <=> v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 0.20/0.50  fof(f473,plain,(
% 0.20/0.50    spl3_51 <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 0.20/0.50  fof(f512,plain,(
% 0.20/0.50    spl3_53 <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 0.20/0.50  fof(f539,plain,(
% 0.20/0.50    spl3_55 <=> ! [X5,X6] : (sK2 = k2_tops_2(X5,X6,k4_relat_1(sK2)) | ~v1_funct_2(k4_relat_1(sK2),X5,X6) | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | k2_relset_1(X5,X6,k4_relat_1(sK2)) != X6)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 0.20/0.50  fof(f563,plain,(
% 0.20/0.50    ~v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) | (~spl3_51 | ~spl3_53 | ~spl3_55)),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f562])).
% 0.20/0.50  fof(f562,plain,(
% 0.20/0.50    k1_relat_1(sK2) != k1_relat_1(sK2) | ~v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) | (~spl3_51 | ~spl3_53 | ~spl3_55)),
% 0.20/0.50    inference(forward_demodulation,[],[f561,f513])).
% 0.20/0.50  fof(f513,plain,(
% 0.20/0.50    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) | ~spl3_53),
% 0.20/0.50    inference(avatar_component_clause,[],[f512])).
% 0.20/0.50  fof(f561,plain,(
% 0.20/0.50    ~v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) | (~spl3_51 | ~spl3_55)),
% 0.20/0.50    inference(resolution,[],[f540,f474])).
% 0.20/0.50  fof(f474,plain,(
% 0.20/0.50    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl3_51),
% 0.20/0.50    inference(avatar_component_clause,[],[f473])).
% 0.20/0.50  fof(f540,plain,(
% 0.20/0.50    ( ! [X6,X5] : (~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_2(k4_relat_1(sK2),X5,X6) | sK2 = k2_tops_2(X5,X6,k4_relat_1(sK2)) | k2_relset_1(X5,X6,k4_relat_1(sK2)) != X6) ) | ~spl3_55),
% 0.20/0.50    inference(avatar_component_clause,[],[f539])).
% 0.20/0.50  fof(f560,plain,(
% 0.20/0.50    ~spl3_57 | spl3_47 | ~spl3_56),
% 0.20/0.50    inference(avatar_split_clause,[],[f556,f550,f441,f558])).
% 0.20/0.50  fof(f441,plain,(
% 0.20/0.50    spl3_47 <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.20/0.50  fof(f550,plain,(
% 0.20/0.50    spl3_56 <=> k4_relat_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 0.20/0.50  fof(f556,plain,(
% 0.20/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)),sK2) | (spl3_47 | ~spl3_56)),
% 0.20/0.50    inference(superposition,[],[f442,f551])).
% 0.20/0.50  fof(f551,plain,(
% 0.20/0.50    k4_relat_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_56),
% 0.20/0.50    inference(avatar_component_clause,[],[f550])).
% 0.20/0.50  fof(f442,plain,(
% 0.20/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2) | spl3_47),
% 0.20/0.50    inference(avatar_component_clause,[],[f441])).
% 0.20/0.50  fof(f555,plain,(
% 0.20/0.50    spl3_56 | ~spl3_48 | ~spl3_45 | ~spl3_52 | ~spl3_54),
% 0.20/0.50    inference(avatar_split_clause,[],[f554,f534,f485,f416,f446,f550])).
% 0.20/0.50  fof(f416,plain,(
% 0.20/0.50    spl3_45 <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.20/0.50  fof(f534,plain,(
% 0.20/0.50    spl3_54 <=> ! [X1,X0] : (k4_relat_1(sK2) = k2_tops_2(X0,X1,sK2) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 0.20/0.50  fof(f554,plain,(
% 0.20/0.50    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k4_relat_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_45 | ~spl3_52 | ~spl3_54)),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f553])).
% 0.20/0.50  fof(f553,plain,(
% 0.20/0.50    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k4_relat_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_45 | ~spl3_52 | ~spl3_54)),
% 0.20/0.50    inference(forward_demodulation,[],[f543,f417])).
% 0.20/0.50  fof(f417,plain,(
% 0.20/0.50    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_45),
% 0.20/0.50    inference(avatar_component_clause,[],[f416])).
% 0.20/0.50  fof(f543,plain,(
% 0.20/0.50    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k4_relat_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_52 | ~spl3_54)),
% 0.20/0.50    inference(resolution,[],[f535,f486])).
% 0.20/0.50  fof(f486,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl3_52),
% 0.20/0.50    inference(avatar_component_clause,[],[f485])).
% 0.20/0.50  fof(f535,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k4_relat_1(sK2) = k2_tops_2(X0,X1,sK2) | k2_relset_1(X0,X1,sK2) != X1) ) | ~spl3_54),
% 0.20/0.50    inference(avatar_component_clause,[],[f534])).
% 0.20/0.50  fof(f541,plain,(
% 0.20/0.50    ~spl3_21 | spl3_55 | ~spl3_23 | ~spl3_34),
% 0.20/0.50    inference(avatar_split_clause,[],[f537,f310,f220,f539,f209])).
% 0.20/0.50  fof(f209,plain,(
% 0.20/0.50    spl3_21 <=> v1_funct_1(k4_relat_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.50  fof(f220,plain,(
% 0.20/0.50    spl3_23 <=> sK2 = k2_funct_1(k4_relat_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.20/0.50  fof(f310,plain,(
% 0.20/0.50    spl3_34 <=> v2_funct_1(k4_relat_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.20/0.50  fof(f537,plain,(
% 0.20/0.50    ( ! [X6,X5] : (sK2 = k2_tops_2(X5,X6,k4_relat_1(sK2)) | k2_relset_1(X5,X6,k4_relat_1(sK2)) != X6 | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_2(k4_relat_1(sK2),X5,X6) | ~v1_funct_1(k4_relat_1(sK2))) ) | (~spl3_23 | ~spl3_34)),
% 0.20/0.50    inference(forward_demodulation,[],[f531,f221])).
% 0.20/0.50  fof(f221,plain,(
% 0.20/0.50    sK2 = k2_funct_1(k4_relat_1(sK2)) | ~spl3_23),
% 0.20/0.50    inference(avatar_component_clause,[],[f220])).
% 0.20/0.50  fof(f531,plain,(
% 0.20/0.50    ( ! [X6,X5] : (k2_funct_1(k4_relat_1(sK2)) = k2_tops_2(X5,X6,k4_relat_1(sK2)) | k2_relset_1(X5,X6,k4_relat_1(sK2)) != X6 | ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_2(k4_relat_1(sK2),X5,X6) | ~v1_funct_1(k4_relat_1(sK2))) ) | ~spl3_34),
% 0.20/0.50    inference(resolution,[],[f88,f311])).
% 0.20/0.50  fof(f311,plain,(
% 0.20/0.50    v2_funct_1(k4_relat_1(sK2)) | ~spl3_34),
% 0.20/0.50    inference(avatar_component_clause,[],[f310])).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.50    inference(flattening,[],[f46])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f17])).
% 0.20/0.50  fof(f17,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.20/0.50  fof(f536,plain,(
% 0.20/0.50    ~spl3_6 | spl3_54 | ~spl3_2 | ~spl3_20),
% 0.20/0.50    inference(avatar_split_clause,[],[f532,f194,f96,f534,f112])).
% 0.20/0.50  fof(f96,plain,(
% 0.20/0.50    spl3_2 <=> v2_funct_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.50  fof(f194,plain,(
% 0.20/0.50    spl3_20 <=> k4_relat_1(sK2) = k2_funct_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.50  fof(f532,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k4_relat_1(sK2) = k2_tops_2(X0,X1,sK2) | k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) ) | (~spl3_2 | ~spl3_20)),
% 0.20/0.50    inference(forward_demodulation,[],[f529,f195])).
% 0.20/0.50  fof(f195,plain,(
% 0.20/0.50    k4_relat_1(sK2) = k2_funct_1(sK2) | ~spl3_20),
% 0.20/0.50    inference(avatar_component_clause,[],[f194])).
% 0.20/0.50  fof(f529,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) ) | ~spl3_2),
% 0.20/0.50    inference(resolution,[],[f88,f97])).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    v2_funct_1(sK2) | ~spl3_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f96])).
% 0.20/0.50  fof(f514,plain,(
% 0.20/0.50    spl3_53 | ~spl3_35 | ~spl3_51),
% 0.20/0.50    inference(avatar_split_clause,[],[f510,f473,f313,f512])).
% 0.20/0.50  fof(f313,plain,(
% 0.20/0.50    spl3_35 <=> k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.20/0.50  fof(f510,plain,(
% 0.20/0.50    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) | (~spl3_35 | ~spl3_51)),
% 0.20/0.50    inference(forward_demodulation,[],[f505,f322])).
% 0.20/0.50  fof(f322,plain,(
% 0.20/0.50    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) | ~spl3_35),
% 0.20/0.50    inference(avatar_component_clause,[],[f313])).
% 0.20/0.50  fof(f505,plain,(
% 0.20/0.50    k2_relat_1(k4_relat_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) | ~spl3_51),
% 0.20/0.50    inference(resolution,[],[f474,f83])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.50  fof(f488,plain,(
% 0.20/0.50    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_struct_0(sK0) != k1_relat_1(sK2) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.20/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.50  fof(f487,plain,(
% 0.20/0.50    spl3_52 | ~spl3_29 | ~spl3_44),
% 0.20/0.50    inference(avatar_split_clause,[],[f465,f406,f263,f485])).
% 0.20/0.50  fof(f263,plain,(
% 0.20/0.50    spl3_29 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.20/0.50  fof(f406,plain,(
% 0.20/0.50    spl3_44 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 0.20/0.50  fof(f465,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_29 | ~spl3_44)),
% 0.20/0.50    inference(superposition,[],[f264,f407])).
% 0.20/0.50  fof(f407,plain,(
% 0.20/0.50    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_44),
% 0.20/0.50    inference(avatar_component_clause,[],[f406])).
% 0.20/0.50  fof(f264,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~spl3_29),
% 0.20/0.50    inference(avatar_component_clause,[],[f263])).
% 0.20/0.50  fof(f476,plain,(
% 0.20/0.50    ~spl3_6 | ~spl3_2 | spl3_51 | ~spl3_48 | ~spl3_20 | ~spl3_29 | ~spl3_44 | ~spl3_45),
% 0.20/0.50    inference(avatar_split_clause,[],[f471,f416,f406,f263,f194,f446,f473,f96,f112])).
% 0.20/0.50  fof(f471,plain,(
% 0.20/0.50    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl3_20 | ~spl3_29 | ~spl3_44 | ~spl3_45)),
% 0.20/0.50    inference(forward_demodulation,[],[f470,f407])).
% 0.20/0.50  fof(f470,plain,(
% 0.20/0.50    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v2_funct_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_20 | ~spl3_29 | ~spl3_44 | ~spl3_45)),
% 0.20/0.50    inference(forward_demodulation,[],[f469,f195])).
% 0.20/0.50  fof(f469,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v2_funct_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_29 | ~spl3_44 | ~spl3_45)),
% 0.20/0.50    inference(forward_demodulation,[],[f468,f407])).
% 0.20/0.50  fof(f468,plain,(
% 0.20/0.50    ~v2_funct_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_29 | ~spl3_44 | ~spl3_45)),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f467])).
% 0.20/0.50  fof(f467,plain,(
% 0.20/0.50    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v2_funct_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_29 | ~spl3_44 | ~spl3_45)),
% 0.20/0.50    inference(forward_demodulation,[],[f466,f417])).
% 0.20/0.50  fof(f466,plain,(
% 0.20/0.50    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_29 | ~spl3_44)),
% 0.20/0.50    inference(forward_demodulation,[],[f460,f407])).
% 0.20/0.50  fof(f460,plain,(
% 0.20/0.50    k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~spl3_29),
% 0.20/0.50    inference(resolution,[],[f264,f87])).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.50    inference(flattening,[],[f44])).
% 0.20/0.50  fof(f44,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.20/0.50  fof(f459,plain,(
% 0.20/0.50    spl3_50 | ~spl3_42 | ~spl3_44),
% 0.20/0.50    inference(avatar_split_clause,[],[f437,f406,f388,f457])).
% 0.20/0.50  fof(f388,plain,(
% 0.20/0.50    spl3_42 <=> v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.20/0.50  fof(f437,plain,(
% 0.20/0.50    v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | (~spl3_42 | ~spl3_44)),
% 0.20/0.50    inference(superposition,[],[f389,f407])).
% 0.20/0.50  fof(f389,plain,(
% 0.20/0.50    v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | ~spl3_42),
% 0.20/0.50    inference(avatar_component_clause,[],[f388])).
% 0.20/0.50  fof(f455,plain,(
% 0.20/0.50    spl3_48 | ~spl3_30 | ~spl3_44),
% 0.20/0.50    inference(avatar_split_clause,[],[f436,f406,f267,f446])).
% 0.20/0.50  fof(f267,plain,(
% 0.20/0.50    spl3_30 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.20/0.50  fof(f436,plain,(
% 0.20/0.50    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_30 | ~spl3_44)),
% 0.20/0.50    inference(superposition,[],[f268,f407])).
% 0.20/0.50  fof(f268,plain,(
% 0.20/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~spl3_30),
% 0.20/0.50    inference(avatar_component_clause,[],[f267])).
% 0.20/0.50  fof(f443,plain,(
% 0.20/0.50    ~spl3_47 | spl3_13 | ~spl3_25 | ~spl3_44),
% 0.20/0.50    inference(avatar_split_clause,[],[f439,f406,f240,f148,f441])).
% 0.20/0.50  fof(f148,plain,(
% 0.20/0.50    spl3_13 <=> r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.50  fof(f240,plain,(
% 0.20/0.50    spl3_25 <=> k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.20/0.50  fof(f439,plain,(
% 0.20/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2) | (spl3_13 | ~spl3_25 | ~spl3_44)),
% 0.20/0.50    inference(forward_demodulation,[],[f431,f241])).
% 0.20/0.50  fof(f241,plain,(
% 0.20/0.50    k2_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_25),
% 0.20/0.50    inference(avatar_component_clause,[],[f240])).
% 0.20/0.50  fof(f431,plain,(
% 0.20/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),sK2) | (spl3_13 | ~spl3_44)),
% 0.20/0.50    inference(superposition,[],[f149,f407])).
% 0.20/0.50  fof(f149,plain,(
% 0.20/0.50    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | spl3_13),
% 0.20/0.50    inference(avatar_component_clause,[],[f148])).
% 0.20/0.50  fof(f428,plain,(
% 0.20/0.50    spl3_29 | ~spl3_14 | ~spl3_25),
% 0.20/0.50    inference(avatar_split_clause,[],[f427,f240,f155,f263])).
% 0.20/0.50  fof(f155,plain,(
% 0.20/0.50    spl3_14 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.50  fof(f427,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | (~spl3_14 | ~spl3_25)),
% 0.20/0.50    inference(forward_demodulation,[],[f156,f241])).
% 0.20/0.50  fof(f156,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_14),
% 0.20/0.50    inference(avatar_component_clause,[],[f155])).
% 0.20/0.50  fof(f426,plain,(
% 0.20/0.50    spl3_27 | ~spl3_12 | ~spl3_25),
% 0.20/0.50    inference(avatar_split_clause,[],[f252,f240,f139,f246])).
% 0.20/0.50  fof(f246,plain,(
% 0.20/0.50    spl3_27 <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.20/0.50  fof(f139,plain,(
% 0.20/0.50    spl3_12 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.50  fof(f252,plain,(
% 0.20/0.50    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | (~spl3_12 | ~spl3_25)),
% 0.20/0.50    inference(superposition,[],[f140,f241])).
% 0.20/0.50  fof(f140,plain,(
% 0.20/0.50    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_12),
% 0.20/0.50    inference(avatar_component_clause,[],[f139])).
% 0.20/0.50  fof(f413,plain,(
% 0.20/0.50    ~spl3_14 | ~spl3_43),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f411])).
% 0.20/0.50  fof(f411,plain,(
% 0.20/0.50    $false | (~spl3_14 | ~spl3_43)),
% 0.20/0.50    inference(subsumption_resolution,[],[f156,f404])).
% 0.20/0.50  fof(f404,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))) ) | ~spl3_43),
% 0.20/0.50    inference(avatar_component_clause,[],[f403])).
% 0.20/0.50  fof(f403,plain,(
% 0.20/0.50    spl3_43 <=> ! [X0] : ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.20/0.50  fof(f410,plain,(
% 0.20/0.50    spl3_43 | ~spl3_19 | ~spl3_30 | spl3_44 | spl3_31 | ~spl3_6 | ~spl3_29),
% 0.20/0.50    inference(avatar_split_clause,[],[f399,f263,f112,f271,f406,f267,f190,f403])).
% 0.20/0.50  fof(f190,plain,(
% 0.20/0.50    spl3_19 <=> v1_relat_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.50  fof(f271,plain,(
% 0.20/0.50    spl3_31 <=> v1_xboole_0(k2_relat_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.20/0.50  fof(f399,plain,(
% 0.20/0.50    ( ! [X1] : (~v1_funct_1(sK2) | v1_xboole_0(k2_relat_1(sK2)) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X1)))) ) | ~spl3_29),
% 0.20/0.50    inference(resolution,[],[f378,f264])).
% 0.20/0.50  fof(f378,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | v1_xboole_0(X2) | k1_relat_1(X0) = X1 | ~v1_funct_2(X0,X1,X2) | ~v1_relat_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))) )),
% 0.20/0.50    inference(resolution,[],[f303,f84])).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.20/0.50    inference(pure_predicate_removal,[],[f9])).
% 0.20/0.50  fof(f9,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.50  fof(f303,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v4_relat_1(X0,X1) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_xboole_0(X2) | k1_relat_1(X0) = X1 | ~v1_funct_2(X0,X1,X2) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(resolution,[],[f79,f80])).
% 0.20/0.50  fof(f80,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | k1_relat_1(X1) = X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f54])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(nnf_transformation,[],[f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,axiom,(
% 0.20/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.20/0.50  fof(f79,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.50    inference(flattening,[],[f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.20/0.50  fof(f395,plain,(
% 0.20/0.50    ~spl3_6 | ~spl3_30 | ~spl3_2 | spl3_42 | ~spl3_20 | ~spl3_27 | ~spl3_29),
% 0.20/0.50    inference(avatar_split_clause,[],[f394,f263,f246,f194,f388,f96,f267,f112])).
% 0.20/0.50  fof(f394,plain,(
% 0.20/0.50    v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | ~v2_funct_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_20 | ~spl3_27 | ~spl3_29)),
% 0.20/0.50    inference(forward_demodulation,[],[f393,f195])).
% 0.20/0.50  fof(f393,plain,(
% 0.20/0.50    ~v2_funct_1(sK2) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_27 | ~spl3_29)),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f392])).
% 0.20/0.50  fof(f392,plain,(
% 0.20/0.50    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v2_funct_1(sK2) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_27 | ~spl3_29)),
% 0.20/0.50    inference(forward_demodulation,[],[f380,f247])).
% 0.20/0.50  fof(f247,plain,(
% 0.20/0.50    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_27),
% 0.20/0.50    inference(avatar_component_clause,[],[f246])).
% 0.20/0.50  fof(f380,plain,(
% 0.20/0.50    k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~spl3_29),
% 0.20/0.50    inference(resolution,[],[f86,f264])).
% 0.20/0.50  fof(f86,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f45])).
% 0.20/0.50  fof(f324,plain,(
% 0.20/0.50    spl3_36),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f323])).
% 0.20/0.50  fof(f323,plain,(
% 0.20/0.50    $false | spl3_36),
% 0.20/0.50    inference(resolution,[],[f317,f65])).
% 0.20/0.50  fof(f65,plain,(
% 0.20/0.50    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.20/0.50  fof(f317,plain,(
% 0.20/0.50    ~v2_funct_1(k6_relat_1(k2_relat_1(sK2))) | spl3_36),
% 0.20/0.50    inference(avatar_component_clause,[],[f316])).
% 0.20/0.50  fof(f316,plain,(
% 0.20/0.50    spl3_36 <=> v2_funct_1(k6_relat_1(k2_relat_1(sK2)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.20/0.50  fof(f321,plain,(
% 0.20/0.50    ~spl3_19 | spl3_35),
% 0.20/0.50    inference(avatar_split_clause,[],[f320,f313,f190])).
% 0.20/0.50  fof(f320,plain,(
% 0.20/0.50    ~v1_relat_1(sK2) | spl3_35),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f319])).
% 0.20/0.50  fof(f319,plain,(
% 0.20/0.50    k1_relat_1(sK2) != k1_relat_1(sK2) | ~v1_relat_1(sK2) | spl3_35),
% 0.20/0.50    inference(superposition,[],[f314,f68])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f24])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 0.20/0.50  fof(f314,plain,(
% 0.20/0.50    k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2)) | spl3_35),
% 0.20/0.50    inference(avatar_component_clause,[],[f313])).
% 0.20/0.50  fof(f318,plain,(
% 0.20/0.50    ~spl3_19 | ~spl3_6 | ~spl3_22 | ~spl3_21 | spl3_34 | ~spl3_35 | ~spl3_36 | ~spl3_33),
% 0.20/0.50    inference(avatar_split_clause,[],[f308,f299,f316,f313,f310,f209,f213,f112,f190])).
% 0.20/0.50  fof(f213,plain,(
% 0.20/0.50    spl3_22 <=> v1_relat_1(k4_relat_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.20/0.50  fof(f299,plain,(
% 0.20/0.50    spl3_33 <=> k6_relat_1(k2_relat_1(sK2)) = k5_relat_1(k4_relat_1(sK2),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.20/0.50  fof(f308,plain,(
% 0.20/0.50    ~v2_funct_1(k6_relat_1(k2_relat_1(sK2))) | k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2)) | v2_funct_1(k4_relat_1(sK2)) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_33),
% 0.20/0.50    inference(superposition,[],[f76,f300])).
% 0.20/0.50  fof(f300,plain,(
% 0.20/0.50    k6_relat_1(k2_relat_1(sK2)) = k5_relat_1(k4_relat_1(sK2),sK2) | ~spl3_33),
% 0.20/0.50    inference(avatar_component_clause,[],[f299])).
% 0.20/0.50  fof(f76,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v2_funct_1(k5_relat_1(X1,X0)) | k1_relat_1(X0) != k2_relat_1(X1) | v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).
% 0.20/0.50  fof(f301,plain,(
% 0.20/0.50    ~spl3_19 | ~spl3_6 | spl3_33 | ~spl3_2 | ~spl3_20),
% 0.20/0.50    inference(avatar_split_clause,[],[f297,f194,f96,f299,f112,f190])).
% 0.20/0.50  fof(f297,plain,(
% 0.20/0.50    k6_relat_1(k2_relat_1(sK2)) = k5_relat_1(k4_relat_1(sK2),sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_2 | ~spl3_20)),
% 0.20/0.50    inference(forward_demodulation,[],[f295,f195])).
% 0.20/0.50  fof(f295,plain,(
% 0.20/0.50    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_2),
% 0.20/0.50    inference(resolution,[],[f75,f97])).
% 0.20/0.50  fof(f75,plain,(
% 0.20/0.50    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f33])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.20/0.50  fof(f273,plain,(
% 0.20/0.50    ~spl3_31 | spl3_16 | ~spl3_25),
% 0.20/0.50    inference(avatar_split_clause,[],[f256,f240,f166,f271])).
% 0.20/0.50  fof(f166,plain,(
% 0.20/0.50    spl3_16 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.50  fof(f256,plain,(
% 0.20/0.50    ~v1_xboole_0(k2_relat_1(sK2)) | (spl3_16 | ~spl3_25)),
% 0.20/0.50    inference(superposition,[],[f167,f241])).
% 0.20/0.50  fof(f167,plain,(
% 0.20/0.50    ~v1_xboole_0(k2_struct_0(sK1)) | spl3_16),
% 0.20/0.50    inference(avatar_component_clause,[],[f166])).
% 0.20/0.50  fof(f269,plain,(
% 0.20/0.50    spl3_30 | ~spl3_15 | ~spl3_25),
% 0.20/0.50    inference(avatar_split_clause,[],[f255,f240,f160,f267])).
% 0.20/0.50  fof(f160,plain,(
% 0.20/0.50    spl3_15 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.50  fof(f255,plain,(
% 0.20/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_15 | ~spl3_25)),
% 0.20/0.50    inference(superposition,[],[f161,f241])).
% 0.20/0.50  fof(f161,plain,(
% 0.20/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_15),
% 0.20/0.50    inference(avatar_component_clause,[],[f160])).
% 0.20/0.50  fof(f251,plain,(
% 0.20/0.50    spl3_25 | ~spl3_12 | ~spl3_24),
% 0.20/0.50    inference(avatar_split_clause,[],[f249,f236,f139,f240])).
% 0.20/0.50  fof(f236,plain,(
% 0.20/0.50    spl3_24 <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.20/0.50  fof(f249,plain,(
% 0.20/0.50    k2_struct_0(sK1) = k2_relat_1(sK2) | (~spl3_12 | ~spl3_24)),
% 0.20/0.50    inference(superposition,[],[f140,f237])).
% 0.20/0.50  fof(f237,plain,(
% 0.20/0.50    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_24),
% 0.20/0.50    inference(avatar_component_clause,[],[f236])).
% 0.20/0.50  fof(f238,plain,(
% 0.20/0.50    spl3_24 | ~spl3_14),
% 0.20/0.50    inference(avatar_split_clause,[],[f234,f155,f236])).
% 0.20/0.50  fof(f234,plain,(
% 0.20/0.50    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_14),
% 0.20/0.50    inference(resolution,[],[f83,f156])).
% 0.20/0.50  fof(f222,plain,(
% 0.20/0.50    ~spl3_19 | ~spl3_6 | spl3_23 | ~spl3_2 | ~spl3_20),
% 0.20/0.50    inference(avatar_split_clause,[],[f218,f194,f96,f220,f112,f190])).
% 0.20/0.50  fof(f218,plain,(
% 0.20/0.50    sK2 = k2_funct_1(k4_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_2 | ~spl3_20)),
% 0.20/0.50    inference(forward_demodulation,[],[f216,f195])).
% 0.20/0.50  fof(f216,plain,(
% 0.20/0.50    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_2),
% 0.20/0.50    inference(resolution,[],[f73,f97])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f31])).
% 0.20/0.50  fof(f31,plain,(
% 0.20/0.50    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 0.20/0.50  fof(f215,plain,(
% 0.20/0.50    ~spl3_19 | ~spl3_6 | spl3_22 | ~spl3_20),
% 0.20/0.50    inference(avatar_split_clause,[],[f207,f194,f213,f112,f190])).
% 0.20/0.50  fof(f207,plain,(
% 0.20/0.50    v1_relat_1(k4_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_20),
% 0.20/0.50    inference(superposition,[],[f70,f195])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  fof(f28,plain,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.50  fof(f211,plain,(
% 0.20/0.50    ~spl3_19 | ~spl3_6 | spl3_21 | ~spl3_20),
% 0.20/0.50    inference(avatar_split_clause,[],[f206,f194,f209,f112,f190])).
% 0.20/0.50  fof(f206,plain,(
% 0.20/0.50    v1_funct_1(k4_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_20),
% 0.20/0.50    inference(superposition,[],[f71,f195])).
% 0.20/0.50  fof(f71,plain,(
% 0.20/0.50    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f28])).
% 0.20/0.50  fof(f205,plain,(
% 0.20/0.50    spl3_14 | ~spl3_4 | ~spl3_10 | ~spl3_11),
% 0.20/0.50    inference(avatar_split_clause,[],[f204,f135,f131,f104,f155])).
% 0.20/0.50  fof(f104,plain,(
% 0.20/0.50    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.50  fof(f131,plain,(
% 0.20/0.50    spl3_10 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.50  fof(f135,plain,(
% 0.20/0.50    spl3_11 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.50  fof(f204,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_4 | ~spl3_10 | ~spl3_11)),
% 0.20/0.50    inference(forward_demodulation,[],[f203,f136])).
% 0.20/0.50  fof(f136,plain,(
% 0.20/0.50    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_11),
% 0.20/0.50    inference(avatar_component_clause,[],[f135])).
% 0.20/0.50  fof(f203,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_4 | ~spl3_10)),
% 0.20/0.50    inference(forward_demodulation,[],[f105,f132])).
% 0.20/0.50  fof(f132,plain,(
% 0.20/0.50    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_10),
% 0.20/0.50    inference(avatar_component_clause,[],[f131])).
% 0.20/0.50  fof(f105,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_4),
% 0.20/0.50    inference(avatar_component_clause,[],[f104])).
% 0.20/0.50  fof(f201,plain,(
% 0.20/0.50    ~spl3_4 | spl3_19),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f199])).
% 0.20/0.50  fof(f199,plain,(
% 0.20/0.50    $false | (~spl3_4 | spl3_19)),
% 0.20/0.50    inference(subsumption_resolution,[],[f105,f198])).
% 0.20/0.50  fof(f198,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl3_19),
% 0.20/0.50    inference(resolution,[],[f191,f82])).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.50  fof(f191,plain,(
% 0.20/0.50    ~v1_relat_1(sK2) | spl3_19),
% 0.20/0.50    inference(avatar_component_clause,[],[f190])).
% 0.20/0.50  fof(f196,plain,(
% 0.20/0.50    ~spl3_19 | ~spl3_6 | spl3_20 | ~spl3_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f187,f96,f194,f112,f190])).
% 0.20/0.50  fof(f187,plain,(
% 0.20/0.50    k4_relat_1(sK2) = k2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_2),
% 0.20/0.50    inference(resolution,[],[f72,f97])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 0.20/0.50  fof(f168,plain,(
% 0.20/0.50    spl3_8 | ~spl3_7 | ~spl3_16 | ~spl3_10),
% 0.20/0.50    inference(avatar_split_clause,[],[f145,f131,f166,f116,f120])).
% 0.20/0.50  fof(f120,plain,(
% 0.20/0.50    spl3_8 <=> v2_struct_0(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.50  fof(f116,plain,(
% 0.20/0.50    spl3_7 <=> l1_struct_0(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.50  fof(f145,plain,(
% 0.20/0.50    ~v1_xboole_0(k2_struct_0(sK1)) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl3_10),
% 0.20/0.50    inference(superposition,[],[f69,f132])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,axiom,(
% 0.20/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.50  fof(f162,plain,(
% 0.20/0.50    spl3_15 | ~spl3_5 | ~spl3_10 | ~spl3_11),
% 0.20/0.50    inference(avatar_split_clause,[],[f158,f135,f131,f108,f160])).
% 0.20/0.50  fof(f108,plain,(
% 0.20/0.50    spl3_5 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.50  fof(f158,plain,(
% 0.20/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_5 | ~spl3_10 | ~spl3_11)),
% 0.20/0.50    inference(forward_demodulation,[],[f144,f136])).
% 0.20/0.50  fof(f144,plain,(
% 0.20/0.50    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_5 | ~spl3_10)),
% 0.20/0.50    inference(superposition,[],[f109,f132])).
% 0.20/0.50  fof(f109,plain,(
% 0.20/0.50    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f108])).
% 0.20/0.50  fof(f152,plain,(
% 0.20/0.50    spl3_12 | ~spl3_3 | ~spl3_10 | ~spl3_11),
% 0.20/0.50    inference(avatar_split_clause,[],[f151,f135,f131,f100,f139])).
% 0.20/0.50  fof(f100,plain,(
% 0.20/0.50    spl3_3 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.50  fof(f151,plain,(
% 0.20/0.50    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_3 | ~spl3_10 | ~spl3_11)),
% 0.20/0.50    inference(forward_demodulation,[],[f142,f136])).
% 0.20/0.50  fof(f142,plain,(
% 0.20/0.50    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_3 | ~spl3_10)),
% 0.20/0.50    inference(superposition,[],[f101,f132])).
% 0.20/0.50  fof(f101,plain,(
% 0.20/0.50    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl3_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f100])).
% 0.20/0.50  fof(f150,plain,(
% 0.20/0.50    ~spl3_13 | spl3_1 | ~spl3_10 | ~spl3_11),
% 0.20/0.50    inference(avatar_split_clause,[],[f146,f135,f131,f92,f148])).
% 0.20/0.50  fof(f92,plain,(
% 0.20/0.50    spl3_1 <=> r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.50  fof(f146,plain,(
% 0.20/0.50    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | (spl3_1 | ~spl3_10 | ~spl3_11)),
% 0.20/0.50    inference(forward_demodulation,[],[f141,f136])).
% 0.20/0.50  fof(f141,plain,(
% 0.20/0.50    ~r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | (spl3_1 | ~spl3_10)),
% 0.20/0.50    inference(superposition,[],[f93,f132])).
% 0.20/0.50  fof(f93,plain,(
% 0.20/0.50    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) | spl3_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f92])).
% 0.20/0.50  fof(f137,plain,(
% 0.20/0.50    spl3_11 | ~spl3_9),
% 0.20/0.50    inference(avatar_split_clause,[],[f129,f124,f135])).
% 0.20/0.50  fof(f124,plain,(
% 0.20/0.50    spl3_9 <=> l1_struct_0(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.50  fof(f129,plain,(
% 0.20/0.50    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_9),
% 0.20/0.50    inference(resolution,[],[f66,f125])).
% 0.20/0.50  fof(f125,plain,(
% 0.20/0.50    l1_struct_0(sK0) | ~spl3_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f124])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,axiom,(
% 0.20/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.50  fof(f133,plain,(
% 0.20/0.50    spl3_10 | ~spl3_7),
% 0.20/0.50    inference(avatar_split_clause,[],[f128,f116,f131])).
% 0.20/0.50  fof(f128,plain,(
% 0.20/0.50    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_7),
% 0.20/0.50    inference(resolution,[],[f66,f117])).
% 0.20/0.50  fof(f117,plain,(
% 0.20/0.50    l1_struct_0(sK1) | ~spl3_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f116])).
% 0.20/0.50  fof(f126,plain,(
% 0.20/0.50    spl3_9),
% 0.20/0.50    inference(avatar_split_clause,[],[f55,f124])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    l1_struct_0(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f53])).
% 0.20/0.50  fof(f53,plain,(
% 0.20/0.50    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f52,f51,f50])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,negated_conjecture,(
% 0.20/0.50    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.20/0.50    inference(negated_conjecture,[],[f18])).
% 0.20/0.50  fof(f18,conjecture,(
% 0.20/0.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).
% 0.20/0.50  fof(f122,plain,(
% 0.20/0.50    ~spl3_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f56,f120])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ~v2_struct_0(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f53])).
% 0.20/0.50  fof(f118,plain,(
% 0.20/0.50    spl3_7),
% 0.20/0.50    inference(avatar_split_clause,[],[f57,f116])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    l1_struct_0(sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f53])).
% 0.20/0.50  fof(f114,plain,(
% 0.20/0.50    spl3_6),
% 0.20/0.50    inference(avatar_split_clause,[],[f58,f112])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    v1_funct_1(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f53])).
% 0.20/0.50  fof(f110,plain,(
% 0.20/0.50    spl3_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f59,f108])).
% 0.20/0.50  fof(f59,plain,(
% 0.20/0.50    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.50    inference(cnf_transformation,[],[f53])).
% 0.20/0.50  fof(f106,plain,(
% 0.20/0.50    spl3_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f60,f104])).
% 0.20/0.50  fof(f60,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.50    inference(cnf_transformation,[],[f53])).
% 0.20/0.50  fof(f102,plain,(
% 0.20/0.50    spl3_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f61,f100])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f53])).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    spl3_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f62,f96])).
% 0.20/0.50  fof(f62,plain,(
% 0.20/0.50    v2_funct_1(sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f53])).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    ~spl3_1),
% 0.20/0.50    inference(avatar_split_clause,[],[f63,f92])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 0.20/0.50    inference(cnf_transformation,[],[f53])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (30754)------------------------------
% 0.20/0.50  % (30754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (30754)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (30754)Memory used [KB]: 11129
% 0.20/0.50  % (30754)Time elapsed: 0.071 s
% 0.20/0.50  % (30754)------------------------------
% 0.20/0.50  % (30754)------------------------------
% 0.20/0.50  % (30752)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (30760)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (30758)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.51  % (30756)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.51  % (30768)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.51  % (30764)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.51  % (30742)Success in time 0.161 s
%------------------------------------------------------------------------------
