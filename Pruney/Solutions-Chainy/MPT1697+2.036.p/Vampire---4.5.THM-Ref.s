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
% DateTime   : Thu Dec  3 13:17:32 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :  200 ( 496 expanded)
%              Number of leaves         :   53 ( 245 expanded)
%              Depth                    :   13
%              Number of atoms          : 1169 (4806 expanded)
%              Number of equality atoms :  197 ( 946 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (30205)Refutation not found, incomplete strategy% (30205)------------------------------
% (30205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f783,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f109,f113,f117,f121,f125,f129,f133,f137,f141,f145,f149,f153,f157,f171,f242,f327,f338,f341,f346,f359,f362,f366,f475,f480,f491,f492,f497,f498,f642,f766,f777,f782])).

fof(f782,plain,
    ( spl9_3
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_8
    | ~ spl9_29
    | ~ spl9_90 ),
    inference(avatar_split_clause,[],[f780,f775,f372,f123,f127,f119,f103])).

fof(f103,plain,
    ( spl9_3
  <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f119,plain,
    ( spl9_7
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f127,plain,
    ( spl9_9
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f123,plain,
    ( spl9_8
  <=> v1_funct_2(sK4,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f372,plain,
    ( spl9_29
  <=> k1_xboole_0 = k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f775,plain,
    ( spl9_90
  <=> ! [X1] :
        ( k1_xboole_0 != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_90])])).

fof(f780,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ spl9_8
    | ~ spl9_29
    | ~ spl9_90 ),
    inference(trivial_inequality_removal,[],[f779])).

fof(f779,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ spl9_8
    | ~ spl9_29
    | ~ spl9_90 ),
    inference(forward_demodulation,[],[f778,f373])).

fof(f373,plain,
    ( k1_xboole_0 = k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | ~ spl9_29 ),
    inference(avatar_component_clause,[],[f372])).

fof(f778,plain,
    ( ~ v1_funct_1(sK4)
    | k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ spl9_8
    | ~ spl9_90 ),
    inference(resolution,[],[f776,f124])).

fof(f124,plain,
    ( v1_funct_2(sK4,sK2,sK1)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f776,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | k1_xboole_0 != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3) )
    | ~ spl9_90 ),
    inference(avatar_component_clause,[],[f775])).

fof(f777,plain,
    ( spl9_14
    | spl9_90
    | ~ spl9_13
    | ~ spl9_31
    | ~ spl9_88 ),
    inference(avatar_split_clause,[],[f773,f764,f379,f143,f775,f147])).

fof(f147,plain,
    ( spl9_14
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f143,plain,
    ( spl9_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f379,plain,
    ( spl9_31
  <=> k1_xboole_0 = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f764,plain,
    ( spl9_88
  <=> ! [X1,X0] :
        ( v1_xboole_0(X0)
        | sK5 = k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ v1_funct_1(X1)
        | k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,X0,sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_88])])).

fof(f773,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3))
        | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | v1_xboole_0(sK2) )
    | ~ spl9_13
    | ~ spl9_31
    | ~ spl9_88 ),
    inference(forward_demodulation,[],[f768,f380])).

fof(f380,plain,
    ( k1_xboole_0 = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ spl9_31 ),
    inference(avatar_component_clause,[],[f379])).

fof(f768,plain,
    ( ! [X1] :
        ( sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3))
        | v1_xboole_0(sK2) )
    | ~ spl9_13
    | ~ spl9_88 ),
    inference(resolution,[],[f765,f144])).

fof(f144,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f143])).

fof(f765,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | sK5 = k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ v1_funct_1(X1)
        | k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,X0,sK3))
        | v1_xboole_0(X0) )
    | ~ spl9_88 ),
    inference(avatar_component_clause,[],[f764])).

fof(f766,plain,
    ( spl9_88
    | spl9_16
    | ~ spl9_11
    | ~ spl9_68 ),
    inference(avatar_split_clause,[],[f762,f640,f135,f155,f764])).

fof(f155,plain,
    ( spl9_16
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f135,plain,
    ( spl9_11
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f640,plain,
    ( spl9_68
  <=> ! [X1,X0,X2] :
        ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X2,X0,sK3))
        | v1_xboole_0(X2)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X2))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | sK5 = k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_68])])).

fof(f762,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(sK0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,X0,sK3))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | sK5 = k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),sK3) )
    | ~ spl9_11
    | ~ spl9_68 ),
    inference(resolution,[],[f641,f136])).

fof(f136,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f135])).

fof(f641,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X2))
        | v1_xboole_0(X2)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
        | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X2,X0,sK3))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | sK5 = k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3) )
    | ~ spl9_68 ),
    inference(avatar_component_clause,[],[f640])).

fof(f642,plain,
    ( spl9_15
    | spl9_12
    | ~ spl9_5
    | spl9_68
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f638,f115,f107,f640,f111,f139,f151])).

fof(f151,plain,
    ( spl9_15
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f139,plain,
    ( spl9_12
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f111,plain,
    ( spl9_5
  <=> v1_funct_2(sK5,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f107,plain,
    ( spl9_4
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f115,plain,
    ( spl9_6
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f638,plain,
    ( ! [X2,X0,X1] :
        ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X2,X0,sK3))
        | ~ v1_funct_2(sK5,sK3,sK1)
        | sK5 = k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X2))
        | v1_xboole_0(sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
        | v1_xboole_0(X0)
        | v1_xboole_0(sK1)
        | v1_xboole_0(X2) )
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(resolution,[],[f534,f108])).

fof(f108,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f534,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
        | k2_partfun1(X0,X1,X2,k9_subset_1(X3,X0,X4)) != k2_partfun1(X4,X1,sK5,k9_subset_1(X3,X0,X4))
        | ~ v1_funct_2(sK5,X4,X1)
        | sK5 = k2_partfun1(k4_subset_1(X3,X0,X4),X1,k1_tmap_1(X3,X1,X0,X4,X2,sK5),X4)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
        | v1_xboole_0(X4)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X3))
        | v1_xboole_0(X0)
        | v1_xboole_0(X1)
        | v1_xboole_0(X3) )
    | ~ spl9_6 ),
    inference(resolution,[],[f163,f116])).

fof(f116,plain,
    ( v1_funct_1(sK5)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f115])).

fof(f163,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f161,f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
        & v1_funct_2(X5,X3,X1)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(X4,X2,X1)
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tmap_1)).

fof(f161,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
      | ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f159,f87])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f159,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f94,f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f94,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
      | ~ m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
      | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
      | ~ v1_funct_1(X6)
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                  | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5
                                  | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4 )
                                & ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                    & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 )
                                  | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                              | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                              | ~ v1_funct_1(X6) )
                          | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          | ~ v1_funct_2(X5,X3,X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      | ~ v1_funct_2(X4,X2,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                  | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5
                                  | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4 )
                                & ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                    & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 )
                                  | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                              | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                              | ~ v1_funct_1(X6) )
                          | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          | ~ v1_funct_2(X5,X3,X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      | ~ v1_funct_2(X4,X2,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                              <=> ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                  & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                              | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                              | ~ v1_funct_1(X6) )
                          | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          | ~ v1_funct_2(X5,X3,X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      | ~ v1_funct_2(X4,X2,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                              <=> ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                  & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                              | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                              | ~ v1_funct_1(X6) )
                          | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          | ~ v1_funct_2(X5,X3,X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      | ~ v1_funct_2(X4,X2,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                        & v1_funct_2(X4,X2,X1)
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                            & v1_funct_2(X5,X3,X1)
                            & v1_funct_1(X5) )
                         => ( k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                           => ! [X6] :
                                ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                                  & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                                  & v1_funct_1(X6) )
                               => ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                <=> ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                    & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tmap_1)).

fof(f498,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | k1_xboole_0 = k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f497,plain,
    ( spl9_2
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_8
    | ~ spl9_29
    | ~ spl9_44 ),
    inference(avatar_split_clause,[],[f495,f489,f372,f123,f127,f119,f100])).

fof(f100,plain,
    ( spl9_2
  <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f489,plain,
    ( spl9_44
  <=> ! [X1] :
        ( k1_xboole_0 != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK2) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).

fof(f495,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl9_8
    | ~ spl9_29
    | ~ spl9_44 ),
    inference(trivial_inequality_removal,[],[f494])).

fof(f494,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl9_8
    | ~ spl9_29
    | ~ spl9_44 ),
    inference(forward_demodulation,[],[f493,f373])).

fof(f493,plain,
    ( ~ v1_funct_1(sK4)
    | k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ spl9_8
    | ~ spl9_44 ),
    inference(resolution,[],[f490,f124])).

fof(f490,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | k1_xboole_0 != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK2) = X1 )
    | ~ spl9_44 ),
    inference(avatar_component_clause,[],[f489])).

fof(f492,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | k1_xboole_0 = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f491,plain,
    ( spl9_14
    | spl9_44
    | ~ spl9_13
    | ~ spl9_31
    | ~ spl9_42 ),
    inference(avatar_split_clause,[],[f487,f478,f379,f143,f489,f147])).

fof(f478,plain,
    ( spl9_42
  <=> ! [X1,X0] :
        ( v1_xboole_0(X0)
        | k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),X0) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ v1_funct_1(X1)
        | k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,X0,sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f487,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3))
        | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK2) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | v1_xboole_0(sK2) )
    | ~ spl9_13
    | ~ spl9_31
    | ~ spl9_42 ),
    inference(forward_demodulation,[],[f482,f380])).

fof(f482,plain,
    ( ! [X1] :
        ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK2) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3))
        | v1_xboole_0(sK2) )
    | ~ spl9_13
    | ~ spl9_42 ),
    inference(resolution,[],[f479,f144])).

fof(f479,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),X0) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ v1_funct_1(X1)
        | k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,X0,sK3))
        | v1_xboole_0(X0) )
    | ~ spl9_42 ),
    inference(avatar_component_clause,[],[f478])).

fof(f480,plain,
    ( spl9_42
    | spl9_16
    | ~ spl9_11
    | ~ spl9_41 ),
    inference(avatar_split_clause,[],[f476,f473,f135,f155,f478])).

fof(f473,plain,
    ( spl9_41
  <=> ! [X1,X0,X2] :
        ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X2,X0,sK3))
        | v1_xboole_0(X2)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X2))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).

fof(f476,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(sK0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,X0,sK3))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),X0) = X1 )
    | ~ spl9_11
    | ~ spl9_41 ),
    inference(resolution,[],[f474,f136])).

fof(f474,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X2))
        | v1_xboole_0(X2)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
        | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X2,X0,sK3))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),X0) = X1 )
    | ~ spl9_41 ),
    inference(avatar_component_clause,[],[f473])).

fof(f475,plain,
    ( spl9_15
    | spl9_12
    | ~ spl9_5
    | spl9_41
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f471,f115,f107,f473,f111,f139,f151])).

fof(f471,plain,
    ( ! [X2,X0,X1] :
        ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X2,X0,sK3))
        | ~ v1_funct_2(sK5,sK3,sK1)
        | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),X0) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X2))
        | v1_xboole_0(sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
        | v1_xboole_0(X0)
        | v1_xboole_0(sK1)
        | v1_xboole_0(X2) )
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(resolution,[],[f468,f108])).

fof(f468,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
        | k2_partfun1(X0,X1,X2,k9_subset_1(X3,X0,X4)) != k2_partfun1(X4,X1,sK5,k9_subset_1(X3,X0,X4))
        | ~ v1_funct_2(sK5,X4,X1)
        | k2_partfun1(k4_subset_1(X3,X0,X4),X1,k1_tmap_1(X3,X1,X0,X4,X2,sK5),X0) = X2
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
        | v1_xboole_0(X4)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X3))
        | v1_xboole_0(X0)
        | v1_xboole_0(X1)
        | v1_xboole_0(X3) )
    | ~ spl9_6 ),
    inference(resolution,[],[f162,f116])).

fof(f162,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f160,f86])).

fof(f160,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
      | ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f158,f87])).

% (30205)Termination reason: Refutation not found, incomplete strategy

% (30205)Memory used [KB]: 11385
% (30205)Time elapsed: 0.199 s
% (30205)------------------------------
% (30205)------------------------------
fof(f158,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f95,f88])).

fof(f95,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
      | ~ m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4
      | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
      | ~ v1_funct_1(X6)
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f366,plain,
    ( ~ spl9_17
    | ~ spl9_11
    | spl9_27 ),
    inference(avatar_split_clause,[],[f364,f357,f135,f169])).

fof(f169,plain,
    ( spl9_17
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f357,plain,
    ( spl9_27
  <=> r1_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f364,plain,
    ( ~ r1_xboole_0(sK2,sK3)
    | ~ spl9_11
    | spl9_27 ),
    inference(resolution,[],[f358,f206])).

fof(f206,plain,
    ( ! [X6,X5] :
        ( r1_xboole_0(k9_subset_1(sK0,X5,sK3),X6)
        | ~ r1_xboole_0(X5,sK3) )
    | ~ spl9_11 ),
    inference(superposition,[],[f192,f199])).

fof(f199,plain,
    ( ! [X0] : k9_subset_1(sK0,X0,sK3) = k4_xboole_0(X0,k4_xboole_0(X0,sK3))
    | ~ spl9_11 ),
    inference(resolution,[],[f91,f136])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f83,f74])).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f192,plain,(
    ! [X4,X2,X3] :
      ( r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X4)
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(resolution,[],[f89,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK8(X0,X1),X1)
          & r2_hidden(sK8(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f25,f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f76,f74])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f24,f48])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f358,plain,
    ( ~ r1_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK4))
    | spl9_27 ),
    inference(avatar_component_clause,[],[f357])).

fof(f362,plain,
    ( ~ spl9_7
    | spl9_26 ),
    inference(avatar_contradiction_clause,[],[f361])).

fof(f361,plain,
    ( $false
    | ~ spl9_7
    | spl9_26 ),
    inference(subsumption_resolution,[],[f120,f360])).

fof(f360,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl9_26 ),
    inference(resolution,[],[f355,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f355,plain,
    ( ~ v1_relat_1(sK4)
    | spl9_26 ),
    inference(avatar_component_clause,[],[f354])).

fof(f354,plain,
    ( spl9_26
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f120,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f119])).

fof(f359,plain,
    ( ~ spl9_26
    | ~ spl9_27
    | spl9_24 ),
    inference(avatar_split_clause,[],[f352,f336,f357,f354])).

fof(f336,plain,
    ( spl9_24
  <=> k1_xboole_0 = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f352,plain,
    ( ~ r1_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | spl9_24 ),
    inference(trivial_inequality_removal,[],[f351])).

fof(f351,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | spl9_24 ),
    inference(superposition,[],[f337,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_relat_1(X0,X1) = k1_xboole_0
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k7_relat_1(X0,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(f337,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | spl9_24 ),
    inference(avatar_component_clause,[],[f336])).

fof(f346,plain,
    ( ~ spl9_17
    | ~ spl9_11
    | spl9_23 ),
    inference(avatar_split_clause,[],[f343,f333,f135,f169])).

fof(f333,plain,
    ( spl9_23
  <=> r1_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f343,plain,
    ( ~ r1_xboole_0(sK2,sK3)
    | ~ spl9_11
    | spl9_23 ),
    inference(resolution,[],[f334,f206])).

fof(f334,plain,
    ( ~ r1_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK5))
    | spl9_23 ),
    inference(avatar_component_clause,[],[f333])).

fof(f341,plain,
    ( ~ spl9_4
    | spl9_22 ),
    inference(avatar_contradiction_clause,[],[f340])).

fof(f340,plain,
    ( $false
    | ~ spl9_4
    | spl9_22 ),
    inference(subsumption_resolution,[],[f108,f339])).

fof(f339,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl9_22 ),
    inference(resolution,[],[f331,f84])).

fof(f331,plain,
    ( ~ v1_relat_1(sK5)
    | spl9_22 ),
    inference(avatar_component_clause,[],[f330])).

fof(f330,plain,
    ( spl9_22
  <=> v1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f338,plain,
    ( ~ spl9_22
    | ~ spl9_23
    | ~ spl9_24
    | spl9_21 ),
    inference(avatar_split_clause,[],[f328,f325,f336,f333,f330])).

fof(f325,plain,
    ( spl9_21
  <=> k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f328,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | ~ r1_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | spl9_21 ),
    inference(superposition,[],[f326,f70])).

fof(f326,plain,
    ( k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | spl9_21 ),
    inference(avatar_component_clause,[],[f325])).

fof(f327,plain,
    ( ~ spl9_9
    | ~ spl9_7
    | ~ spl9_21
    | spl9_20 ),
    inference(avatar_split_clause,[],[f321,f240,f325,f119,f127])).

fof(f240,plain,
    ( spl9_20
  <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f321,plain,
    ( k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | spl9_20 ),
    inference(superposition,[],[f241,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f241,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | spl9_20 ),
    inference(avatar_component_clause,[],[f240])).

fof(f242,plain,
    ( ~ spl9_6
    | ~ spl9_4
    | ~ spl9_20
    | spl9_1 ),
    inference(avatar_split_clause,[],[f236,f97,f240,f107,f115])).

fof(f97,plain,
    ( spl9_1
  <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f236,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_1(sK5)
    | spl9_1 ),
    inference(superposition,[],[f98,f85])).

fof(f98,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f171,plain,
    ( spl9_14
    | spl9_12
    | spl9_17
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f165,f131,f169,f139,f147])).

fof(f131,plain,
    ( spl9_10
  <=> r1_subset_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f165,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2)
    | ~ spl9_10 ),
    inference(resolution,[],[f81,f132])).

fof(f132,plain,
    ( r1_subset_1(sK2,sK3)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f131])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | r1_xboole_0(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(f157,plain,(
    ~ spl9_16 ),
    inference(avatar_split_clause,[],[f53,f155])).

fof(f53,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
      | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    & v1_funct_2(sK5,sK3,sK1)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & v1_funct_2(sK4,sK2,sK1)
    & v1_funct_1(sK4)
    & r1_subset_1(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(sK0))
    & ~ v1_xboole_0(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f19,f40,f39,f38,f37,f36,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
                              | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
                              | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                            & v1_funct_2(X5,X3,X1)
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                        & v1_funct_2(X4,X2,X1)
                        & v1_funct_1(X4) )
                    & r1_subset_1(X2,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(sK0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(sK0))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5
                          | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4
                          | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                        & v1_funct_2(X5,X3,X1)
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                    & v1_funct_2(X4,X2,X1)
                    & v1_funct_1(X4) )
                & r1_subset_1(X2,X3)
                & m1_subset_1(X3,k1_zfmisc_1(sK0))
                & ~ v1_xboole_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(sK0))
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X3) != X5
                        | k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X2) != X4
                        | k2_partfun1(X2,sK1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,X2,X3)) )
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1)))
                      & v1_funct_2(X5,X3,sK1)
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
                  & v1_funct_2(X4,X2,sK1)
                  & v1_funct_1(X4) )
              & r1_subset_1(X2,X3)
              & m1_subset_1(X3,k1_zfmisc_1(sK0))
              & ~ v1_xboole_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0))
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X3) != X5
                      | k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X2) != X4
                      | k2_partfun1(X2,sK1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,X2,X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1)))
                    & v1_funct_2(X5,X3,sK1)
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
                & v1_funct_2(X4,X2,sK1)
                & v1_funct_1(X4) )
            & r1_subset_1(X2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(sK0))
            & ~ v1_xboole_0(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0))
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),X3) != X5
                    | k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK2) != X4
                    | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,sK2,X3)) )
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1)))
                  & v1_funct_2(X5,X3,sK1)
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
              & v1_funct_2(X4,sK2,sK1)
              & v1_funct_1(X4) )
          & r1_subset_1(sK2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(sK0))
          & ~ v1_xboole_0(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0))
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),X3) != X5
                  | k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK2) != X4
                  | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,sK2,X3)) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1)))
                & v1_funct_2(X5,X3,sK1)
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
            & v1_funct_2(X4,sK2,sK1)
            & v1_funct_1(X4) )
        & r1_subset_1(sK2,X3)
        & m1_subset_1(X3,k1_zfmisc_1(sK0))
        & ~ v1_xboole_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK3) != X5
                | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK2) != X4
                | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
              & v1_funct_2(X5,sK3,sK1)
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
          & v1_funct_2(X4,sK2,sK1)
          & v1_funct_1(X4) )
      & r1_subset_1(sK2,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(sK0))
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK3) != X5
              | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK2) != X4
              | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
            & v1_funct_2(X5,sK3,sK1)
            & v1_funct_1(X5) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        & v1_funct_2(X4,sK2,sK1)
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK3) != X5
            | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK2)
            | k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
          & v1_funct_2(X5,sK3,sK1)
          & v1_funct_1(X5) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      & v1_funct_2(sK4,sK2,sK1)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X5] :
        ( ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK3) != X5
          | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK2)
          | k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) )
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
        & v1_funct_2(X5,sK3,sK1)
        & v1_funct_1(X5) )
   => ( ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
        | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
        | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      & v1_funct_2(sK5,sK3,sK1)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(X0))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(X0))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                      & ~ v1_xboole_0(X3) )
                   => ( r1_subset_1(X2,X3)
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                            & v1_funct_2(X4,X2,X1)
                            & v1_funct_1(X4) )
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                                & v1_funct_2(X5,X3,X1)
                                & v1_funct_1(X5) )
                             => ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
                                & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
                                & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                 => ( r1_subset_1(X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                          & v1_funct_2(X4,X2,X1)
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                              & v1_funct_2(X5,X3,X1)
                              & v1_funct_1(X5) )
                           => ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
                              & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
                              & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tmap_1)).

fof(f153,plain,(
    ~ spl9_15 ),
    inference(avatar_split_clause,[],[f54,f151])).

fof(f54,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f149,plain,(
    ~ spl9_14 ),
    inference(avatar_split_clause,[],[f55,f147])).

fof(f55,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f145,plain,(
    spl9_13 ),
    inference(avatar_split_clause,[],[f56,f143])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f141,plain,(
    ~ spl9_12 ),
    inference(avatar_split_clause,[],[f57,f139])).

fof(f57,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f137,plain,(
    spl9_11 ),
    inference(avatar_split_clause,[],[f58,f135])).

fof(f58,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f133,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f59,f131])).

fof(f59,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f129,plain,(
    spl9_9 ),
    inference(avatar_split_clause,[],[f60,f127])).

fof(f60,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f125,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f61,f123])).

fof(f61,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f121,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f62,f119])).

fof(f62,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f117,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f63,f115])).

fof(f63,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f41])).

fof(f113,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f64,f111])).

fof(f64,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f109,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f65,f107])).

fof(f65,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f105,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f66,f103,f100,f97])).

fof(f66,plain,
    ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:56:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (30201)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (30219)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (30216)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (30200)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (30199)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (30195)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (30224)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (30214)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (30208)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (30206)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (30198)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.38/0.53  % (30197)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.38/0.54  % (30223)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.38/0.54  % (30209)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.38/0.54  % (30207)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.38/0.54  % (30211)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.38/0.54  % (30222)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.38/0.54  % (30218)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.38/0.54  % (30210)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.38/0.55  % (30196)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.38/0.55  % (30217)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.38/0.55  % (30213)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.50/0.55  % (30212)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.50/0.55  % (30203)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.50/0.55  % (30202)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.50/0.55  % (30215)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.50/0.56  % (30220)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.50/0.56  % (30221)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.50/0.56  % (30204)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.50/0.56  % (30205)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.50/0.58  % (30217)Refutation not found, incomplete strategy% (30217)------------------------------
% 1.50/0.58  % (30217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.58  % (30217)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.58  
% 1.50/0.58  % (30217)Memory used [KB]: 11513
% 1.50/0.58  % (30217)Time elapsed: 0.171 s
% 1.50/0.58  % (30217)------------------------------
% 1.50/0.58  % (30217)------------------------------
% 1.50/0.61  % (30214)Refutation found. Thanks to Tanya!
% 1.50/0.61  % SZS status Theorem for theBenchmark
% 1.50/0.62  % SZS output start Proof for theBenchmark
% 1.50/0.62  % (30205)Refutation not found, incomplete strategy% (30205)------------------------------
% 1.50/0.62  % (30205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.62  fof(f783,plain,(
% 1.50/0.62    $false),
% 1.50/0.62    inference(avatar_sat_refutation,[],[f105,f109,f113,f117,f121,f125,f129,f133,f137,f141,f145,f149,f153,f157,f171,f242,f327,f338,f341,f346,f359,f362,f366,f475,f480,f491,f492,f497,f498,f642,f766,f777,f782])).
% 1.50/0.62  fof(f782,plain,(
% 1.50/0.62    spl9_3 | ~spl9_7 | ~spl9_9 | ~spl9_8 | ~spl9_29 | ~spl9_90),
% 1.50/0.62    inference(avatar_split_clause,[],[f780,f775,f372,f123,f127,f119,f103])).
% 1.50/0.62  fof(f103,plain,(
% 1.50/0.62    spl9_3 <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 1.50/0.62  fof(f119,plain,(
% 1.50/0.62    spl9_7 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 1.50/0.62  fof(f127,plain,(
% 1.50/0.62    spl9_9 <=> v1_funct_1(sK4)),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 1.50/0.62  fof(f123,plain,(
% 1.50/0.62    spl9_8 <=> v1_funct_2(sK4,sK2,sK1)),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 1.50/0.62  fof(f372,plain,(
% 1.50/0.62    spl9_29 <=> k1_xboole_0 = k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).
% 1.50/0.62  fof(f775,plain,(
% 1.50/0.62    spl9_90 <=> ! [X1] : (k1_xboole_0 != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3))),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl9_90])])).
% 1.50/0.62  fof(f780,plain,(
% 1.50/0.62    ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl9_8 | ~spl9_29 | ~spl9_90)),
% 1.50/0.62    inference(trivial_inequality_removal,[],[f779])).
% 1.50/0.62  fof(f779,plain,(
% 1.50/0.62    k1_xboole_0 != k1_xboole_0 | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl9_8 | ~spl9_29 | ~spl9_90)),
% 1.50/0.62    inference(forward_demodulation,[],[f778,f373])).
% 1.50/0.62  fof(f373,plain,(
% 1.50/0.62    k1_xboole_0 = k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) | ~spl9_29),
% 1.50/0.62    inference(avatar_component_clause,[],[f372])).
% 1.50/0.62  fof(f778,plain,(
% 1.50/0.62    ~v1_funct_1(sK4) | k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl9_8 | ~spl9_90)),
% 1.50/0.62    inference(resolution,[],[f776,f124])).
% 1.50/0.62  fof(f124,plain,(
% 1.50/0.62    v1_funct_2(sK4,sK2,sK1) | ~spl9_8),
% 1.50/0.62    inference(avatar_component_clause,[],[f123])).
% 1.50/0.62  fof(f776,plain,(
% 1.50/0.62    ( ! [X1] : (~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | k1_xboole_0 != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3)) ) | ~spl9_90),
% 1.50/0.62    inference(avatar_component_clause,[],[f775])).
% 1.50/0.62  fof(f777,plain,(
% 1.50/0.62    spl9_14 | spl9_90 | ~spl9_13 | ~spl9_31 | ~spl9_88),
% 1.50/0.62    inference(avatar_split_clause,[],[f773,f764,f379,f143,f775,f147])).
% 1.50/0.62  fof(f147,plain,(
% 1.50/0.62    spl9_14 <=> v1_xboole_0(sK2)),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 1.50/0.62  fof(f143,plain,(
% 1.50/0.62    spl9_13 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 1.50/0.62  fof(f379,plain,(
% 1.50/0.62    spl9_31 <=> k1_xboole_0 = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).
% 1.50/0.62  fof(f764,plain,(
% 1.50/0.62    spl9_88 <=> ! [X1,X0] : (v1_xboole_0(X0) | sK5 = k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~v1_funct_2(X1,X0,sK1) | ~v1_funct_1(X1) | k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,X0,sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)))),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl9_88])])).
% 1.50/0.62  fof(f773,plain,(
% 1.50/0.62    ( ! [X1] : (k1_xboole_0 != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | v1_xboole_0(sK2)) ) | (~spl9_13 | ~spl9_31 | ~spl9_88)),
% 1.50/0.62    inference(forward_demodulation,[],[f768,f380])).
% 1.50/0.62  fof(f380,plain,(
% 1.50/0.62    k1_xboole_0 = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~spl9_31),
% 1.50/0.62    inference(avatar_component_clause,[],[f379])).
% 1.50/0.62  fof(f768,plain,(
% 1.50/0.62    ( ! [X1] : (sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK2)) ) | (~spl9_13 | ~spl9_88)),
% 1.50/0.62    inference(resolution,[],[f765,f144])).
% 1.50/0.62  fof(f144,plain,(
% 1.50/0.62    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl9_13),
% 1.50/0.62    inference(avatar_component_clause,[],[f143])).
% 1.50/0.62  fof(f765,plain,(
% 1.50/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | sK5 = k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~v1_funct_2(X1,X0,sK1) | ~v1_funct_1(X1) | k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,X0,sK3)) | v1_xboole_0(X0)) ) | ~spl9_88),
% 1.50/0.62    inference(avatar_component_clause,[],[f764])).
% 1.50/0.62  fof(f766,plain,(
% 1.50/0.62    spl9_88 | spl9_16 | ~spl9_11 | ~spl9_68),
% 1.50/0.62    inference(avatar_split_clause,[],[f762,f640,f135,f155,f764])).
% 1.50/0.62  fof(f155,plain,(
% 1.50/0.62    spl9_16 <=> v1_xboole_0(sK0)),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 1.50/0.62  fof(f135,plain,(
% 1.50/0.62    spl9_11 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 1.50/0.62  fof(f640,plain,(
% 1.50/0.62    spl9_68 <=> ! [X1,X0,X2] : (k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X2,X0,sK3)) | v1_xboole_0(X2) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(X2)) | ~m1_subset_1(sK3,k1_zfmisc_1(X2)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | sK5 = k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3))),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl9_68])])).
% 1.50/0.62  fof(f762,plain,(
% 1.50/0.62    ( ! [X0,X1] : (v1_xboole_0(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,X0,sK3)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),sK3)) ) | (~spl9_11 | ~spl9_68)),
% 1.50/0.62    inference(resolution,[],[f641,f136])).
% 1.50/0.62  fof(f136,plain,(
% 1.50/0.62    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl9_11),
% 1.50/0.62    inference(avatar_component_clause,[],[f135])).
% 1.50/0.62  fof(f641,plain,(
% 1.50/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(X2)) | v1_xboole_0(X2) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(X2)) | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X2,X0,sK3)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | sK5 = k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3)) ) | ~spl9_68),
% 1.50/0.62    inference(avatar_component_clause,[],[f640])).
% 1.50/0.62  fof(f642,plain,(
% 1.50/0.62    spl9_15 | spl9_12 | ~spl9_5 | spl9_68 | ~spl9_4 | ~spl9_6),
% 1.50/0.62    inference(avatar_split_clause,[],[f638,f115,f107,f640,f111,f139,f151])).
% 1.50/0.62  fof(f151,plain,(
% 1.50/0.62    spl9_15 <=> v1_xboole_0(sK1)),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 1.50/0.62  fof(f139,plain,(
% 1.50/0.62    spl9_12 <=> v1_xboole_0(sK3)),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 1.50/0.62  fof(f111,plain,(
% 1.50/0.62    spl9_5 <=> v1_funct_2(sK5,sK3,sK1)),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 1.50/0.62  fof(f107,plain,(
% 1.50/0.62    spl9_4 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 1.50/0.62  fof(f115,plain,(
% 1.50/0.62    spl9_6 <=> v1_funct_1(sK5)),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 1.50/0.62  fof(f638,plain,(
% 1.50/0.62    ( ! [X2,X0,X1] : (k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X2,X0,sK3)) | ~v1_funct_2(sK5,sK3,sK1) | sK5 = k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~v1_funct_2(X1,X0,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(X2)) | v1_xboole_0(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(X2)) | v1_xboole_0(X0) | v1_xboole_0(sK1) | v1_xboole_0(X2)) ) | (~spl9_4 | ~spl9_6)),
% 1.50/0.62    inference(resolution,[],[f534,f108])).
% 1.50/0.62  fof(f108,plain,(
% 1.50/0.62    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~spl9_4),
% 1.50/0.62    inference(avatar_component_clause,[],[f107])).
% 1.50/0.62  fof(f534,plain,(
% 1.50/0.62    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) | k2_partfun1(X0,X1,X2,k9_subset_1(X3,X0,X4)) != k2_partfun1(X4,X1,sK5,k9_subset_1(X3,X0,X4)) | ~v1_funct_2(sK5,X4,X1) | sK5 = k2_partfun1(k4_subset_1(X3,X0,X4),X1,k1_tmap_1(X3,X1,X0,X4,X2,sK5),X4) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | ~m1_subset_1(X0,k1_zfmisc_1(X3)) | v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X3)) ) | ~spl9_6),
% 1.50/0.62    inference(resolution,[],[f163,f116])).
% 1.50/0.62  fof(f116,plain,(
% 1.50/0.62    v1_funct_1(sK5) | ~spl9_6),
% 1.50/0.62    inference(avatar_component_clause,[],[f115])).
% 1.50/0.62  fof(f163,plain,(
% 1.50/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.50/0.62    inference(subsumption_resolution,[],[f161,f86])).
% 1.50/0.62  fof(f86,plain,(
% 1.50/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.50/0.62    inference(cnf_transformation,[],[f34])).
% 1.50/0.62  fof(f34,plain,(
% 1.50/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.50/0.62    inference(flattening,[],[f33])).
% 1.50/0.62  fof(f33,plain,(
% 1.50/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.50/0.62    inference(ennf_transformation,[],[f13])).
% 1.50/0.62  fof(f13,axiom,(
% 1.50/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 1.50/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 1.50/0.62  fof(f161,plain,(
% 1.50/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.50/0.62    inference(subsumption_resolution,[],[f159,f87])).
% 1.50/0.62  fof(f87,plain,(
% 1.50/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.50/0.62    inference(cnf_transformation,[],[f34])).
% 1.50/0.62  fof(f159,plain,(
% 1.50/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.50/0.62    inference(subsumption_resolution,[],[f94,f88])).
% 1.50/0.62  fof(f88,plain,(
% 1.50/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.50/0.62    inference(cnf_transformation,[],[f34])).
% 1.50/0.62  fof(f94,plain,(
% 1.50/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.50/0.62    inference(equality_resolution,[],[f68])).
% 1.50/0.62  fof(f68,plain,(
% 1.50/0.62    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.50/0.62    inference(cnf_transformation,[],[f43])).
% 1.50/0.62  fof(f43,plain,(
% 1.50/0.62    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.50/0.62    inference(flattening,[],[f42])).
% 1.50/0.62  fof(f42,plain,(
% 1.50/0.62    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.50/0.62    inference(nnf_transformation,[],[f21])).
% 1.50/0.62  fof(f21,plain,(
% 1.50/0.62    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.50/0.62    inference(flattening,[],[f20])).
% 1.50/0.62  fof(f20,plain,(
% 1.50/0.62    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.50/0.62    inference(ennf_transformation,[],[f12])).
% 1.50/0.62  fof(f12,axiom,(
% 1.50/0.62    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 1.50/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tmap_1)).
% 1.50/0.62  fof(f498,plain,(
% 1.50/0.62    k1_xboole_0 != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | k1_xboole_0 = k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))),
% 1.50/0.62    introduced(theory_tautology_sat_conflict,[])).
% 1.50/0.62  fof(f497,plain,(
% 1.50/0.62    spl9_2 | ~spl9_7 | ~spl9_9 | ~spl9_8 | ~spl9_29 | ~spl9_44),
% 1.50/0.62    inference(avatar_split_clause,[],[f495,f489,f372,f123,f127,f119,f100])).
% 1.50/0.62  fof(f100,plain,(
% 1.50/0.62    spl9_2 <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.50/0.62  fof(f489,plain,(
% 1.50/0.62    spl9_44 <=> ! [X1] : (k1_xboole_0 != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK2) = X1)),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl9_44])])).
% 1.50/0.62  fof(f495,plain,(
% 1.50/0.62    ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl9_8 | ~spl9_29 | ~spl9_44)),
% 1.50/0.62    inference(trivial_inequality_removal,[],[f494])).
% 1.50/0.62  fof(f494,plain,(
% 1.50/0.62    k1_xboole_0 != k1_xboole_0 | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl9_8 | ~spl9_29 | ~spl9_44)),
% 1.50/0.62    inference(forward_demodulation,[],[f493,f373])).
% 1.50/0.62  fof(f493,plain,(
% 1.50/0.62    ~v1_funct_1(sK4) | k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | (~spl9_8 | ~spl9_44)),
% 1.50/0.62    inference(resolution,[],[f490,f124])).
% 1.50/0.62  fof(f490,plain,(
% 1.50/0.62    ( ! [X1] : (~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | k1_xboole_0 != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK2) = X1) ) | ~spl9_44),
% 1.50/0.62    inference(avatar_component_clause,[],[f489])).
% 1.50/0.62  fof(f492,plain,(
% 1.50/0.62    k1_xboole_0 != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | k1_xboole_0 = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 1.50/0.62    introduced(theory_tautology_sat_conflict,[])).
% 1.50/0.62  fof(f491,plain,(
% 1.50/0.62    spl9_14 | spl9_44 | ~spl9_13 | ~spl9_31 | ~spl9_42),
% 1.50/0.62    inference(avatar_split_clause,[],[f487,f478,f379,f143,f489,f147])).
% 1.50/0.62  fof(f478,plain,(
% 1.50/0.62    spl9_42 <=> ! [X1,X0] : (v1_xboole_0(X0) | k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),X0) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~v1_funct_2(X1,X0,sK1) | ~v1_funct_1(X1) | k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,X0,sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)))),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).
% 1.50/0.62  fof(f487,plain,(
% 1.50/0.62    ( ! [X1] : (k1_xboole_0 != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK2) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | v1_xboole_0(sK2)) ) | (~spl9_13 | ~spl9_31 | ~spl9_42)),
% 1.50/0.62    inference(forward_demodulation,[],[f482,f380])).
% 1.50/0.62  fof(f482,plain,(
% 1.50/0.62    ( ! [X1] : (k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK2) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK2)) ) | (~spl9_13 | ~spl9_42)),
% 1.50/0.62    inference(resolution,[],[f479,f144])).
% 1.50/0.62  fof(f479,plain,(
% 1.50/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),X0) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~v1_funct_2(X1,X0,sK1) | ~v1_funct_1(X1) | k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,X0,sK3)) | v1_xboole_0(X0)) ) | ~spl9_42),
% 1.50/0.62    inference(avatar_component_clause,[],[f478])).
% 1.50/0.62  fof(f480,plain,(
% 1.50/0.62    spl9_42 | spl9_16 | ~spl9_11 | ~spl9_41),
% 1.50/0.62    inference(avatar_split_clause,[],[f476,f473,f135,f155,f478])).
% 1.50/0.62  fof(f473,plain,(
% 1.50/0.62    spl9_41 <=> ! [X1,X0,X2] : (k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X2,X0,sK3)) | v1_xboole_0(X2) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(X2)) | ~m1_subset_1(sK3,k1_zfmisc_1(X2)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),X0) = X1)),
% 1.50/0.62    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).
% 1.50/0.62  fof(f476,plain,(
% 1.50/0.62    ( ! [X0,X1] : (v1_xboole_0(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,X0,sK3)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),X0) = X1) ) | (~spl9_11 | ~spl9_41)),
% 1.50/0.62    inference(resolution,[],[f474,f136])).
% 1.50/0.62  fof(f474,plain,(
% 1.50/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(X2)) | v1_xboole_0(X2) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(X2)) | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X2,X0,sK3)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),X0) = X1) ) | ~spl9_41),
% 1.50/0.62    inference(avatar_component_clause,[],[f473])).
% 1.50/0.62  fof(f475,plain,(
% 1.50/0.62    spl9_15 | spl9_12 | ~spl9_5 | spl9_41 | ~spl9_4 | ~spl9_6),
% 1.50/0.62    inference(avatar_split_clause,[],[f471,f115,f107,f473,f111,f139,f151])).
% 1.50/0.62  fof(f471,plain,(
% 1.50/0.62    ( ! [X2,X0,X1] : (k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X2,X0,sK3)) | ~v1_funct_2(sK5,sK3,sK1) | k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),X0) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~v1_funct_2(X1,X0,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(X2)) | v1_xboole_0(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(X2)) | v1_xboole_0(X0) | v1_xboole_0(sK1) | v1_xboole_0(X2)) ) | (~spl9_4 | ~spl9_6)),
% 1.50/0.62    inference(resolution,[],[f468,f108])).
% 1.50/0.62  fof(f468,plain,(
% 1.50/0.62    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) | k2_partfun1(X0,X1,X2,k9_subset_1(X3,X0,X4)) != k2_partfun1(X4,X1,sK5,k9_subset_1(X3,X0,X4)) | ~v1_funct_2(sK5,X4,X1) | k2_partfun1(k4_subset_1(X3,X0,X4),X1,k1_tmap_1(X3,X1,X0,X4,X2,sK5),X0) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | ~m1_subset_1(X0,k1_zfmisc_1(X3)) | v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X3)) ) | ~spl9_6),
% 1.50/0.62    inference(resolution,[],[f162,f116])).
% 1.50/0.62  fof(f162,plain,(
% 1.50/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.50/0.62    inference(subsumption_resolution,[],[f160,f86])).
% 1.50/0.62  fof(f160,plain,(
% 1.50/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.50/0.62    inference(subsumption_resolution,[],[f158,f87])).
% 2.05/0.63  % (30205)Termination reason: Refutation not found, incomplete strategy
% 2.05/0.63  
% 2.05/0.63  % (30205)Memory used [KB]: 11385
% 2.05/0.63  % (30205)Time elapsed: 0.199 s
% 2.05/0.63  % (30205)------------------------------
% 2.05/0.63  % (30205)------------------------------
% 2.05/0.63  fof(f158,plain,(
% 2.05/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.05/0.63    inference(subsumption_resolution,[],[f95,f88])).
% 2.05/0.63  fof(f95,plain,(
% 2.05/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.05/0.63    inference(equality_resolution,[],[f67])).
% 2.05/0.63  fof(f67,plain,(
% 2.05/0.63    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f43])).
% 2.05/0.63  fof(f366,plain,(
% 2.05/0.63    ~spl9_17 | ~spl9_11 | spl9_27),
% 2.05/0.63    inference(avatar_split_clause,[],[f364,f357,f135,f169])).
% 2.05/0.63  fof(f169,plain,(
% 2.05/0.63    spl9_17 <=> r1_xboole_0(sK2,sK3)),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 2.05/0.63  fof(f357,plain,(
% 2.05/0.63    spl9_27 <=> r1_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK4))),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).
% 2.05/0.63  fof(f364,plain,(
% 2.05/0.63    ~r1_xboole_0(sK2,sK3) | (~spl9_11 | spl9_27)),
% 2.05/0.63    inference(resolution,[],[f358,f206])).
% 2.05/0.63  fof(f206,plain,(
% 2.05/0.63    ( ! [X6,X5] : (r1_xboole_0(k9_subset_1(sK0,X5,sK3),X6) | ~r1_xboole_0(X5,sK3)) ) | ~spl9_11),
% 2.05/0.63    inference(superposition,[],[f192,f199])).
% 2.05/0.63  fof(f199,plain,(
% 2.05/0.63    ( ! [X0] : (k9_subset_1(sK0,X0,sK3) = k4_xboole_0(X0,k4_xboole_0(X0,sK3))) ) | ~spl9_11),
% 2.05/0.63    inference(resolution,[],[f91,f136])).
% 2.05/0.63  fof(f91,plain,(
% 2.05/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 2.05/0.63    inference(definition_unfolding,[],[f83,f74])).
% 2.05/0.63  fof(f74,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.05/0.63    inference(cnf_transformation,[],[f5])).
% 2.05/0.63  fof(f5,axiom,(
% 2.05/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.05/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.05/0.63  fof(f83,plain,(
% 2.05/0.63    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.05/0.63    inference(cnf_transformation,[],[f29])).
% 2.05/0.63  fof(f29,plain,(
% 2.05/0.63    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.05/0.63    inference(ennf_transformation,[],[f6])).
% 2.05/0.63  fof(f6,axiom,(
% 2.05/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 2.05/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 2.05/0.63  fof(f192,plain,(
% 2.05/0.63    ( ! [X4,X2,X3] : (r1_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X3)),X4) | ~r1_xboole_0(X2,X3)) )),
% 2.05/0.63    inference(resolution,[],[f89,f77])).
% 2.05/0.63  fof(f77,plain,(
% 2.05/0.63    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f51])).
% 2.05/0.63  fof(f51,plain,(
% 2.05/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.05/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f25,f50])).
% 2.05/0.63  fof(f50,plain,(
% 2.05/0.63    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK8(X0,X1),X1) & r2_hidden(sK8(X0,X1),X0)))),
% 2.05/0.63    introduced(choice_axiom,[])).
% 2.05/0.63  fof(f25,plain,(
% 2.05/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.05/0.63    inference(ennf_transformation,[],[f17])).
% 2.05/0.63  fof(f17,plain,(
% 2.05/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.05/0.63    inference(rectify,[],[f3])).
% 2.05/0.63  fof(f3,axiom,(
% 2.05/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.05/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 2.05/0.63  fof(f89,plain,(
% 2.05/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 2.05/0.63    inference(definition_unfolding,[],[f76,f74])).
% 2.05/0.63  fof(f76,plain,(
% 2.05/0.63    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 2.05/0.63    inference(cnf_transformation,[],[f49])).
% 2.05/0.63  fof(f49,plain,(
% 2.05/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.05/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f24,f48])).
% 2.05/0.63  fof(f48,plain,(
% 2.05/0.63    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK7(X0,X1),k3_xboole_0(X0,X1)))),
% 2.05/0.63    introduced(choice_axiom,[])).
% 2.05/0.63  fof(f24,plain,(
% 2.05/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.05/0.63    inference(ennf_transformation,[],[f16])).
% 2.05/0.63  fof(f16,plain,(
% 2.05/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.05/0.63    inference(rectify,[],[f4])).
% 2.05/0.63  fof(f4,axiom,(
% 2.05/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.05/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.05/0.63  fof(f358,plain,(
% 2.05/0.63    ~r1_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK4)) | spl9_27),
% 2.05/0.63    inference(avatar_component_clause,[],[f357])).
% 2.05/0.63  fof(f362,plain,(
% 2.05/0.63    ~spl9_7 | spl9_26),
% 2.05/0.63    inference(avatar_contradiction_clause,[],[f361])).
% 2.05/0.63  fof(f361,plain,(
% 2.05/0.63    $false | (~spl9_7 | spl9_26)),
% 2.05/0.63    inference(subsumption_resolution,[],[f120,f360])).
% 2.05/0.63  fof(f360,plain,(
% 2.05/0.63    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl9_26),
% 2.05/0.63    inference(resolution,[],[f355,f84])).
% 2.05/0.63  fof(f84,plain,(
% 2.05/0.63    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.05/0.63    inference(cnf_transformation,[],[f30])).
% 2.05/0.63  fof(f30,plain,(
% 2.05/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.05/0.63    inference(ennf_transformation,[],[f10])).
% 2.05/0.63  fof(f10,axiom,(
% 2.05/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.05/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.05/0.63  fof(f355,plain,(
% 2.05/0.63    ~v1_relat_1(sK4) | spl9_26),
% 2.05/0.63    inference(avatar_component_clause,[],[f354])).
% 2.05/0.63  fof(f354,plain,(
% 2.05/0.63    spl9_26 <=> v1_relat_1(sK4)),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).
% 2.05/0.63  fof(f120,plain,(
% 2.05/0.63    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl9_7),
% 2.05/0.63    inference(avatar_component_clause,[],[f119])).
% 2.05/0.63  fof(f359,plain,(
% 2.05/0.63    ~spl9_26 | ~spl9_27 | spl9_24),
% 2.05/0.63    inference(avatar_split_clause,[],[f352,f336,f357,f354])).
% 2.05/0.63  fof(f336,plain,(
% 2.05/0.63    spl9_24 <=> k1_xboole_0 = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).
% 2.05/0.63  fof(f352,plain,(
% 2.05/0.63    ~r1_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK4)) | ~v1_relat_1(sK4) | spl9_24),
% 2.05/0.63    inference(trivial_inequality_removal,[],[f351])).
% 2.05/0.63  fof(f351,plain,(
% 2.05/0.63    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK4)) | ~v1_relat_1(sK4) | spl9_24),
% 2.05/0.63    inference(superposition,[],[f337,f70])).
% 2.05/0.63  fof(f70,plain,(
% 2.05/0.63    ( ! [X0,X1] : (k7_relat_1(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f22])).
% 2.05/0.63  fof(f22,plain,(
% 2.05/0.63    ! [X0] : (! [X1] : (k7_relat_1(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.05/0.63    inference(ennf_transformation,[],[f8])).
% 2.05/0.63  fof(f8,axiom,(
% 2.05/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k7_relat_1(X0,X1) = k1_xboole_0))),
% 2.05/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).
% 2.05/0.63  fof(f337,plain,(
% 2.05/0.63    k1_xboole_0 != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | spl9_24),
% 2.05/0.63    inference(avatar_component_clause,[],[f336])).
% 2.05/0.63  fof(f346,plain,(
% 2.05/0.63    ~spl9_17 | ~spl9_11 | spl9_23),
% 2.05/0.63    inference(avatar_split_clause,[],[f343,f333,f135,f169])).
% 2.05/0.63  fof(f333,plain,(
% 2.05/0.63    spl9_23 <=> r1_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK5))),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 2.05/0.63  fof(f343,plain,(
% 2.05/0.63    ~r1_xboole_0(sK2,sK3) | (~spl9_11 | spl9_23)),
% 2.05/0.63    inference(resolution,[],[f334,f206])).
% 2.05/0.63  fof(f334,plain,(
% 2.05/0.63    ~r1_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK5)) | spl9_23),
% 2.05/0.63    inference(avatar_component_clause,[],[f333])).
% 2.05/0.63  fof(f341,plain,(
% 2.05/0.63    ~spl9_4 | spl9_22),
% 2.05/0.63    inference(avatar_contradiction_clause,[],[f340])).
% 2.05/0.63  fof(f340,plain,(
% 2.05/0.63    $false | (~spl9_4 | spl9_22)),
% 2.05/0.63    inference(subsumption_resolution,[],[f108,f339])).
% 2.05/0.63  fof(f339,plain,(
% 2.05/0.63    ( ! [X0,X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl9_22),
% 2.05/0.63    inference(resolution,[],[f331,f84])).
% 2.05/0.63  fof(f331,plain,(
% 2.05/0.63    ~v1_relat_1(sK5) | spl9_22),
% 2.05/0.63    inference(avatar_component_clause,[],[f330])).
% 2.05/0.63  fof(f330,plain,(
% 2.05/0.63    spl9_22 <=> v1_relat_1(sK5)),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 2.05/0.63  fof(f338,plain,(
% 2.05/0.63    ~spl9_22 | ~spl9_23 | ~spl9_24 | spl9_21),
% 2.05/0.63    inference(avatar_split_clause,[],[f328,f325,f336,f333,f330])).
% 2.05/0.63  fof(f325,plain,(
% 2.05/0.63    spl9_21 <=> k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 2.05/0.63  fof(f328,plain,(
% 2.05/0.63    k1_xboole_0 != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | ~r1_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK5)) | ~v1_relat_1(sK5) | spl9_21),
% 2.05/0.63    inference(superposition,[],[f326,f70])).
% 2.05/0.63  fof(f326,plain,(
% 2.05/0.63    k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | spl9_21),
% 2.05/0.63    inference(avatar_component_clause,[],[f325])).
% 2.05/0.63  fof(f327,plain,(
% 2.05/0.63    ~spl9_9 | ~spl9_7 | ~spl9_21 | spl9_20),
% 2.05/0.63    inference(avatar_split_clause,[],[f321,f240,f325,f119,f127])).
% 2.05/0.63  fof(f240,plain,(
% 2.05/0.63    spl9_20 <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 2.05/0.63  fof(f321,plain,(
% 2.05/0.63    k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK4) | spl9_20),
% 2.05/0.63    inference(superposition,[],[f241,f85])).
% 2.05/0.63  fof(f85,plain,(
% 2.05/0.63    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f32])).
% 2.05/0.63  fof(f32,plain,(
% 2.05/0.63    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.05/0.63    inference(flattening,[],[f31])).
% 2.05/0.63  fof(f31,plain,(
% 2.05/0.63    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.05/0.63    inference(ennf_transformation,[],[f11])).
% 2.05/0.63  fof(f11,axiom,(
% 2.05/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 2.05/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 2.05/0.63  fof(f241,plain,(
% 2.05/0.63    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | spl9_20),
% 2.05/0.63    inference(avatar_component_clause,[],[f240])).
% 2.05/0.63  fof(f242,plain,(
% 2.05/0.63    ~spl9_6 | ~spl9_4 | ~spl9_20 | spl9_1),
% 2.05/0.63    inference(avatar_split_clause,[],[f236,f97,f240,f107,f115])).
% 2.05/0.63  fof(f97,plain,(
% 2.05/0.63    spl9_1 <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 2.05/0.63  fof(f236,plain,(
% 2.05/0.63    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_1(sK5) | spl9_1),
% 2.05/0.63    inference(superposition,[],[f98,f85])).
% 2.05/0.63  fof(f98,plain,(
% 2.05/0.63    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | spl9_1),
% 2.05/0.63    inference(avatar_component_clause,[],[f97])).
% 2.05/0.63  fof(f171,plain,(
% 2.05/0.63    spl9_14 | spl9_12 | spl9_17 | ~spl9_10),
% 2.05/0.63    inference(avatar_split_clause,[],[f165,f131,f169,f139,f147])).
% 2.05/0.63  fof(f131,plain,(
% 2.05/0.63    spl9_10 <=> r1_subset_1(sK2,sK3)),
% 2.05/0.63    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 2.05/0.63  fof(f165,plain,(
% 2.05/0.63    r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2) | ~spl9_10),
% 2.05/0.63    inference(resolution,[],[f81,f132])).
% 2.05/0.63  fof(f132,plain,(
% 2.05/0.63    r1_subset_1(sK2,sK3) | ~spl9_10),
% 2.05/0.63    inference(avatar_component_clause,[],[f131])).
% 2.05/0.63  fof(f81,plain,(
% 2.05/0.63    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | r1_xboole_0(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.05/0.63    inference(cnf_transformation,[],[f52])).
% 2.05/0.63  fof(f52,plain,(
% 2.05/0.63    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.05/0.63    inference(nnf_transformation,[],[f28])).
% 2.05/0.63  fof(f28,plain,(
% 2.05/0.63    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.05/0.63    inference(flattening,[],[f27])).
% 2.05/0.63  fof(f27,plain,(
% 2.05/0.63    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.05/0.63    inference(ennf_transformation,[],[f9])).
% 2.05/0.63  fof(f9,axiom,(
% 2.05/0.63    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 2.05/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 2.05/0.63  fof(f157,plain,(
% 2.05/0.63    ~spl9_16),
% 2.05/0.63    inference(avatar_split_clause,[],[f53,f155])).
% 2.05/0.63  fof(f53,plain,(
% 2.05/0.63    ~v1_xboole_0(sK0)),
% 2.05/0.63    inference(cnf_transformation,[],[f41])).
% 2.05/0.63  fof(f41,plain,(
% 2.05/0.63    ((((((sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 2.05/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f19,f40,f39,f38,f37,f36,f35])).
% 2.05/0.63  fof(f35,plain,(
% 2.05/0.63    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 2.05/0.63    introduced(choice_axiom,[])).
% 2.05/0.63  fof(f36,plain,(
% 2.05/0.63    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))),
% 2.05/0.63    introduced(choice_axiom,[])).
% 2.05/0.63  fof(f37,plain,(
% 2.05/0.63    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2))),
% 2.05/0.63    introduced(choice_axiom,[])).
% 2.05/0.63  fof(f38,plain,(
% 2.05/0.63    ? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3))),
% 2.05/0.63    introduced(choice_axiom,[])).
% 2.05/0.63  fof(f39,plain,(
% 2.05/0.63    ? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK3) != X5 | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK2) | k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4))),
% 2.05/0.63    introduced(choice_axiom,[])).
% 2.05/0.63  fof(f40,plain,(
% 2.05/0.63    ? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK3) != X5 | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK2) | k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) => ((sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5))),
% 2.05/0.63    introduced(choice_axiom,[])).
% 2.05/0.63  fof(f19,plain,(
% 2.05/0.63    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.05/0.63    inference(flattening,[],[f18])).
% 2.05/0.63  fof(f18,plain,(
% 2.05/0.63    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.05/0.63    inference(ennf_transformation,[],[f15])).
% 2.05/0.63  fof(f15,negated_conjecture,(
% 2.05/0.63    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 2.05/0.63    inference(negated_conjecture,[],[f14])).
% 2.05/0.63  fof(f14,conjecture,(
% 2.05/0.63    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 2.05/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tmap_1)).
% 2.05/0.63  fof(f153,plain,(
% 2.05/0.63    ~spl9_15),
% 2.05/0.63    inference(avatar_split_clause,[],[f54,f151])).
% 2.05/0.63  fof(f54,plain,(
% 2.05/0.63    ~v1_xboole_0(sK1)),
% 2.05/0.63    inference(cnf_transformation,[],[f41])).
% 2.05/0.63  fof(f149,plain,(
% 2.05/0.63    ~spl9_14),
% 2.05/0.63    inference(avatar_split_clause,[],[f55,f147])).
% 2.05/0.63  fof(f55,plain,(
% 2.05/0.63    ~v1_xboole_0(sK2)),
% 2.05/0.63    inference(cnf_transformation,[],[f41])).
% 2.05/0.63  fof(f145,plain,(
% 2.05/0.63    spl9_13),
% 2.05/0.63    inference(avatar_split_clause,[],[f56,f143])).
% 2.05/0.63  fof(f56,plain,(
% 2.05/0.63    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.05/0.63    inference(cnf_transformation,[],[f41])).
% 2.05/0.63  fof(f141,plain,(
% 2.05/0.63    ~spl9_12),
% 2.05/0.63    inference(avatar_split_clause,[],[f57,f139])).
% 2.05/0.63  fof(f57,plain,(
% 2.05/0.63    ~v1_xboole_0(sK3)),
% 2.05/0.63    inference(cnf_transformation,[],[f41])).
% 2.05/0.63  fof(f137,plain,(
% 2.05/0.63    spl9_11),
% 2.05/0.63    inference(avatar_split_clause,[],[f58,f135])).
% 2.05/0.63  fof(f58,plain,(
% 2.05/0.63    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 2.05/0.63    inference(cnf_transformation,[],[f41])).
% 2.05/0.63  fof(f133,plain,(
% 2.05/0.63    spl9_10),
% 2.05/0.63    inference(avatar_split_clause,[],[f59,f131])).
% 2.05/0.63  fof(f59,plain,(
% 2.05/0.63    r1_subset_1(sK2,sK3)),
% 2.05/0.63    inference(cnf_transformation,[],[f41])).
% 2.05/0.63  fof(f129,plain,(
% 2.05/0.63    spl9_9),
% 2.05/0.63    inference(avatar_split_clause,[],[f60,f127])).
% 2.05/0.63  fof(f60,plain,(
% 2.05/0.63    v1_funct_1(sK4)),
% 2.05/0.63    inference(cnf_transformation,[],[f41])).
% 2.05/0.63  fof(f125,plain,(
% 2.05/0.63    spl9_8),
% 2.05/0.63    inference(avatar_split_clause,[],[f61,f123])).
% 2.05/0.63  fof(f61,plain,(
% 2.05/0.63    v1_funct_2(sK4,sK2,sK1)),
% 2.05/0.63    inference(cnf_transformation,[],[f41])).
% 2.05/0.63  fof(f121,plain,(
% 2.05/0.63    spl9_7),
% 2.05/0.63    inference(avatar_split_clause,[],[f62,f119])).
% 2.05/0.63  fof(f62,plain,(
% 2.05/0.63    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.05/0.63    inference(cnf_transformation,[],[f41])).
% 2.05/0.63  fof(f117,plain,(
% 2.05/0.63    spl9_6),
% 2.05/0.63    inference(avatar_split_clause,[],[f63,f115])).
% 2.05/0.63  fof(f63,plain,(
% 2.05/0.63    v1_funct_1(sK5)),
% 2.05/0.63    inference(cnf_transformation,[],[f41])).
% 2.05/0.63  fof(f113,plain,(
% 2.05/0.63    spl9_5),
% 2.05/0.63    inference(avatar_split_clause,[],[f64,f111])).
% 2.05/0.63  fof(f64,plain,(
% 2.05/0.63    v1_funct_2(sK5,sK3,sK1)),
% 2.05/0.63    inference(cnf_transformation,[],[f41])).
% 2.05/0.63  fof(f109,plain,(
% 2.05/0.63    spl9_4),
% 2.05/0.63    inference(avatar_split_clause,[],[f65,f107])).
% 2.05/0.63  fof(f65,plain,(
% 2.05/0.63    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 2.05/0.63    inference(cnf_transformation,[],[f41])).
% 2.05/0.63  fof(f105,plain,(
% 2.05/0.63    ~spl9_1 | ~spl9_2 | ~spl9_3),
% 2.05/0.63    inference(avatar_split_clause,[],[f66,f103,f100,f97])).
% 2.05/0.63  fof(f66,plain,(
% 2.05/0.63    sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 2.05/0.63    inference(cnf_transformation,[],[f41])).
% 2.05/0.63  % SZS output end Proof for theBenchmark
% 2.05/0.63  % (30214)------------------------------
% 2.05/0.63  % (30214)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.05/0.63  % (30214)Termination reason: Refutation
% 2.05/0.63  
% 2.05/0.63  % (30214)Memory used [KB]: 11641
% 2.05/0.63  % (30214)Time elapsed: 0.208 s
% 2.05/0.63  % (30214)------------------------------
% 2.05/0.63  % (30214)------------------------------
% 2.05/0.63  % (30194)Success in time 0.267 s
%------------------------------------------------------------------------------
