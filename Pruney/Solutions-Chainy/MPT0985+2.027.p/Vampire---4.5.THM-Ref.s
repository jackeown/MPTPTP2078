%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  193 ( 454 expanded)
%              Number of leaves         :   34 ( 178 expanded)
%              Depth                    :   14
%              Number of atoms          :  657 (1480 expanded)
%              Number of equality atoms :  117 ( 332 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f733,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f93,f102,f109,f114,f137,f161,f164,f180,f185,f201,f216,f221,f249,f260,f265,f281,f313,f333,f346,f355,f362,f485,f527,f580,f596,f720])).

fof(f720,plain,
    ( ~ spl6_4
    | spl6_8
    | ~ spl6_9
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(avatar_contradiction_clause,[],[f719])).

fof(f719,plain,
    ( $false
    | ~ spl6_4
    | spl6_8
    | ~ spl6_9
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f132,f714])).

fof(f714,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl6_4
    | ~ spl6_9
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(backward_demodulation,[],[f711,f160])).

fof(f160,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl6_13
  <=> sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f711,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),sK0)
    | ~ spl6_4
    | ~ spl6_9
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(forward_demodulation,[],[f327,f209])).

fof(f209,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl6_4
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f207,f108])).

fof(f108,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl6_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f207,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_16 ),
    inference(superposition,[],[f196,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f196,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl6_16
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f327,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))
    | ~ spl6_9
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f326,f179])).

fof(f179,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl6_14
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f326,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl6_9
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f325,f135])).

fof(f135,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl6_9
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f325,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl6_15 ),
    inference(superposition,[],[f41,f184])).

fof(f184,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl6_15
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f41,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f132,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl6_8
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f596,plain,
    ( ~ spl6_55
    | ~ spl6_9
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_17
    | spl6_22
    | ~ spl6_30
    | spl6_31 ),
    inference(avatar_split_clause,[],[f584,f343,f339,f278,f198,f182,f177,f158,f134,f567])).

fof(f567,plain,
    ( spl6_55
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).

fof(f198,plain,
    ( spl6_17
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f278,plain,
    ( spl6_22
  <=> v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f339,plain,
    ( spl6_30
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f343,plain,
    ( spl6_31
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f584,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0))
    | ~ spl6_9
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_17
    | spl6_22
    | ~ spl6_30
    | spl6_31 ),
    inference(subsumption_resolution,[],[f380,f344])).

fof(f344,plain,
    ( k1_xboole_0 != sK0
    | spl6_31 ),
    inference(avatar_component_clause,[],[f343])).

fof(f380,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0))
    | k1_xboole_0 = sK0
    | ~ spl6_9
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_17
    | spl6_22
    | ~ spl6_30 ),
    inference(backward_demodulation,[],[f289,f341])).

fof(f341,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f339])).

fof(f289,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2))
    | ~ spl6_9
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_17
    | spl6_22 ),
    inference(subsumption_resolution,[],[f288,f252])).

fof(f252,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_9
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f245,f135])).

fof(f245,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_17 ),
    inference(forward_demodulation,[],[f234,f78])).

fof(f78,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f234,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_17 ),
    inference(backward_demodulation,[],[f189,f200])).

fof(f200,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f198])).

fof(f189,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(forward_demodulation,[],[f188,f160])).

fof(f188,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(forward_demodulation,[],[f187,f184])).

fof(f187,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl6_14 ),
    inference(resolution,[],[f179,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f288,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2))
    | spl6_22 ),
    inference(forward_demodulation,[],[f287,f78])).

fof(f287,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl6_22 ),
    inference(resolution,[],[f280,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f280,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl6_22 ),
    inference(avatar_component_clause,[],[f278])).

fof(f580,plain,
    ( ~ spl6_45
    | ~ spl6_51
    | spl6_55 ),
    inference(avatar_contradiction_clause,[],[f579])).

fof(f579,plain,
    ( $false
    | ~ spl6_45
    | ~ spl6_51
    | spl6_55 ),
    inference(subsumption_resolution,[],[f578,f526])).

fof(f526,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_51 ),
    inference(avatar_component_clause,[],[f524])).

fof(f524,plain,
    ( spl6_51
  <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f578,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_45
    | spl6_55 ),
    inference(forward_demodulation,[],[f577,f78])).

fof(f577,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl6_45
    | spl6_55 ),
    inference(subsumption_resolution,[],[f576,f484])).

fof(f484,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f482])).

fof(f482,plain,
    ( spl6_45
  <=> k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f576,plain,
    ( k1_xboole_0 != k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl6_55 ),
    inference(superposition,[],[f569,f67])).

fof(f569,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0))
    | spl6_55 ),
    inference(avatar_component_clause,[],[f567])).

fof(f527,plain,
    ( spl6_51
    | ~ spl6_9
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_17
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f374,f339,f198,f182,f177,f158,f134,f524])).

fof(f374,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_9
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_17
    | ~ spl6_30 ),
    inference(backward_demodulation,[],[f252,f341])).

fof(f485,plain,
    ( spl6_45
    | ~ spl6_27
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f384,f339,f310,f482])).

fof(f310,plain,
    ( spl6_27
  <=> k1_xboole_0 = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f384,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl6_27
    | ~ spl6_30 ),
    inference(backward_demodulation,[],[f312,f341])).

fof(f312,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f310])).

fof(f362,plain,
    ( ~ spl6_20
    | spl6_29
    | ~ spl6_31
    | ~ spl6_32 ),
    inference(avatar_contradiction_clause,[],[f361])).

fof(f361,plain,
    ( $false
    | ~ spl6_20
    | spl6_29
    | ~ spl6_31
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f360,f264])).

fof(f264,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f262])).

fof(f262,plain,
    ( spl6_20
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f360,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | spl6_29
    | ~ spl6_31
    | ~ spl6_32 ),
    inference(forward_demodulation,[],[f359,f77])).

fof(f77,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f359,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl6_29
    | ~ spl6_31
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f356,f350])).

fof(f350,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | spl6_29
    | ~ spl6_31 ),
    inference(backward_demodulation,[],[f332,f345])).

fof(f345,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f343])).

fof(f332,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,sK2)
    | spl6_29 ),
    inference(avatar_component_clause,[],[f330])).

fof(f330,plain,
    ( spl6_29
  <=> sK0 = k1_relset_1(sK0,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f356,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_32 ),
    inference(resolution,[],[f354,f79])).

fof(f79,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f354,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f352])).

fof(f352,plain,
    ( spl6_32
  <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f355,plain,
    ( spl6_32
    | ~ spl6_19
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f347,f343,f257,f352])).

fof(f257,plain,
    ( spl6_19
  <=> v1_funct_2(sK2,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f347,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl6_19
    | ~ spl6_31 ),
    inference(backward_demodulation,[],[f259,f345])).

fof(f259,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f257])).

fof(f346,plain,
    ( spl6_30
    | spl6_31
    | ~ spl6_19
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f269,f262,f257,f343,f339])).

fof(f269,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl6_19
    | ~ spl6_20 ),
    inference(subsumption_resolution,[],[f268,f264])).

fof(f268,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ spl6_19 ),
    inference(forward_demodulation,[],[f266,f77])).

fof(f266,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_19 ),
    inference(resolution,[],[f259,f81])).

fof(f81,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f333,plain,
    ( ~ spl6_29
    | spl6_16
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f247,f198,f194,f330])).

fof(f247,plain,
    ( sK0 != k1_relset_1(sK0,k1_xboole_0,sK2)
    | spl6_16
    | ~ spl6_17 ),
    inference(forward_demodulation,[],[f195,f200])).

fof(f195,plain,
    ( sK0 != k1_relset_1(sK0,sK1,sK2)
    | spl6_16 ),
    inference(avatar_component_clause,[],[f194])).

fof(f313,plain,
    ( spl6_27
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f231,f198,f158,f310])).

fof(f231,plain,
    ( k1_xboole_0 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl6_13
    | ~ spl6_17 ),
    inference(backward_demodulation,[],[f160,f200])).

fof(f281,plain,
    ( ~ spl6_22
    | spl6_8
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f253,f198,f130,f278])).

fof(f253,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl6_8
    | ~ spl6_17 ),
    inference(forward_demodulation,[],[f132,f200])).

fof(f265,plain,
    ( spl6_20
    | ~ spl6_4
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f236,f198,f106,f262])).

fof(f236,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_4
    | ~ spl6_17 ),
    inference(forward_demodulation,[],[f223,f77])).

fof(f223,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_4
    | ~ spl6_17 ),
    inference(backward_demodulation,[],[f108,f200])).

fof(f260,plain,
    ( spl6_19
    | ~ spl6_3
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f222,f198,f99,f257])).

fof(f99,plain,
    ( spl6_3
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f222,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl6_3
    | ~ spl6_17 ),
    inference(backward_demodulation,[],[f101,f200])).

fof(f101,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f99])).

fof(f249,plain,
    ( spl6_7
    | ~ spl6_9
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_17 ),
    inference(avatar_contradiction_clause,[],[f248])).

fof(f248,plain,
    ( $false
    | spl6_7
    | ~ spl6_9
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f135,f246])).

fof(f246,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl6_7
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_17 ),
    inference(subsumption_resolution,[],[f245,f237])).

fof(f237,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | spl6_7
    | ~ spl6_17 ),
    inference(forward_demodulation,[],[f226,f78])).

fof(f226,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl6_7
    | ~ spl6_17 ),
    inference(backward_demodulation,[],[f128,f200])).

fof(f128,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl6_7
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f221,plain,
    ( ~ spl6_1
    | spl6_9
    | ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f220])).

fof(f220,plain,
    ( $false
    | ~ spl6_1
    | spl6_9
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f219,f155])).

fof(f155,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl6_12
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f219,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl6_1
    | spl6_9 ),
    inference(subsumption_resolution,[],[f217,f87])).

fof(f87,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl6_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f217,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl6_9 ),
    inference(resolution,[],[f136,f44])).

fof(f44,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f136,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl6_9 ),
    inference(avatar_component_clause,[],[f134])).

fof(f216,plain,
    ( ~ spl6_9
    | ~ spl6_4
    | spl6_7
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f215,f194,f182,f177,f158,f126,f106,f134])).

fof(f215,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl6_4
    | spl6_7
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f211,f128])).

fof(f211,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl6_4
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(backward_demodulation,[],[f189,f209])).

fof(f201,plain,
    ( spl6_16
    | spl6_17
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f104,f99,f198,f194])).

fof(f104,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f103,f36])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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

fof(f103,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_3 ),
    inference(resolution,[],[f101,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f185,plain,
    ( spl6_15
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f166,f154,f90,f85,f182])).

fof(f90,plain,
    ( spl6_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f166,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f97,f155])).

fof(f97,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f95,f87])).

fof(f95,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl6_2 ),
    inference(resolution,[],[f92,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f92,plain,
    ( v2_funct_1(sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f180,plain,
    ( spl6_14
    | ~ spl6_1
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f170,f154,f85,f177])).

fof(f170,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl6_1
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f168,f87])).

fof(f168,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ spl6_12 ),
    inference(resolution,[],[f155,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f164,plain,
    ( ~ spl6_4
    | spl6_12 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | ~ spl6_4
    | spl6_12 ),
    inference(subsumption_resolution,[],[f108,f162])).

fof(f162,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_12 ),
    inference(resolution,[],[f156,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f156,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_12 ),
    inference(avatar_component_clause,[],[f154])).

fof(f161,plain,
    ( ~ spl6_12
    | spl6_13
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f119,f111,f106,f90,f85,f158,f154])).

fof(f111,plain,
    ( spl6_5
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f119,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(backward_demodulation,[],[f96,f118])).

fof(f118,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f116,f108])).

fof(f116,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_5 ),
    inference(superposition,[],[f113,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f113,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f111])).

fof(f96,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f94,f87])).

fof(f94,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl6_2 ),
    inference(resolution,[],[f92,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f137,plain,
    ( ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f33,f134,f130,f126])).

fof(f33,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f114,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f38,f111])).

fof(f38,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f109,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f36,f106])).

fof(f102,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f35,f99])).

fof(f35,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f93,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f37,f90])).

fof(f37,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f88,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f34,f85])).

fof(f34,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:20:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (2695)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.50  % (2671)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.50  % (2679)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.50  % (2679)Refutation not found, incomplete strategy% (2679)------------------------------
% 0.22/0.50  % (2679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (2679)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (2679)Memory used [KB]: 10618
% 0.22/0.50  % (2679)Time elapsed: 0.089 s
% 0.22/0.50  % (2679)------------------------------
% 0.22/0.50  % (2679)------------------------------
% 0.22/0.50  % (2687)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.51  % (2689)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.51  % (2670)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (2675)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (2691)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (2682)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.52  % (2671)Refutation not found, incomplete strategy% (2671)------------------------------
% 0.22/0.52  % (2671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (2671)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (2671)Memory used [KB]: 10874
% 0.22/0.52  % (2671)Time elapsed: 0.107 s
% 0.22/0.52  % (2671)------------------------------
% 0.22/0.52  % (2671)------------------------------
% 0.22/0.53  % (2672)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (2674)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (2683)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (2673)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (2669)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (2691)Refutation not found, incomplete strategy% (2691)------------------------------
% 0.22/0.53  % (2691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (2691)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (2691)Memory used [KB]: 10874
% 0.22/0.53  % (2691)Time elapsed: 0.091 s
% 0.22/0.53  % (2691)------------------------------
% 0.22/0.53  % (2691)------------------------------
% 0.22/0.54  % (2690)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (2681)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (2678)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.54  % (2680)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (2677)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (2698)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (2693)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (2696)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (2684)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (2694)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (2688)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (2692)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (2689)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f733,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f88,f93,f102,f109,f114,f137,f161,f164,f180,f185,f201,f216,f221,f249,f260,f265,f281,f313,f333,f346,f355,f362,f485,f527,f580,f596,f720])).
% 0.22/0.55  fof(f720,plain,(
% 0.22/0.55    ~spl6_4 | spl6_8 | ~spl6_9 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_16),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f719])).
% 0.22/0.55  fof(f719,plain,(
% 0.22/0.55    $false | (~spl6_4 | spl6_8 | ~spl6_9 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_16)),
% 0.22/0.55    inference(subsumption_resolution,[],[f132,f714])).
% 0.22/0.55  fof(f714,plain,(
% 0.22/0.55    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | (~spl6_4 | ~spl6_9 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_16)),
% 0.22/0.55    inference(backward_demodulation,[],[f711,f160])).
% 0.22/0.55  fof(f160,plain,(
% 0.22/0.55    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~spl6_13),
% 0.22/0.55    inference(avatar_component_clause,[],[f158])).
% 0.22/0.55  fof(f158,plain,(
% 0.22/0.55    spl6_13 <=> sK1 = k1_relat_1(k2_funct_1(sK2))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.22/0.55  fof(f711,plain,(
% 0.22/0.55    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),sK0) | (~spl6_4 | ~spl6_9 | ~spl6_14 | ~spl6_15 | ~spl6_16)),
% 0.22/0.55    inference(forward_demodulation,[],[f327,f209])).
% 0.22/0.55  fof(f209,plain,(
% 0.22/0.55    sK0 = k1_relat_1(sK2) | (~spl6_4 | ~spl6_16)),
% 0.22/0.55    inference(subsumption_resolution,[],[f207,f108])).
% 0.22/0.55  fof(f108,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_4),
% 0.22/0.55    inference(avatar_component_clause,[],[f106])).
% 0.22/0.55  fof(f106,plain,(
% 0.22/0.55    spl6_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.55  fof(f207,plain,(
% 0.22/0.55    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_16),
% 0.22/0.55    inference(superposition,[],[f196,f67])).
% 0.22/0.55  fof(f67,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f29])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.55  fof(f196,plain,(
% 0.22/0.55    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl6_16),
% 0.22/0.55    inference(avatar_component_clause,[],[f194])).
% 0.22/0.55  fof(f194,plain,(
% 0.22/0.55    spl6_16 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.22/0.55  fof(f327,plain,(
% 0.22/0.55    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) | (~spl6_9 | ~spl6_14 | ~spl6_15)),
% 0.22/0.55    inference(subsumption_resolution,[],[f326,f179])).
% 0.22/0.55  fof(f179,plain,(
% 0.22/0.55    v1_relat_1(k2_funct_1(sK2)) | ~spl6_14),
% 0.22/0.55    inference(avatar_component_clause,[],[f177])).
% 0.22/0.55  fof(f177,plain,(
% 0.22/0.55    spl6_14 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.22/0.55  fof(f326,plain,(
% 0.22/0.55    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl6_9 | ~spl6_15)),
% 0.22/0.55    inference(subsumption_resolution,[],[f325,f135])).
% 0.22/0.55  fof(f135,plain,(
% 0.22/0.55    v1_funct_1(k2_funct_1(sK2)) | ~spl6_9),
% 0.22/0.55    inference(avatar_component_clause,[],[f134])).
% 0.22/0.55  fof(f134,plain,(
% 0.22/0.55    spl6_9 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.55  fof(f325,plain,(
% 0.22/0.55    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl6_15),
% 0.22/0.55    inference(superposition,[],[f41,f184])).
% 0.22/0.55  fof(f184,plain,(
% 0.22/0.55    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl6_15),
% 0.22/0.55    inference(avatar_component_clause,[],[f182])).
% 0.22/0.55  fof(f182,plain,(
% 0.22/0.55    spl6_15 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f22])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(flattening,[],[f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f15])).
% 0.22/0.55  fof(f15,axiom,(
% 0.22/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.22/0.55  fof(f132,plain,(
% 0.22/0.55    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl6_8),
% 0.22/0.55    inference(avatar_component_clause,[],[f130])).
% 0.22/0.55  fof(f130,plain,(
% 0.22/0.55    spl6_8 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.55  fof(f596,plain,(
% 0.22/0.55    ~spl6_55 | ~spl6_9 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_17 | spl6_22 | ~spl6_30 | spl6_31),
% 0.22/0.55    inference(avatar_split_clause,[],[f584,f343,f339,f278,f198,f182,f177,f158,f134,f567])).
% 0.22/0.55  fof(f567,plain,(
% 0.22/0.55    spl6_55 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).
% 0.22/0.55  fof(f198,plain,(
% 0.22/0.55    spl6_17 <=> k1_xboole_0 = sK1),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.22/0.55  fof(f278,plain,(
% 0.22/0.55    spl6_22 <=> v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.22/0.55  fof(f339,plain,(
% 0.22/0.55    spl6_30 <=> k1_xboole_0 = sK2),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.22/0.55  fof(f343,plain,(
% 0.22/0.55    spl6_31 <=> k1_xboole_0 = sK0),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.22/0.55  fof(f584,plain,(
% 0.22/0.55    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) | (~spl6_9 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_17 | spl6_22 | ~spl6_30 | spl6_31)),
% 0.22/0.55    inference(subsumption_resolution,[],[f380,f344])).
% 0.22/0.55  fof(f344,plain,(
% 0.22/0.55    k1_xboole_0 != sK0 | spl6_31),
% 0.22/0.55    inference(avatar_component_clause,[],[f343])).
% 0.22/0.55  fof(f380,plain,(
% 0.22/0.55    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) | k1_xboole_0 = sK0 | (~spl6_9 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_17 | spl6_22 | ~spl6_30)),
% 0.22/0.55    inference(backward_demodulation,[],[f289,f341])).
% 0.22/0.55  fof(f341,plain,(
% 0.22/0.55    k1_xboole_0 = sK2 | ~spl6_30),
% 0.22/0.55    inference(avatar_component_clause,[],[f339])).
% 0.22/0.55  fof(f289,plain,(
% 0.22/0.55    k1_xboole_0 = sK0 | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) | (~spl6_9 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_17 | spl6_22)),
% 0.22/0.55    inference(subsumption_resolution,[],[f288,f252])).
% 0.22/0.55  fof(f252,plain,(
% 0.22/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (~spl6_9 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_17)),
% 0.22/0.55    inference(subsumption_resolution,[],[f245,f135])).
% 0.22/0.55  fof(f245,plain,(
% 0.22/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_17)),
% 0.22/0.55    inference(forward_demodulation,[],[f234,f78])).
% 0.22/0.55  fof(f78,plain,(
% 0.22/0.55    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.55    inference(equality_resolution,[],[f58])).
% 0.22/0.55  fof(f58,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.55  fof(f234,plain,(
% 0.22/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_17)),
% 0.22/0.55    inference(backward_demodulation,[],[f189,f200])).
% 0.22/0.55  fof(f200,plain,(
% 0.22/0.55    k1_xboole_0 = sK1 | ~spl6_17),
% 0.22/0.55    inference(avatar_component_clause,[],[f198])).
% 0.22/0.55  fof(f189,plain,(
% 0.22/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl6_13 | ~spl6_14 | ~spl6_15)),
% 0.22/0.55    inference(forward_demodulation,[],[f188,f160])).
% 0.22/0.55  fof(f188,plain,(
% 0.22/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl6_14 | ~spl6_15)),
% 0.22/0.55    inference(forward_demodulation,[],[f187,f184])).
% 0.22/0.55  fof(f187,plain,(
% 0.22/0.55    ~v1_funct_1(k2_funct_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | ~spl6_14),
% 0.22/0.55    inference(resolution,[],[f179,f42])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f22])).
% 0.22/0.55  fof(f288,plain,(
% 0.22/0.55    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK0 | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) | spl6_22),
% 0.22/0.55    inference(forward_demodulation,[],[f287,f78])).
% 0.22/0.55  fof(f287,plain,(
% 0.22/0.55    k1_xboole_0 = sK0 | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl6_22),
% 0.22/0.55    inference(resolution,[],[f280,f73])).
% 0.22/0.55  fof(f73,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f32])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(flattening,[],[f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.55  fof(f280,plain,(
% 0.22/0.55    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | spl6_22),
% 0.22/0.55    inference(avatar_component_clause,[],[f278])).
% 0.22/0.55  fof(f580,plain,(
% 0.22/0.55    ~spl6_45 | ~spl6_51 | spl6_55),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f579])).
% 0.22/0.55  fof(f579,plain,(
% 0.22/0.55    $false | (~spl6_45 | ~spl6_51 | spl6_55)),
% 0.22/0.55    inference(subsumption_resolution,[],[f578,f526])).
% 0.22/0.55  fof(f526,plain,(
% 0.22/0.55    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | ~spl6_51),
% 0.22/0.55    inference(avatar_component_clause,[],[f524])).
% 0.22/0.55  fof(f524,plain,(
% 0.22/0.55    spl6_51 <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).
% 0.22/0.55  fof(f578,plain,(
% 0.22/0.55    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl6_45 | spl6_55)),
% 0.22/0.55    inference(forward_demodulation,[],[f577,f78])).
% 0.22/0.55  fof(f577,plain,(
% 0.22/0.55    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (~spl6_45 | spl6_55)),
% 0.22/0.55    inference(subsumption_resolution,[],[f576,f484])).
% 0.22/0.55  fof(f484,plain,(
% 0.22/0.55    k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) | ~spl6_45),
% 0.22/0.55    inference(avatar_component_clause,[],[f482])).
% 0.22/0.55  fof(f482,plain,(
% 0.22/0.55    spl6_45 <=> k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 0.22/0.55  fof(f576,plain,(
% 0.22/0.55    k1_xboole_0 != k1_relat_1(k2_funct_1(k1_xboole_0)) | ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl6_55),
% 0.22/0.55    inference(superposition,[],[f569,f67])).
% 0.22/0.55  fof(f569,plain,(
% 0.22/0.55    k1_xboole_0 != k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) | spl6_55),
% 0.22/0.55    inference(avatar_component_clause,[],[f567])).
% 0.22/0.55  fof(f527,plain,(
% 0.22/0.55    spl6_51 | ~spl6_9 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_17 | ~spl6_30),
% 0.22/0.55    inference(avatar_split_clause,[],[f374,f339,f198,f182,f177,f158,f134,f524])).
% 0.22/0.55  fof(f374,plain,(
% 0.22/0.55    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) | (~spl6_9 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_17 | ~spl6_30)),
% 0.22/0.55    inference(backward_demodulation,[],[f252,f341])).
% 0.22/0.55  fof(f485,plain,(
% 0.22/0.55    spl6_45 | ~spl6_27 | ~spl6_30),
% 0.22/0.55    inference(avatar_split_clause,[],[f384,f339,f310,f482])).
% 0.22/0.55  fof(f310,plain,(
% 0.22/0.55    spl6_27 <=> k1_xboole_0 = k1_relat_1(k2_funct_1(sK2))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.22/0.55  fof(f384,plain,(
% 0.22/0.55    k1_xboole_0 = k1_relat_1(k2_funct_1(k1_xboole_0)) | (~spl6_27 | ~spl6_30)),
% 0.22/0.55    inference(backward_demodulation,[],[f312,f341])).
% 0.22/0.55  fof(f312,plain,(
% 0.22/0.55    k1_xboole_0 = k1_relat_1(k2_funct_1(sK2)) | ~spl6_27),
% 0.22/0.55    inference(avatar_component_clause,[],[f310])).
% 0.22/0.55  fof(f362,plain,(
% 0.22/0.55    ~spl6_20 | spl6_29 | ~spl6_31 | ~spl6_32),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f361])).
% 0.22/0.55  fof(f361,plain,(
% 0.22/0.55    $false | (~spl6_20 | spl6_29 | ~spl6_31 | ~spl6_32)),
% 0.22/0.55    inference(subsumption_resolution,[],[f360,f264])).
% 0.22/0.55  fof(f264,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl6_20),
% 0.22/0.55    inference(avatar_component_clause,[],[f262])).
% 0.22/0.55  fof(f262,plain,(
% 0.22/0.55    spl6_20 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.22/0.55  fof(f360,plain,(
% 0.22/0.55    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (spl6_29 | ~spl6_31 | ~spl6_32)),
% 0.22/0.55    inference(forward_demodulation,[],[f359,f77])).
% 0.22/0.55  fof(f77,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.55    inference(equality_resolution,[],[f59])).
% 0.22/0.55  fof(f59,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f5])).
% 0.22/0.55  fof(f359,plain,(
% 0.22/0.55    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (spl6_29 | ~spl6_31 | ~spl6_32)),
% 0.22/0.55    inference(subsumption_resolution,[],[f356,f350])).
% 0.22/0.55  fof(f350,plain,(
% 0.22/0.55    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (spl6_29 | ~spl6_31)),
% 0.22/0.55    inference(backward_demodulation,[],[f332,f345])).
% 0.22/0.55  fof(f345,plain,(
% 0.22/0.55    k1_xboole_0 = sK0 | ~spl6_31),
% 0.22/0.55    inference(avatar_component_clause,[],[f343])).
% 0.22/0.55  fof(f332,plain,(
% 0.22/0.55    sK0 != k1_relset_1(sK0,k1_xboole_0,sK2) | spl6_29),
% 0.22/0.55    inference(avatar_component_clause,[],[f330])).
% 0.22/0.55  fof(f330,plain,(
% 0.22/0.55    spl6_29 <=> sK0 = k1_relset_1(sK0,k1_xboole_0,sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.22/0.55  fof(f356,plain,(
% 0.22/0.55    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl6_32),
% 0.22/0.55    inference(resolution,[],[f354,f79])).
% 0.22/0.55  fof(f79,plain,(
% 0.22/0.55    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.22/0.55    inference(equality_resolution,[],[f72])).
% 0.22/0.55  fof(f72,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f32])).
% 0.22/0.55  fof(f354,plain,(
% 0.22/0.55    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~spl6_32),
% 0.22/0.55    inference(avatar_component_clause,[],[f352])).
% 0.22/0.55  fof(f352,plain,(
% 0.22/0.55    spl6_32 <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.22/0.55  fof(f355,plain,(
% 0.22/0.55    spl6_32 | ~spl6_19 | ~spl6_31),
% 0.22/0.55    inference(avatar_split_clause,[],[f347,f343,f257,f352])).
% 0.22/0.55  fof(f257,plain,(
% 0.22/0.55    spl6_19 <=> v1_funct_2(sK2,sK0,k1_xboole_0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.22/0.55  fof(f347,plain,(
% 0.22/0.55    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl6_19 | ~spl6_31)),
% 0.22/0.55    inference(backward_demodulation,[],[f259,f345])).
% 0.22/0.55  fof(f259,plain,(
% 0.22/0.55    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl6_19),
% 0.22/0.55    inference(avatar_component_clause,[],[f257])).
% 0.22/0.55  fof(f346,plain,(
% 0.22/0.55    spl6_30 | spl6_31 | ~spl6_19 | ~spl6_20),
% 0.22/0.55    inference(avatar_split_clause,[],[f269,f262,f257,f343,f339])).
% 0.22/0.55  fof(f269,plain,(
% 0.22/0.55    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | (~spl6_19 | ~spl6_20)),
% 0.22/0.55    inference(subsumption_resolution,[],[f268,f264])).
% 0.22/0.55  fof(f268,plain,(
% 0.22/0.55    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~spl6_19),
% 0.22/0.55    inference(forward_demodulation,[],[f266,f77])).
% 0.22/0.55  fof(f266,plain,(
% 0.22/0.55    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl6_19),
% 0.22/0.55    inference(resolution,[],[f259,f81])).
% 0.22/0.55  fof(f81,plain,(
% 0.22/0.55    ( ! [X2,X0] : (~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 0.22/0.55    inference(equality_resolution,[],[f70])).
% 0.22/0.55  fof(f70,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f32])).
% 0.22/0.55  fof(f333,plain,(
% 0.22/0.55    ~spl6_29 | spl6_16 | ~spl6_17),
% 0.22/0.55    inference(avatar_split_clause,[],[f247,f198,f194,f330])).
% 0.22/0.55  fof(f247,plain,(
% 0.22/0.55    sK0 != k1_relset_1(sK0,k1_xboole_0,sK2) | (spl6_16 | ~spl6_17)),
% 0.22/0.55    inference(forward_demodulation,[],[f195,f200])).
% 0.22/0.55  fof(f195,plain,(
% 0.22/0.55    sK0 != k1_relset_1(sK0,sK1,sK2) | spl6_16),
% 0.22/0.55    inference(avatar_component_clause,[],[f194])).
% 0.22/0.55  fof(f313,plain,(
% 0.22/0.55    spl6_27 | ~spl6_13 | ~spl6_17),
% 0.22/0.55    inference(avatar_split_clause,[],[f231,f198,f158,f310])).
% 0.22/0.55  fof(f231,plain,(
% 0.22/0.55    k1_xboole_0 = k1_relat_1(k2_funct_1(sK2)) | (~spl6_13 | ~spl6_17)),
% 0.22/0.55    inference(backward_demodulation,[],[f160,f200])).
% 0.22/0.55  fof(f281,plain,(
% 0.22/0.55    ~spl6_22 | spl6_8 | ~spl6_17),
% 0.22/0.55    inference(avatar_split_clause,[],[f253,f198,f130,f278])).
% 0.22/0.55  fof(f253,plain,(
% 0.22/0.55    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl6_8 | ~spl6_17)),
% 0.22/0.55    inference(forward_demodulation,[],[f132,f200])).
% 0.22/0.55  fof(f265,plain,(
% 0.22/0.55    spl6_20 | ~spl6_4 | ~spl6_17),
% 0.22/0.55    inference(avatar_split_clause,[],[f236,f198,f106,f262])).
% 0.22/0.55  fof(f236,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl6_4 | ~spl6_17)),
% 0.22/0.55    inference(forward_demodulation,[],[f223,f77])).
% 0.22/0.55  fof(f223,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl6_4 | ~spl6_17)),
% 0.22/0.55    inference(backward_demodulation,[],[f108,f200])).
% 0.22/0.55  fof(f260,plain,(
% 0.22/0.55    spl6_19 | ~spl6_3 | ~spl6_17),
% 0.22/0.55    inference(avatar_split_clause,[],[f222,f198,f99,f257])).
% 0.22/0.55  fof(f99,plain,(
% 0.22/0.55    spl6_3 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.55  fof(f222,plain,(
% 0.22/0.55    v1_funct_2(sK2,sK0,k1_xboole_0) | (~spl6_3 | ~spl6_17)),
% 0.22/0.55    inference(backward_demodulation,[],[f101,f200])).
% 0.22/0.55  fof(f101,plain,(
% 0.22/0.55    v1_funct_2(sK2,sK0,sK1) | ~spl6_3),
% 0.22/0.55    inference(avatar_component_clause,[],[f99])).
% 0.22/0.55  fof(f249,plain,(
% 0.22/0.55    spl6_7 | ~spl6_9 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_17),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f248])).
% 0.22/0.55  fof(f248,plain,(
% 0.22/0.55    $false | (spl6_7 | ~spl6_9 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_17)),
% 0.22/0.55    inference(subsumption_resolution,[],[f135,f246])).
% 0.22/0.55  fof(f246,plain,(
% 0.22/0.55    ~v1_funct_1(k2_funct_1(sK2)) | (spl6_7 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_17)),
% 0.22/0.55    inference(subsumption_resolution,[],[f245,f237])).
% 0.22/0.55  fof(f237,plain,(
% 0.22/0.55    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (spl6_7 | ~spl6_17)),
% 0.22/0.55    inference(forward_demodulation,[],[f226,f78])).
% 0.22/0.55  fof(f226,plain,(
% 0.22/0.55    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl6_7 | ~spl6_17)),
% 0.22/0.55    inference(backward_demodulation,[],[f128,f200])).
% 0.22/0.55  fof(f128,plain,(
% 0.22/0.55    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl6_7),
% 0.22/0.55    inference(avatar_component_clause,[],[f126])).
% 0.22/0.55  fof(f126,plain,(
% 0.22/0.55    spl6_7 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.55  fof(f221,plain,(
% 0.22/0.55    ~spl6_1 | spl6_9 | ~spl6_12),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f220])).
% 0.22/0.55  fof(f220,plain,(
% 0.22/0.55    $false | (~spl6_1 | spl6_9 | ~spl6_12)),
% 0.22/0.55    inference(subsumption_resolution,[],[f219,f155])).
% 0.22/0.55  fof(f155,plain,(
% 0.22/0.55    v1_relat_1(sK2) | ~spl6_12),
% 0.22/0.55    inference(avatar_component_clause,[],[f154])).
% 0.22/0.55  fof(f154,plain,(
% 0.22/0.55    spl6_12 <=> v1_relat_1(sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.22/0.55  fof(f219,plain,(
% 0.22/0.55    ~v1_relat_1(sK2) | (~spl6_1 | spl6_9)),
% 0.22/0.55    inference(subsumption_resolution,[],[f217,f87])).
% 0.22/0.55  fof(f87,plain,(
% 0.22/0.55    v1_funct_1(sK2) | ~spl6_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f85])).
% 0.22/0.55  fof(f85,plain,(
% 0.22/0.55    spl6_1 <=> v1_funct_1(sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.55  fof(f217,plain,(
% 0.22/0.55    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl6_9),
% 0.22/0.55    inference(resolution,[],[f136,f44])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f24])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(flattening,[],[f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.55  fof(f136,plain,(
% 0.22/0.55    ~v1_funct_1(k2_funct_1(sK2)) | spl6_9),
% 0.22/0.55    inference(avatar_component_clause,[],[f134])).
% 0.22/0.55  fof(f216,plain,(
% 0.22/0.55    ~spl6_9 | ~spl6_4 | spl6_7 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_16),
% 0.22/0.55    inference(avatar_split_clause,[],[f215,f194,f182,f177,f158,f126,f106,f134])).
% 0.22/0.55  fof(f215,plain,(
% 0.22/0.55    ~v1_funct_1(k2_funct_1(sK2)) | (~spl6_4 | spl6_7 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_16)),
% 0.22/0.55    inference(subsumption_resolution,[],[f211,f128])).
% 0.22/0.55  fof(f211,plain,(
% 0.22/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl6_4 | ~spl6_13 | ~spl6_14 | ~spl6_15 | ~spl6_16)),
% 0.22/0.55    inference(backward_demodulation,[],[f189,f209])).
% 0.22/0.55  fof(f201,plain,(
% 0.22/0.55    spl6_16 | spl6_17 | ~spl6_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f104,f99,f198,f194])).
% 0.22/0.55  fof(f104,plain,(
% 0.22/0.55    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl6_3),
% 0.22/0.55    inference(subsumption_resolution,[],[f103,f36])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.55    inference(flattening,[],[f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.55    inference(ennf_transformation,[],[f17])).
% 0.22/0.55  fof(f17,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.55    inference(negated_conjecture,[],[f16])).
% 0.22/0.55  fof(f16,conjecture,(
% 0.22/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.22/0.55  fof(f103,plain,(
% 0.22/0.55    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_3),
% 0.22/0.55    inference(resolution,[],[f101,f74])).
% 0.22/0.55  fof(f74,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f32])).
% 0.22/0.55  fof(f185,plain,(
% 0.22/0.55    spl6_15 | ~spl6_1 | ~spl6_2 | ~spl6_12),
% 0.22/0.55    inference(avatar_split_clause,[],[f166,f154,f90,f85,f182])).
% 0.22/0.55  fof(f90,plain,(
% 0.22/0.55    spl6_2 <=> v2_funct_1(sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.55  fof(f166,plain,(
% 0.22/0.55    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl6_1 | ~spl6_2 | ~spl6_12)),
% 0.22/0.55    inference(subsumption_resolution,[],[f97,f155])).
% 0.22/0.55  fof(f97,plain,(
% 0.22/0.55    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl6_1 | ~spl6_2)),
% 0.22/0.55    inference(subsumption_resolution,[],[f95,f87])).
% 0.22/0.55  fof(f95,plain,(
% 0.22/0.55    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl6_2),
% 0.22/0.55    inference(resolution,[],[f92,f46])).
% 0.22/0.55  fof(f46,plain,(
% 0.22/0.55    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(flattening,[],[f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,axiom,(
% 0.22/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.55  fof(f92,plain,(
% 0.22/0.55    v2_funct_1(sK2) | ~spl6_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f90])).
% 0.22/0.55  fof(f180,plain,(
% 0.22/0.55    spl6_14 | ~spl6_1 | ~spl6_12),
% 0.22/0.55    inference(avatar_split_clause,[],[f170,f154,f85,f177])).
% 0.22/0.55  fof(f170,plain,(
% 0.22/0.55    v1_relat_1(k2_funct_1(sK2)) | (~spl6_1 | ~spl6_12)),
% 0.22/0.55    inference(subsumption_resolution,[],[f168,f87])).
% 0.22/0.55  fof(f168,plain,(
% 0.22/0.55    ~v1_funct_1(sK2) | v1_relat_1(k2_funct_1(sK2)) | ~spl6_12),
% 0.22/0.55    inference(resolution,[],[f155,f43])).
% 0.22/0.55  fof(f43,plain,(
% 0.22/0.55    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f24])).
% 0.22/0.55  fof(f164,plain,(
% 0.22/0.55    ~spl6_4 | spl6_12),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f163])).
% 0.22/0.55  fof(f163,plain,(
% 0.22/0.55    $false | (~spl6_4 | spl6_12)),
% 0.22/0.55    inference(subsumption_resolution,[],[f108,f162])).
% 0.22/0.55  fof(f162,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl6_12),
% 0.22/0.55    inference(resolution,[],[f156,f66])).
% 0.22/0.55  fof(f66,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f10])).
% 0.22/0.55  fof(f10,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.55  fof(f156,plain,(
% 0.22/0.55    ~v1_relat_1(sK2) | spl6_12),
% 0.22/0.55    inference(avatar_component_clause,[],[f154])).
% 0.22/0.55  fof(f161,plain,(
% 0.22/0.55    ~spl6_12 | spl6_13 | ~spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_5),
% 0.22/0.55    inference(avatar_split_clause,[],[f119,f111,f106,f90,f85,f158,f154])).
% 0.22/0.55  fof(f111,plain,(
% 0.22/0.55    spl6_5 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.55  fof(f119,plain,(
% 0.22/0.55    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | (~spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_5)),
% 0.22/0.55    inference(backward_demodulation,[],[f96,f118])).
% 0.22/0.55  fof(f118,plain,(
% 0.22/0.55    sK1 = k2_relat_1(sK2) | (~spl6_4 | ~spl6_5)),
% 0.22/0.55    inference(subsumption_resolution,[],[f116,f108])).
% 0.22/0.55  fof(f116,plain,(
% 0.22/0.55    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_5),
% 0.22/0.55    inference(superposition,[],[f113,f68])).
% 0.22/0.55  fof(f68,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(ennf_transformation,[],[f12])).
% 0.22/0.55  fof(f12,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.55  fof(f113,plain,(
% 0.22/0.55    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl6_5),
% 0.22/0.55    inference(avatar_component_clause,[],[f111])).
% 0.22/0.55  fof(f96,plain,(
% 0.22/0.55    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl6_1 | ~spl6_2)),
% 0.22/0.55    inference(subsumption_resolution,[],[f94,f87])).
% 0.22/0.55  fof(f94,plain,(
% 0.22/0.55    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl6_2),
% 0.22/0.55    inference(resolution,[],[f92,f45])).
% 0.22/0.55  fof(f45,plain,(
% 0.22/0.55    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f26])).
% 0.22/0.55  fof(f137,plain,(
% 0.22/0.55    ~spl6_7 | ~spl6_8 | ~spl6_9),
% 0.22/0.55    inference(avatar_split_clause,[],[f33,f134,f130,f126])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  fof(f114,plain,(
% 0.22/0.55    spl6_5),
% 0.22/0.55    inference(avatar_split_clause,[],[f38,f111])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  fof(f109,plain,(
% 0.22/0.55    spl6_4),
% 0.22/0.55    inference(avatar_split_clause,[],[f36,f106])).
% 0.22/0.55  fof(f102,plain,(
% 0.22/0.55    spl6_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f35,f99])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  fof(f93,plain,(
% 0.22/0.55    spl6_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f37,f90])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    v2_funct_1(sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  fof(f88,plain,(
% 0.22/0.55    spl6_1),
% 0.22/0.55    inference(avatar_split_clause,[],[f34,f85])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    v1_funct_1(sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (2689)------------------------------
% 0.22/0.55  % (2689)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (2689)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (2689)Memory used [KB]: 11129
% 0.22/0.55  % (2689)Time elapsed: 0.130 s
% 0.22/0.55  % (2689)------------------------------
% 0.22/0.55  % (2689)------------------------------
% 0.22/0.56  % (2668)Success in time 0.186 s
%------------------------------------------------------------------------------
