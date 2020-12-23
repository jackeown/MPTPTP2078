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
% DateTime   : Thu Dec  3 13:07:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  214 ( 487 expanded)
%              Number of leaves         :   55 ( 224 expanded)
%              Depth                    :   17
%              Number of atoms          :  799 (2246 expanded)
%              Number of equality atoms :  128 ( 465 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f325,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f85,f90,f95,f100,f105,f110,f118,f123,f128,f135,f140,f146,f151,f158,f163,f174,f179,f185,f192,f198,f209,f215,f221,f226,f231,f236,f247,f255,f273,f279,f291,f304,f312,f318,f324])).

fof(f324,plain,
    ( ~ spl6_2
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_22
    | ~ spl6_30
    | spl6_37 ),
    inference(avatar_contradiction_clause,[],[f323])).

fof(f323,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_22
    | ~ spl6_30
    | spl6_37 ),
    inference(subsumption_resolution,[],[f322,f145])).

fof(f145,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl6_13
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f322,plain,
    ( ~ r2_hidden(sK5,sK1)
    | ~ spl6_2
    | ~ spl6_11
    | ~ spl6_22
    | ~ spl6_30
    | spl6_37 ),
    inference(forward_demodulation,[],[f321,f254])).

fof(f254,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl6_30
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f321,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ spl6_2
    | ~ spl6_11
    | ~ spl6_22
    | spl6_37 ),
    inference(subsumption_resolution,[],[f320,f134])).

fof(f134,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl6_11
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f320,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl6_2
    | ~ spl6_22
    | spl6_37 ),
    inference(subsumption_resolution,[],[f319,f208])).

fof(f208,plain,
    ( v5_relat_1(sK3,k1_relat_1(sK4))
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl6_22
  <=> v5_relat_1(sK3,k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f319,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ v5_relat_1(sK3,k1_relat_1(sK4))
    | ~ v1_relat_1(sK3)
    | ~ spl6_2
    | spl6_37 ),
    inference(subsumption_resolution,[],[f314,f84])).

fof(f84,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl6_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f314,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v5_relat_1(sK3,k1_relat_1(sK4))
    | ~ v1_relat_1(sK3)
    | spl6_37 ),
    inference(resolution,[],[f311,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).

fof(f311,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | spl6_37 ),
    inference(avatar_component_clause,[],[f309])).

fof(f309,plain,
    ( spl6_37
  <=> r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f318,plain,
    ( ~ spl6_2
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_22
    | ~ spl6_30
    | spl6_37 ),
    inference(avatar_contradiction_clause,[],[f317])).

fof(f317,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_11
    | ~ spl6_13
    | ~ spl6_22
    | ~ spl6_30
    | spl6_37 ),
    inference(subsumption_resolution,[],[f316,f145])).

fof(f316,plain,
    ( ~ r2_hidden(sK5,sK1)
    | ~ spl6_2
    | ~ spl6_11
    | ~ spl6_22
    | ~ spl6_30
    | spl6_37 ),
    inference(forward_demodulation,[],[f313,f254])).

fof(f313,plain,
    ( ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ spl6_2
    | ~ spl6_11
    | ~ spl6_22
    | spl6_37 ),
    inference(unit_resulting_resolution,[],[f134,f84,f208,f311,f59])).

fof(f312,plain,
    ( ~ spl6_37
    | ~ spl6_3
    | ~ spl6_12
    | ~ spl6_16
    | spl6_36 ),
    inference(avatar_split_clause,[],[f305,f301,f160,f137,f87,f309])).

fof(f87,plain,
    ( spl6_3
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f137,plain,
    ( spl6_12
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f160,plain,
    ( spl6_16
  <=> v5_relat_1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f301,plain,
    ( spl6_36
  <=> k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f305,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ spl6_3
    | ~ spl6_12
    | ~ spl6_16
    | spl6_36 ),
    inference(unit_resulting_resolution,[],[f139,f89,f162,f303,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

fof(f303,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl6_36 ),
    inference(avatar_component_clause,[],[f301])).

fof(f162,plain,
    ( v5_relat_1(sK4,sK0)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f160])).

fof(f89,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f139,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f137])).

fof(f304,plain,
    ( ~ spl6_36
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | spl6_6
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_21
    | ~ spl6_23
    | ~ spl6_26
    | spl6_27 ),
    inference(avatar_split_clause,[],[f299,f233,f228,f212,f195,f125,f120,f107,f102,f97,f87,f82,f77,f301])).

fof(f77,plain,
    ( spl6_1
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f97,plain,
    ( spl6_5
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f102,plain,
    ( spl6_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f107,plain,
    ( spl6_7
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f120,plain,
    ( spl6_9
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f125,plain,
    ( spl6_10
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f195,plain,
    ( spl6_21
  <=> k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f212,plain,
    ( spl6_23
  <=> r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f228,plain,
    ( spl6_26
  <=> k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f233,plain,
    ( spl6_27
  <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f299,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | spl6_6
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_21
    | ~ spl6_23
    | ~ spl6_26
    | spl6_27 ),
    inference(backward_demodulation,[],[f235,f298])).

fof(f298,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | spl6_6
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_21
    | ~ spl6_23
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f297,f214])).

fof(f214,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f212])).

fof(f297,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | spl6_6
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_21
    | ~ spl6_26 ),
    inference(forward_demodulation,[],[f296,f230])).

% (20766)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f230,plain,
    ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f228])).

fof(f296,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4))
    | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | spl6_6
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f295,f89])).

fof(f295,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ v1_funct_1(sK4)
    | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | spl6_6
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_21 ),
    inference(resolution,[],[f294,f127])).

fof(f127,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f125])).

fof(f294,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1))
        | ~ v1_funct_1(X1)
        | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_5
    | spl6_6
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_21 ),
    inference(resolution,[],[f285,f99])).

fof(f99,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f97])).

fof(f285,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,sK1)
        | ~ r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ v1_funct_1(X1)
        | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2)) )
    | spl6_1
    | ~ spl6_2
    | spl6_6
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_21 ),
    inference(forward_demodulation,[],[f284,f197])).

fof(f197,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f195])).

fof(f284,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
        | ~ m1_subset_1(X2,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ v1_funct_1(X1)
        | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2)) )
    | spl6_1
    | ~ spl6_2
    | spl6_6
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f283,f79])).

fof(f79,plain,
    ( ~ v1_xboole_0(sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f283,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
        | ~ m1_subset_1(X2,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ v1_funct_1(X1)
        | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
        | v1_xboole_0(sK2) )
    | ~ spl6_2
    | spl6_6
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f282,f84])).

fof(f282,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
        | ~ m1_subset_1(X2,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ v1_funct_1(X1)
        | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
        | ~ v1_funct_1(sK3)
        | v1_xboole_0(sK2) )
    | spl6_6
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f281,f122])).

fof(f122,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f120])).

fof(f281,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
        | ~ m1_subset_1(X2,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
        | ~ v1_funct_1(sK3)
        | v1_xboole_0(sK2) )
    | spl6_6
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f280,f104])).

fof(f104,plain,
    ( k1_xboole_0 != sK1
    | spl6_6 ),
    inference(avatar_component_clause,[],[f102])).

fof(f280,plain,
    ( ! [X2,X0,X1] :
        ( k1_xboole_0 = sK1
        | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1))
        | ~ m1_subset_1(X2,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))
        | ~ v1_funct_1(sK3)
        | v1_xboole_0(sK2) )
    | ~ spl6_7 ),
    inference(resolution,[],[f61,f109])).

fof(f109,plain,
    ( v1_funct_2(sK3,sK1,sK2)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f107])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_2(X3,X1,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

fof(f235,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
    | spl6_27 ),
    inference(avatar_component_clause,[],[f233])).

fof(f291,plain,
    ( ~ spl6_35
    | ~ spl6_10
    | spl6_31
    | spl6_32 ),
    inference(avatar_split_clause,[],[f286,f266,f262,f125,f288])).

fof(f288,plain,
    ( spl6_35
  <=> sK2 = k1_relset_1(sK2,sK0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f262,plain,
    ( spl6_31
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f266,plain,
    ( spl6_32
  <=> v1_funct_2(sK4,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f286,plain,
    ( sK2 != k1_relset_1(sK2,sK0,sK4)
    | ~ spl6_10
    | spl6_31
    | spl6_32 ),
    inference(unit_resulting_resolution,[],[f263,f127,f267,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f267,plain,
    ( ~ v1_funct_2(sK4,sK2,sK0)
    | spl6_32 ),
    inference(avatar_component_clause,[],[f266])).

fof(f263,plain,
    ( k1_xboole_0 != sK0
    | spl6_31 ),
    inference(avatar_component_clause,[],[f262])).

fof(f279,plain,
    ( ~ spl6_34
    | spl6_31 ),
    inference(avatar_split_clause,[],[f274,f262,f276])).

fof(f276,plain,
    ( spl6_34
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f274,plain,
    ( ~ v1_xboole_0(sK0)
    | spl6_31 ),
    inference(unit_resulting_resolution,[],[f263,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f273,plain,
    ( spl6_31
    | spl6_32
    | ~ spl6_33
    | ~ spl6_10
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f257,f228,f125,f270,f266,f262])).

fof(f270,plain,
    ( spl6_33
  <=> sK2 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f257,plain,
    ( sK2 != k1_relat_1(sK4)
    | v1_funct_2(sK4,sK2,sK0)
    | k1_xboole_0 = sK0
    | ~ spl6_10
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f256,f127])).

fof(f256,plain,
    ( sK2 != k1_relat_1(sK4)
    | v1_funct_2(sK4,sK2,sK0)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl6_26 ),
    inference(superposition,[],[f67,f230])).

fof(f255,plain,
    ( spl6_30
    | ~ spl6_25
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f248,f244,f223,f252])).

fof(f223,plain,
    ( spl6_25
  <=> k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f244,plain,
    ( spl6_29
  <=> sK1 = k1_relset_1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f248,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl6_25
    | ~ spl6_29 ),
    inference(backward_demodulation,[],[f225,f246])).

fof(f246,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f244])).

fof(f225,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f223])).

fof(f247,plain,
    ( spl6_28
    | spl6_29
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f238,f120,f107,f244,f240])).

fof(f240,plain,
    ( spl6_28
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f238,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = sK2
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f237,f122])).

fof(f237,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_7 ),
    inference(resolution,[],[f65,f109])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f236,plain,(
    ~ spl6_27 ),
    inference(avatar_split_clause,[],[f51,f233])).

fof(f51,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
    & k1_xboole_0 != sK1
    & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    & m1_subset_1(sK5,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f18,f38,f37,f36,f35])).

fof(f35,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                    & k1_xboole_0 != X1
                    & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                    & m1_subset_1(X5,X1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != sK1
                  & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4))
                  & m1_subset_1(X5,sK1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X3,sK1,sK2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5))
                & k1_xboole_0 != sK1
                & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4))
                & m1_subset_1(X5,sK1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_2(X3,sK1,sK2)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5))
              & k1_xboole_0 != sK1
              & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4))
              & m1_subset_1(X5,sK1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5))
            & k1_xboole_0 != sK1
            & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4))
            & m1_subset_1(X5,sK1) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5))
          & k1_xboole_0 != sK1
          & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
          & m1_subset_1(X5,sK1) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X5] :
        ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5))
        & k1_xboole_0 != sK1
        & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
        & m1_subset_1(X5,sK1) )
   => ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))
      & k1_xboole_0 != sK1
      & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
      & m1_subset_1(sK5,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                  & k1_xboole_0 != X1
                  & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  & m1_subset_1(X5,X1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
           => ! [X4] :
                ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                  & v1_funct_1(X4) )
               => ! [X5] :
                    ( m1_subset_1(X5,X1)
                   => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                     => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                        | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).

fof(f231,plain,
    ( spl6_26
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f200,f125,f228])).

fof(f200,plain,
    ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f127,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f226,plain,
    ( spl6_25
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f199,f120,f223])).

fof(f199,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3)
    | ~ spl6_9 ),
    inference(unit_resulting_resolution,[],[f122,f63])).

fof(f221,plain,
    ( spl6_24
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f165,f125,f218])).

fof(f218,plain,
    ( spl6_24
  <=> k2_relset_1(sK2,sK0,sK4) = k2_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f165,plain,
    ( k2_relset_1(sK2,sK0,sK4) = k2_relat_1(sK4)
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f127,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f215,plain,
    ( spl6_23
    | ~ spl6_10
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f204,f182,f125,f212])).

fof(f182,plain,
    ( spl6_19
  <=> r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f204,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))
    | ~ spl6_10
    | ~ spl6_19 ),
    inference(backward_demodulation,[],[f184,f200])).

fof(f184,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f182])).

fof(f209,plain,
    ( spl6_22
    | ~ spl6_10
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f203,f189,f125,f206])).

fof(f189,plain,
    ( spl6_20
  <=> v5_relat_1(sK3,k1_relset_1(sK2,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f203,plain,
    ( v5_relat_1(sK3,k1_relat_1(sK4))
    | ~ spl6_10
    | ~ spl6_20 ),
    inference(backward_demodulation,[],[f191,f200])).

fof(f191,plain,
    ( v5_relat_1(sK3,k1_relset_1(sK2,sK0,sK4))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f189])).

fof(f198,plain,
    ( spl6_21
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f164,f120,f195])).

fof(f164,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)
    | ~ spl6_9 ),
    inference(unit_resulting_resolution,[],[f122,f62])).

fof(f192,plain,
    ( spl6_20
    | ~ spl6_11
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f187,f182,f132,f189])).

fof(f187,plain,
    ( v5_relat_1(sK3,k1_relset_1(sK2,sK0,sK4))
    | ~ spl6_11
    | ~ spl6_19 ),
    inference(unit_resulting_resolution,[],[f134,f184,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f185,plain,
    ( spl6_19
    | ~ spl6_9
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f167,f148,f120,f182])).

fof(f148,plain,
    ( spl6_14
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f167,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ spl6_9
    | ~ spl6_14 ),
    inference(backward_demodulation,[],[f150,f164])).

fof(f150,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f148])).

fof(f179,plain,
    ( spl6_18
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f169,f160,f137,f176])).

fof(f176,plain,
    ( spl6_18
  <=> r1_tarski(k2_relat_1(sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f169,plain,
    ( r1_tarski(k2_relat_1(sK4),sK0)
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f139,f162,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f174,plain,
    ( spl6_17
    | ~ spl6_11
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f168,f155,f132,f171])).

fof(f171,plain,
    ( spl6_17
  <=> r1_tarski(k2_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f155,plain,
    ( spl6_15
  <=> v5_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f168,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | ~ spl6_11
    | ~ spl6_15 ),
    inference(unit_resulting_resolution,[],[f134,f157,f56])).

fof(f157,plain,
    ( v5_relat_1(sK3,sK2)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f155])).

fof(f163,plain,
    ( spl6_16
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f153,f125,f160])).

fof(f153,plain,
    ( v5_relat_1(sK4,sK0)
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f127,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f158,plain,
    ( spl6_15
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f152,f120,f155])).

fof(f152,plain,
    ( v5_relat_1(sK3,sK2)
    | ~ spl6_9 ),
    inference(unit_resulting_resolution,[],[f122,f64])).

fof(f151,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f49,f148])).

fof(f49,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f39])).

fof(f146,plain,
    ( spl6_13
    | ~ spl6_5
    | spl6_8 ),
    inference(avatar_split_clause,[],[f141,f115,f97,f143])).

fof(f115,plain,
    ( spl6_8
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f141,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl6_5
    | spl6_8 ),
    inference(unit_resulting_resolution,[],[f99,f117,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f117,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_8 ),
    inference(avatar_component_clause,[],[f115])).

fof(f140,plain,
    ( spl6_12
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f130,f125,f137])).

fof(f130,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_10 ),
    inference(unit_resulting_resolution,[],[f55,f127,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f55,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f135,plain,
    ( spl6_11
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f129,f120,f132])).

fof(f129,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_9 ),
    inference(unit_resulting_resolution,[],[f55,f122,f53])).

fof(f128,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f47,f125])).

fof(f47,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f123,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f45,f120])).

fof(f45,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f39])).

fof(f118,plain,
    ( ~ spl6_8
    | spl6_6 ),
    inference(avatar_split_clause,[],[f112,f102,f115])).

fof(f112,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_6 ),
    inference(unit_resulting_resolution,[],[f104,f54])).

fof(f110,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f44,f107])).

fof(f44,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f105,plain,(
    ~ spl6_6 ),
    inference(avatar_split_clause,[],[f50,f102])).

fof(f50,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f39])).

fof(f100,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f48,f97])).

fof(f48,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f95,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f52,f92])).

fof(f92,plain,
    ( spl6_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f90,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f46,f87])).

fof(f46,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f85,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f43,f82])).

fof(f43,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f80,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f42,f77])).

fof(f42,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:46:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.41  % (20769)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (20769)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f325,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f80,f85,f90,f95,f100,f105,f110,f118,f123,f128,f135,f140,f146,f151,f158,f163,f174,f179,f185,f192,f198,f209,f215,f221,f226,f231,f236,f247,f255,f273,f279,f291,f304,f312,f318,f324])).
% 0.21/0.49  fof(f324,plain,(
% 0.21/0.49    ~spl6_2 | ~spl6_11 | ~spl6_13 | ~spl6_22 | ~spl6_30 | spl6_37),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f323])).
% 0.21/0.49  fof(f323,plain,(
% 0.21/0.49    $false | (~spl6_2 | ~spl6_11 | ~spl6_13 | ~spl6_22 | ~spl6_30 | spl6_37)),
% 0.21/0.49    inference(subsumption_resolution,[],[f322,f145])).
% 0.21/0.49  fof(f145,plain,(
% 0.21/0.49    r2_hidden(sK5,sK1) | ~spl6_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f143])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    spl6_13 <=> r2_hidden(sK5,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.49  fof(f322,plain,(
% 0.21/0.49    ~r2_hidden(sK5,sK1) | (~spl6_2 | ~spl6_11 | ~spl6_22 | ~spl6_30 | spl6_37)),
% 0.21/0.49    inference(forward_demodulation,[],[f321,f254])).
% 0.21/0.49  fof(f254,plain,(
% 0.21/0.49    sK1 = k1_relat_1(sK3) | ~spl6_30),
% 0.21/0.49    inference(avatar_component_clause,[],[f252])).
% 0.21/0.49  fof(f252,plain,(
% 0.21/0.49    spl6_30 <=> sK1 = k1_relat_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.21/0.49  fof(f321,plain,(
% 0.21/0.49    ~r2_hidden(sK5,k1_relat_1(sK3)) | (~spl6_2 | ~spl6_11 | ~spl6_22 | spl6_37)),
% 0.21/0.49    inference(subsumption_resolution,[],[f320,f134])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    v1_relat_1(sK3) | ~spl6_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f132])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    spl6_11 <=> v1_relat_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.49  fof(f320,plain,(
% 0.21/0.49    ~r2_hidden(sK5,k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl6_2 | ~spl6_22 | spl6_37)),
% 0.21/0.49    inference(subsumption_resolution,[],[f319,f208])).
% 0.21/0.49  fof(f208,plain,(
% 0.21/0.49    v5_relat_1(sK3,k1_relat_1(sK4)) | ~spl6_22),
% 0.21/0.49    inference(avatar_component_clause,[],[f206])).
% 0.21/0.49  fof(f206,plain,(
% 0.21/0.49    spl6_22 <=> v5_relat_1(sK3,k1_relat_1(sK4))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.21/0.49  fof(f319,plain,(
% 0.21/0.49    ~r2_hidden(sK5,k1_relat_1(sK3)) | ~v5_relat_1(sK3,k1_relat_1(sK4)) | ~v1_relat_1(sK3) | (~spl6_2 | spl6_37)),
% 0.21/0.49    inference(subsumption_resolution,[],[f314,f84])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    v1_funct_1(sK3) | ~spl6_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f82])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    spl6_2 <=> v1_funct_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.49  fof(f314,plain,(
% 0.21/0.49    ~r2_hidden(sK5,k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v5_relat_1(sK3,k1_relat_1(sK4)) | ~v1_relat_1(sK3) | spl6_37),
% 0.21/0.49    inference(resolution,[],[f311,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_funct_1)).
% 0.21/0.49  fof(f311,plain,(
% 0.21/0.49    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | spl6_37),
% 0.21/0.49    inference(avatar_component_clause,[],[f309])).
% 0.21/0.49  fof(f309,plain,(
% 0.21/0.49    spl6_37 <=> r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 0.21/0.49  fof(f318,plain,(
% 0.21/0.49    ~spl6_2 | ~spl6_11 | ~spl6_13 | ~spl6_22 | ~spl6_30 | spl6_37),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f317])).
% 0.21/0.49  fof(f317,plain,(
% 0.21/0.49    $false | (~spl6_2 | ~spl6_11 | ~spl6_13 | ~spl6_22 | ~spl6_30 | spl6_37)),
% 0.21/0.49    inference(subsumption_resolution,[],[f316,f145])).
% 0.21/0.49  fof(f316,plain,(
% 0.21/0.49    ~r2_hidden(sK5,sK1) | (~spl6_2 | ~spl6_11 | ~spl6_22 | ~spl6_30 | spl6_37)),
% 0.21/0.49    inference(forward_demodulation,[],[f313,f254])).
% 0.21/0.49  fof(f313,plain,(
% 0.21/0.49    ~r2_hidden(sK5,k1_relat_1(sK3)) | (~spl6_2 | ~spl6_11 | ~spl6_22 | spl6_37)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f134,f84,f208,f311,f59])).
% 0.21/0.49  fof(f312,plain,(
% 0.21/0.49    ~spl6_37 | ~spl6_3 | ~spl6_12 | ~spl6_16 | spl6_36),
% 0.21/0.49    inference(avatar_split_clause,[],[f305,f301,f160,f137,f87,f309])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    spl6_3 <=> v1_funct_1(sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    spl6_12 <=> v1_relat_1(sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    spl6_16 <=> v5_relat_1(sK4,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.21/0.49  fof(f301,plain,(
% 0.21/0.49    spl6_36 <=> k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 0.21/0.49  fof(f305,plain,(
% 0.21/0.49    ~r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | (~spl6_3 | ~spl6_12 | ~spl6_16 | spl6_36)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f139,f89,f162,f303,f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k1_funct_1(X1,X2) = k7_partfun1(X0,X1,X2)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).
% 0.21/0.49  fof(f303,plain,(
% 0.21/0.49    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | spl6_36),
% 0.21/0.49    inference(avatar_component_clause,[],[f301])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    v5_relat_1(sK4,sK0) | ~spl6_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f160])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    v1_funct_1(sK4) | ~spl6_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f87])).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    v1_relat_1(sK4) | ~spl6_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f137])).
% 0.21/0.49  fof(f304,plain,(
% 0.21/0.49    ~spl6_36 | spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_5 | spl6_6 | ~spl6_7 | ~spl6_9 | ~spl6_10 | ~spl6_21 | ~spl6_23 | ~spl6_26 | spl6_27),
% 0.21/0.49    inference(avatar_split_clause,[],[f299,f233,f228,f212,f195,f125,f120,f107,f102,f97,f87,f82,f77,f301])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    spl6_1 <=> v1_xboole_0(sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    spl6_5 <=> m1_subset_1(sK5,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    spl6_6 <=> k1_xboole_0 = sK1),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    spl6_7 <=> v1_funct_2(sK3,sK1,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    spl6_9 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    spl6_10 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.49  fof(f195,plain,(
% 0.21/0.49    spl6_21 <=> k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.21/0.49  fof(f212,plain,(
% 0.21/0.49    spl6_23 <=> r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.21/0.49  fof(f228,plain,(
% 0.21/0.49    spl6_26 <=> k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.21/0.49  fof(f233,plain,(
% 0.21/0.49    spl6_27 <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.21/0.49  fof(f299,plain,(
% 0.21/0.49    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_5 | spl6_6 | ~spl6_7 | ~spl6_9 | ~spl6_10 | ~spl6_21 | ~spl6_23 | ~spl6_26 | spl6_27)),
% 0.21/0.49    inference(backward_demodulation,[],[f235,f298])).
% 0.21/0.49  fof(f298,plain,(
% 0.21/0.49    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_5 | spl6_6 | ~spl6_7 | ~spl6_9 | ~spl6_10 | ~spl6_21 | ~spl6_23 | ~spl6_26)),
% 0.21/0.49    inference(subsumption_resolution,[],[f297,f214])).
% 0.21/0.49  fof(f214,plain,(
% 0.21/0.49    r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | ~spl6_23),
% 0.21/0.49    inference(avatar_component_clause,[],[f212])).
% 0.21/0.49  fof(f297,plain,(
% 0.21/0.49    ~r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_5 | spl6_6 | ~spl6_7 | ~spl6_9 | ~spl6_10 | ~spl6_21 | ~spl6_26)),
% 0.21/0.49    inference(forward_demodulation,[],[f296,f230])).
% 0.21/0.49  % (20766)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  fof(f230,plain,(
% 0.21/0.49    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) | ~spl6_26),
% 0.21/0.49    inference(avatar_component_clause,[],[f228])).
% 0.21/0.49  fof(f296,plain,(
% 0.21/0.49    ~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4)) | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_5 | spl6_6 | ~spl6_7 | ~spl6_9 | ~spl6_10 | ~spl6_21)),
% 0.21/0.49    inference(subsumption_resolution,[],[f295,f89])).
% 0.21/0.49  fof(f295,plain,(
% 0.21/0.49    ~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4)) | ~v1_funct_1(sK4) | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (spl6_1 | ~spl6_2 | ~spl6_5 | spl6_6 | ~spl6_7 | ~spl6_9 | ~spl6_10 | ~spl6_21)),
% 0.21/0.49    inference(resolution,[],[f294,f127])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl6_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f125])).
% 0.21/0.49  fof(f294,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1)) | ~v1_funct_1(X1) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),sK5) = k1_funct_1(X1,k1_funct_1(sK3,sK5))) ) | (spl6_1 | ~spl6_2 | ~spl6_5 | spl6_6 | ~spl6_7 | ~spl6_9 | ~spl6_21)),
% 0.21/0.49    inference(resolution,[],[f285,f99])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    m1_subset_1(sK5,sK1) | ~spl6_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f97])).
% 0.21/0.49  fof(f285,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,sK1) | ~r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X1) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))) ) | (spl6_1 | ~spl6_2 | spl6_6 | ~spl6_7 | ~spl6_9 | ~spl6_21)),
% 0.21/0.49    inference(forward_demodulation,[],[f284,f197])).
% 0.21/0.49  fof(f197,plain,(
% 0.21/0.49    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) | ~spl6_21),
% 0.21/0.49    inference(avatar_component_clause,[],[f195])).
% 0.21/0.49  fof(f284,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1)) | ~m1_subset_1(X2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X1) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2))) ) | (spl6_1 | ~spl6_2 | spl6_6 | ~spl6_7 | ~spl6_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f283,f79])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    ~v1_xboole_0(sK2) | spl6_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f77])).
% 0.21/0.49  fof(f283,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1)) | ~m1_subset_1(X2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X1) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2)) | v1_xboole_0(sK2)) ) | (~spl6_2 | spl6_6 | ~spl6_7 | ~spl6_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f282,f84])).
% 0.21/0.49  fof(f282,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1)) | ~m1_subset_1(X2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X1) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2)) | ~v1_funct_1(sK3) | v1_xboole_0(sK2)) ) | (spl6_6 | ~spl6_7 | ~spl6_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f281,f122])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f120])).
% 0.21/0.49  fof(f281,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1)) | ~m1_subset_1(X2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2)) | ~v1_funct_1(sK3) | v1_xboole_0(sK2)) ) | (spl6_6 | ~spl6_7)),
% 0.21/0.49    inference(subsumption_resolution,[],[f280,f104])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    k1_xboole_0 != sK1 | spl6_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f102])).
% 0.21/0.49  fof(f280,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,X0,X1)) | ~m1_subset_1(X2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_1(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | k1_funct_1(k8_funct_2(sK1,sK2,X0,sK3,X1),X2) = k1_funct_1(X1,k1_funct_1(sK3,X2)) | ~v1_funct_1(sK3) | v1_xboole_0(sK2)) ) | ~spl6_7),
% 0.21/0.49    inference(resolution,[],[f61,f109])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    v1_funct_2(sK3,sK1,sK2) | ~spl6_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f107])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_2(X3,X1,X2) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 0.21/0.49    inference(flattening,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).
% 0.21/0.49  fof(f235,plain,(
% 0.21/0.49    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) | spl6_27),
% 0.21/0.49    inference(avatar_component_clause,[],[f233])).
% 0.21/0.49  fof(f291,plain,(
% 0.21/0.49    ~spl6_35 | ~spl6_10 | spl6_31 | spl6_32),
% 0.21/0.49    inference(avatar_split_clause,[],[f286,f266,f262,f125,f288])).
% 0.21/0.49  fof(f288,plain,(
% 0.21/0.49    spl6_35 <=> sK2 = k1_relset_1(sK2,sK0,sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 0.21/0.49  fof(f262,plain,(
% 0.21/0.49    spl6_31 <=> k1_xboole_0 = sK0),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.21/0.49  fof(f266,plain,(
% 0.21/0.49    spl6_32 <=> v1_funct_2(sK4,sK2,sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.21/0.49  fof(f286,plain,(
% 0.21/0.49    sK2 != k1_relset_1(sK2,sK0,sK4) | (~spl6_10 | spl6_31 | spl6_32)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f263,f127,f267,f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(nnf_transformation,[],[f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(flattening,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.49  fof(f267,plain,(
% 0.21/0.49    ~v1_funct_2(sK4,sK2,sK0) | spl6_32),
% 0.21/0.49    inference(avatar_component_clause,[],[f266])).
% 0.21/0.49  fof(f263,plain,(
% 0.21/0.49    k1_xboole_0 != sK0 | spl6_31),
% 0.21/0.49    inference(avatar_component_clause,[],[f262])).
% 0.21/0.49  fof(f279,plain,(
% 0.21/0.49    ~spl6_34 | spl6_31),
% 0.21/0.49    inference(avatar_split_clause,[],[f274,f262,f276])).
% 0.21/0.49  fof(f276,plain,(
% 0.21/0.49    spl6_34 <=> v1_xboole_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 0.21/0.49  fof(f274,plain,(
% 0.21/0.49    ~v1_xboole_0(sK0) | spl6_31),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f263,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.49  fof(f273,plain,(
% 0.21/0.49    spl6_31 | spl6_32 | ~spl6_33 | ~spl6_10 | ~spl6_26),
% 0.21/0.49    inference(avatar_split_clause,[],[f257,f228,f125,f270,f266,f262])).
% 0.21/0.49  fof(f270,plain,(
% 0.21/0.49    spl6_33 <=> sK2 = k1_relat_1(sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.21/0.49  fof(f257,plain,(
% 0.21/0.49    sK2 != k1_relat_1(sK4) | v1_funct_2(sK4,sK2,sK0) | k1_xboole_0 = sK0 | (~spl6_10 | ~spl6_26)),
% 0.21/0.49    inference(subsumption_resolution,[],[f256,f127])).
% 0.21/0.49  fof(f256,plain,(
% 0.21/0.49    sK2 != k1_relat_1(sK4) | v1_funct_2(sK4,sK2,sK0) | k1_xboole_0 = sK0 | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl6_26),
% 0.21/0.49    inference(superposition,[],[f67,f230])).
% 0.21/0.49  fof(f255,plain,(
% 0.21/0.49    spl6_30 | ~spl6_25 | ~spl6_29),
% 0.21/0.49    inference(avatar_split_clause,[],[f248,f244,f223,f252])).
% 0.21/0.49  fof(f223,plain,(
% 0.21/0.49    spl6_25 <=> k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.21/0.49  fof(f244,plain,(
% 0.21/0.49    spl6_29 <=> sK1 = k1_relset_1(sK1,sK2,sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.21/0.49  fof(f248,plain,(
% 0.21/0.49    sK1 = k1_relat_1(sK3) | (~spl6_25 | ~spl6_29)),
% 0.21/0.49    inference(backward_demodulation,[],[f225,f246])).
% 0.21/0.49  fof(f246,plain,(
% 0.21/0.49    sK1 = k1_relset_1(sK1,sK2,sK3) | ~spl6_29),
% 0.21/0.49    inference(avatar_component_clause,[],[f244])).
% 0.21/0.49  fof(f225,plain,(
% 0.21/0.49    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) | ~spl6_25),
% 0.21/0.49    inference(avatar_component_clause,[],[f223])).
% 0.21/0.49  fof(f247,plain,(
% 0.21/0.49    spl6_28 | spl6_29 | ~spl6_7 | ~spl6_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f238,f120,f107,f244,f240])).
% 0.21/0.49  fof(f240,plain,(
% 0.21/0.49    spl6_28 <=> k1_xboole_0 = sK2),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.21/0.49  fof(f238,plain,(
% 0.21/0.49    sK1 = k1_relset_1(sK1,sK2,sK3) | k1_xboole_0 = sK2 | (~spl6_7 | ~spl6_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f237,f122])).
% 0.21/0.49  fof(f237,plain,(
% 0.21/0.49    sK1 = k1_relset_1(sK1,sK2,sK3) | k1_xboole_0 = sK2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl6_7),
% 0.21/0.49    inference(resolution,[],[f65,f109])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f41])).
% 0.21/0.49  fof(f236,plain,(
% 0.21/0.49    ~spl6_27),
% 0.21/0.49    inference(avatar_split_clause,[],[f51,f233])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 0.21/0.49    inference(cnf_transformation,[],[f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    (((k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)) & ~v1_xboole_0(sK2)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f18,f38,f37,f36,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & ~v1_xboole_0(sK2))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,X3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,X3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,X4),X5) != k7_partfun1(sK0,X4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,X4)) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(X4)) => (? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(X5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) & v1_funct_1(sK4))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ? [X5] : (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),X5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,X5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(X5,sK1)) => (k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) & k1_xboole_0 != sK1 & r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) & m1_subset_1(sK5,sK1))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 0.21/0.49    inference(flattening,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f14])).
% 0.21/0.49  fof(f14,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).
% 0.21/0.49  fof(f231,plain,(
% 0.21/0.49    spl6_26 | ~spl6_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f200,f125,f228])).
% 0.21/0.49  fof(f200,plain,(
% 0.21/0.49    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) | ~spl6_10),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f127,f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.49  fof(f226,plain,(
% 0.21/0.49    spl6_25 | ~spl6_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f199,f120,f223])).
% 0.21/0.49  fof(f199,plain,(
% 0.21/0.49    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) | ~spl6_9),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f122,f63])).
% 0.21/0.49  fof(f221,plain,(
% 0.21/0.49    spl6_24 | ~spl6_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f165,f125,f218])).
% 0.21/0.49  fof(f218,plain,(
% 0.21/0.49    spl6_24 <=> k2_relset_1(sK2,sK0,sK4) = k2_relat_1(sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.21/0.49  fof(f165,plain,(
% 0.21/0.49    k2_relset_1(sK2,sK0,sK4) = k2_relat_1(sK4) | ~spl6_10),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f127,f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.49  fof(f215,plain,(
% 0.21/0.49    spl6_23 | ~spl6_10 | ~spl6_19),
% 0.21/0.49    inference(avatar_split_clause,[],[f204,f182,f125,f212])).
% 0.21/0.49  fof(f182,plain,(
% 0.21/0.49    spl6_19 <=> r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.21/0.49  fof(f204,plain,(
% 0.21/0.49    r1_tarski(k2_relat_1(sK3),k1_relat_1(sK4)) | (~spl6_10 | ~spl6_19)),
% 0.21/0.49    inference(backward_demodulation,[],[f184,f200])).
% 0.21/0.49  fof(f184,plain,(
% 0.21/0.49    r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4)) | ~spl6_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f182])).
% 0.21/0.49  fof(f209,plain,(
% 0.21/0.49    spl6_22 | ~spl6_10 | ~spl6_20),
% 0.21/0.49    inference(avatar_split_clause,[],[f203,f189,f125,f206])).
% 0.21/0.49  fof(f189,plain,(
% 0.21/0.49    spl6_20 <=> v5_relat_1(sK3,k1_relset_1(sK2,sK0,sK4))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.21/0.49  fof(f203,plain,(
% 0.21/0.49    v5_relat_1(sK3,k1_relat_1(sK4)) | (~spl6_10 | ~spl6_20)),
% 0.21/0.49    inference(backward_demodulation,[],[f191,f200])).
% 0.21/0.49  fof(f191,plain,(
% 0.21/0.49    v5_relat_1(sK3,k1_relset_1(sK2,sK0,sK4)) | ~spl6_20),
% 0.21/0.49    inference(avatar_component_clause,[],[f189])).
% 0.21/0.49  fof(f198,plain,(
% 0.21/0.49    spl6_21 | ~spl6_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f164,f120,f195])).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) | ~spl6_9),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f122,f62])).
% 0.21/0.49  fof(f192,plain,(
% 0.21/0.49    spl6_20 | ~spl6_11 | ~spl6_19),
% 0.21/0.49    inference(avatar_split_clause,[],[f187,f182,f132,f189])).
% 0.21/0.49  fof(f187,plain,(
% 0.21/0.49    v5_relat_1(sK3,k1_relset_1(sK2,sK0,sK4)) | (~spl6_11 | ~spl6_19)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f134,f184,f57])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.49  fof(f185,plain,(
% 0.21/0.49    spl6_19 | ~spl6_9 | ~spl6_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f167,f148,f120,f182])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    spl6_14 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    r1_tarski(k2_relat_1(sK3),k1_relset_1(sK2,sK0,sK4)) | (~spl6_9 | ~spl6_14)),
% 0.21/0.49    inference(backward_demodulation,[],[f150,f164])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) | ~spl6_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f148])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    spl6_18 | ~spl6_12 | ~spl6_16),
% 0.21/0.49    inference(avatar_split_clause,[],[f169,f160,f137,f176])).
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    spl6_18 <=> r1_tarski(k2_relat_1(sK4),sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.21/0.49  fof(f169,plain,(
% 0.21/0.49    r1_tarski(k2_relat_1(sK4),sK0) | (~spl6_12 | ~spl6_16)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f139,f162,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f40])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    spl6_17 | ~spl6_11 | ~spl6_15),
% 0.21/0.49    inference(avatar_split_clause,[],[f168,f155,f132,f171])).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    spl6_17 <=> r1_tarski(k2_relat_1(sK3),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    spl6_15 <=> v5_relat_1(sK3,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    r1_tarski(k2_relat_1(sK3),sK2) | (~spl6_11 | ~spl6_15)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f134,f157,f56])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    v5_relat_1(sK3,sK2) | ~spl6_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f155])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    spl6_16 | ~spl6_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f153,f125,f160])).
% 0.21/0.49  fof(f153,plain,(
% 0.21/0.49    v5_relat_1(sK4,sK0) | ~spl6_10),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f127,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.49  fof(f158,plain,(
% 0.21/0.49    spl6_15 | ~spl6_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f152,f120,f155])).
% 0.21/0.49  fof(f152,plain,(
% 0.21/0.49    v5_relat_1(sK3,sK2) | ~spl6_9),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f122,f64])).
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    spl6_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f49,f148])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 0.21/0.49    inference(cnf_transformation,[],[f39])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    spl6_13 | ~spl6_5 | spl6_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f141,f115,f97,f143])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    spl6_8 <=> v1_xboole_0(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    r2_hidden(sK5,sK1) | (~spl6_5 | spl6_8)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f99,f117,f58])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    ~v1_xboole_0(sK1) | spl6_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f115])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    spl6_12 | ~spl6_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f130,f125,f137])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    v1_relat_1(sK4) | ~spl6_10),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f55,f127,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    spl6_11 | ~spl6_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f129,f120,f132])).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    v1_relat_1(sK3) | ~spl6_9),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f55,f122,f53])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    spl6_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f47,f125])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f39])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    spl6_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f45,f120])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.49    inference(cnf_transformation,[],[f39])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    ~spl6_8 | spl6_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f112,f102,f115])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    ~v1_xboole_0(sK1) | spl6_6),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f104,f54])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    spl6_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f44,f107])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    v1_funct_2(sK3,sK1,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f39])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    ~spl6_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f50,f102])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    k1_xboole_0 != sK1),
% 0.21/0.49    inference(cnf_transformation,[],[f39])).
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    spl6_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f48,f97])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    m1_subset_1(sK5,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f39])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    spl6_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f52,f92])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    spl6_4 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    spl6_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f46,f87])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    v1_funct_1(sK4)),
% 0.21/0.49    inference(cnf_transformation,[],[f39])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    spl6_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f43,f82])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    v1_funct_1(sK3)),
% 0.21/0.49    inference(cnf_transformation,[],[f39])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ~spl6_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f42,f77])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ~v1_xboole_0(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f39])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (20769)------------------------------
% 0.21/0.49  % (20769)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (20769)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (20769)Memory used [KB]: 1791
% 0.21/0.49  % (20769)Time elapsed: 0.081 s
% 0.21/0.49  % (20769)------------------------------
% 0.21/0.49  % (20769)------------------------------
% 0.21/0.49  % (20761)Success in time 0.134 s
%------------------------------------------------------------------------------
