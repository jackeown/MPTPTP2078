%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t161_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:34 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 225 expanded)
%              Number of leaves         :   21 (  86 expanded)
%              Depth                    :   19
%              Number of atoms          :  354 ( 728 expanded)
%              Number of equality atoms :   47 ( 123 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f215,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f76,f83,f90,f104,f113,f128,f141,f152,f185,f187,f202,f204,f210,f214])).

fof(f214,plain,
    ( spl4_11
    | ~ spl4_22 ),
    inference(avatar_contradiction_clause,[],[f213])).

fof(f213,plain,
    ( $false
    | ~ spl4_11
    | ~ spl4_22 ),
    inference(subsumption_resolution,[],[f212,f103])).

fof(f103,plain,
    ( k1_xboole_0 != sK1
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl4_11
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f212,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_22 ),
    inference(resolution,[],[f184,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t161_funct_2.p',t6_boole)).

fof(f184,plain,
    ( v1_xboole_0(sK1)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl4_22
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f210,plain,
    ( spl4_22
    | spl4_14
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_12
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f209,f139,f111,f88,f81,f120,f183])).

fof(f120,plain,
    ( spl4_14
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f81,plain,
    ( spl4_4
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f88,plain,
    ( spl4_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f111,plain,
    ( spl4_12
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f139,plain,
    ( spl4_18
  <=> k3_partfun1(sK2,sK0,sK1) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f209,plain,
    ( v1_partfun1(sK2,sK0)
    | v1_xboole_0(sK1)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_12
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f208,f112])).

fof(f112,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f111])).

fof(f208,plain,
    ( ~ v1_relat_1(sK2)
    | v1_partfun1(sK2,sK0)
    | v1_xboole_0(sK1)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_12
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f207,f140])).

fof(f140,plain,
    ( k3_partfun1(sK2,sK0,sK1) = sK2
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f139])).

fof(f207,plain,
    ( v1_partfun1(sK2,sK0)
    | v1_xboole_0(sK1)
    | ~ v1_relat_1(k3_partfun1(sK2,sK0,sK1))
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_12
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f206,f140])).

fof(f206,plain,
    ( v1_xboole_0(sK1)
    | v1_partfun1(k3_partfun1(sK2,sK0,sK1),sK0)
    | ~ v1_relat_1(k3_partfun1(sK2,sK0,sK1))
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_12
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f205,f89])).

fof(f89,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f205,plain,
    ( ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1)
    | v1_partfun1(k3_partfun1(sK2,sK0,sK1),sK0)
    | ~ v1_relat_1(k3_partfun1(sK2,sK0,sK1))
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_12
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f189,f140])).

fof(f189,plain,
    ( ~ v1_funct_1(k3_partfun1(sK2,sK0,sK1))
    | v1_xboole_0(sK1)
    | v1_partfun1(k3_partfun1(sK2,sK0,sK1),sK0)
    | ~ v1_relat_1(k3_partfun1(sK2,sK0,sK1))
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_12
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f188,f82])).

fof(f82,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f188,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(k3_partfun1(sK2,sK0,sK1))
    | v1_xboole_0(sK1)
    | v1_partfun1(k3_partfun1(sK2,sK0,sK1),sK0)
    | ~ v1_relat_1(k3_partfun1(sK2,sK0,sK1))
    | ~ spl4_6
    | ~ spl4_12
    | ~ spl4_18 ),
    inference(superposition,[],[f175,f140])).

fof(f175,plain,
    ( ! [X6,X5] :
        ( ~ v1_funct_2(k3_partfun1(sK2,X6,X5),X6,X5)
        | ~ v1_funct_1(k3_partfun1(sK2,X6,X5))
        | v1_xboole_0(X5)
        | v1_partfun1(k3_partfun1(sK2,X6,X5),X6)
        | ~ v1_relat_1(k3_partfun1(sK2,X6,X5)) )
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(duplicate_literal_removal,[],[f174])).

fof(f174,plain,
    ( ! [X6,X5] :
        ( v1_xboole_0(X5)
        | ~ v1_funct_1(k3_partfun1(sK2,X6,X5))
        | ~ v1_funct_2(k3_partfun1(sK2,X6,X5),X6,X5)
        | v1_partfun1(k3_partfun1(sK2,X6,X5),X6)
        | ~ v1_funct_1(k3_partfun1(sK2,X6,X5))
        | ~ v1_relat_1(k3_partfun1(sK2,X6,X5)) )
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(resolution,[],[f60,f163])).

fof(f163,plain,
    ( ! [X4,X5] :
        ( m1_subset_1(k3_partfun1(sK2,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(k3_partfun1(sK2,X4,X5))
        | ~ v1_relat_1(k3_partfun1(sK2,X4,X5)) )
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(superposition,[],[f56,f158])).

fof(f158,plain,
    ( ! [X0,X1] : k3_partfun1(sK2,X0,X1) = k3_partfun1(k3_partfun1(sK2,X0,X1),X0,X1)
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f155,f89])).

fof(f155,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(sK2)
        | k3_partfun1(sK2,X0,X1) = k3_partfun1(k3_partfun1(sK2,X0,X1),X0,X1) )
    | ~ spl4_12 ),
    inference(resolution,[],[f142,f112])).

fof(f142,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k3_partfun1(X2,X3,X4) = k3_partfun1(k3_partfun1(X2,X3,X4),X3,X4) ) ),
    inference(subsumption_resolution,[],[f133,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k3_partfun1(X0,X1,X2))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k3_partfun1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(k3_partfun1(X0,X1,X2)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k3_partfun1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(k3_partfun1(X0,X1,X2)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(k3_partfun1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(k3_partfun1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t161_funct_2.p',dt_k3_partfun1)).

fof(f133,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_funct_1(k3_partfun1(X2,X3,X4))
      | k3_partfun1(X2,X3,X4) = k3_partfun1(k3_partfun1(X2,X3,X4),X3,X4)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f54,f56])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k3_partfun1(X2,X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k3_partfun1(X2,X0,X1) = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t161_funct_2.p',t87_partfun1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_partfun1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t161_funct_2.p',cc5_funct_2)).

fof(f204,plain,
    ( ~ spl4_15
    | ~ spl4_2
    | ~ spl4_6
    | spl4_21 ),
    inference(avatar_split_clause,[],[f200,f150,f88,f74,f117])).

fof(f117,plain,
    ( spl4_15
  <=> ~ v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f74,plain,
    ( spl4_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f150,plain,
    ( spl4_21
  <=> k5_partfun1(sK0,sK1,sK2) != k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f200,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f199,f151])).

fof(f151,plain,
    ( k5_partfun1(sK0,sK1,sK2) != k1_tarski(sK2)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f150])).

fof(f199,plain,
    ( k5_partfun1(sK0,sK1,sK2) = k1_tarski(sK2)
    | ~ v1_partfun1(sK2,sK0)
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f194,f89])).

fof(f194,plain,
    ( ~ v1_funct_1(sK2)
    | k5_partfun1(sK0,sK1,sK2) = k1_tarski(sK2)
    | ~ v1_partfun1(sK2,sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f53,f75])).

fof(f75,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | k5_partfun1(X0,X1,X2) = k1_tarski(X2)
      | ~ v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v1_partfun1(X2,X0)
      <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v1_partfun1(X2,X0)
      <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( v1_partfun1(X2,X0)
      <=> k5_partfun1(X0,X1,X2) = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t161_funct_2.p',t174_partfun1)).

fof(f202,plain,
    ( ~ spl4_2
    | ~ spl4_6
    | ~ spl4_14
    | spl4_21 ),
    inference(avatar_contradiction_clause,[],[f201])).

fof(f201,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_14
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f200,f121])).

fof(f121,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f120])).

fof(f187,plain,
    ( spl4_14
    | spl4_22
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f177,f88,f81,f74,f183,f120])).

fof(f177,plain,
    ( v1_xboole_0(sK1)
    | v1_partfun1(sK2,sK0)
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f176,f82])).

fof(f176,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | v1_partfun1(sK2,sK0)
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f171,f89])).

fof(f171,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | v1_partfun1(sK2,sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f60,f75])).

fof(f185,plain,
    ( spl4_22
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | spl4_15 ),
    inference(avatar_split_clause,[],[f178,f117,f88,f81,f74,f183])).

fof(f178,plain,
    ( v1_xboole_0(sK1)
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f177,f118])).

fof(f118,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f117])).

fof(f152,plain,
    ( ~ spl4_21
    | spl4_1
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f143,f139,f67,f150])).

fof(f67,plain,
    ( spl4_1
  <=> k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1)) != k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f143,plain,
    ( k5_partfun1(sK0,sK1,sK2) != k1_tarski(sK2)
    | ~ spl4_1
    | ~ spl4_18 ),
    inference(backward_demodulation,[],[f140,f68])).

fof(f68,plain,
    ( k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1)) != k1_tarski(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f141,plain,
    ( spl4_18
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f134,f88,f74,f139])).

fof(f134,plain,
    ( k3_partfun1(sK2,sK0,sK1) = sK2
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f131,f89])).

fof(f131,plain,
    ( ~ v1_funct_1(sK2)
    | k3_partfun1(sK2,sK0,sK1) = sK2
    | ~ spl4_2 ),
    inference(resolution,[],[f54,f75])).

fof(f128,plain,
    ( spl4_14
    | ~ spl4_17
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f114,f74,f126,f120])).

fof(f126,plain,
    ( spl4_17
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f114,plain,
    ( ~ v1_xboole_0(sK0)
    | v1_partfun1(sK2,sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f61,f75])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t161_funct_2.p',cc1_partfun1)).

fof(f113,plain,
    ( spl4_12
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f105,f74,f111])).

fof(f105,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f62,f75])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t161_funct_2.p',cc1_relset_1)).

fof(f104,plain,
    ( spl4_8
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f91,f102,f96])).

fof(f96,plain,
    ( spl4_8
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f91,plain,
    ( k1_xboole_0 != sK1
    | sK0 = sK1 ),
    inference(inner_rewriting,[],[f47])).

fof(f47,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) != k1_tarski(X2)
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) != k1_tarski(X2)
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t161_funct_2.p',t161_funct_2)).

fof(f90,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f48,f88])).

fof(f48,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f83,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f49,f81])).

fof(f49,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f76,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f50,f74])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f69,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f51,f67])).

fof(f51,plain,(
    k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1)) != k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
