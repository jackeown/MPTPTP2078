%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t20_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:41 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 278 expanded)
%              Number of leaves         :   32 ( 111 expanded)
%              Depth                    :   11
%              Number of atoms          :  431 (1020 expanded)
%              Number of equality atoms :   98 ( 283 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1412,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f107,f111,f115,f123,f127,f131,f135,f160,f183,f187,f196,f200,f204,f208,f222,f788,f964,f986,f1091,f1410,f1411])).

fof(f1411,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) != k2_relat_1(k5_relat_1(sK3,sK4))
    | k2_relat_1(k5_relat_1(sK3,sK4)) != sK2
    | k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
    introduced(theory_axiom,[])).

fof(f1410,plain,
    ( spl6_336
    | ~ spl6_162 ),
    inference(avatar_split_clause,[],[f892,f786,f1408])).

fof(f1408,plain,
    ( spl6_336
  <=> k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_336])])).

fof(f786,plain,
    ( spl6_162
  <=> m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_162])])).

fof(f892,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4))
    | ~ spl6_162 ),
    inference(resolution,[],[f787,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t20_funct_2.p',redefinition_k2_relset_1)).

fof(f787,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_162 ),
    inference(avatar_component_clause,[],[f786])).

fof(f1091,plain,
    ( ~ spl6_221
    | spl6_23
    | ~ spl6_186 ),
    inference(avatar_split_clause,[],[f974,f962,f185,f1089])).

fof(f1089,plain,
    ( spl6_221
  <=> k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_221])])).

fof(f185,plain,
    ( spl6_23
  <=> k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f962,plain,
    ( spl6_186
  <=> k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_186])])).

fof(f974,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) != sK2
    | ~ spl6_23
    | ~ spl6_186 ),
    inference(superposition,[],[f186,f963])).

fof(f963,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl6_186 ),
    inference(avatar_component_clause,[],[f962])).

fof(f186,plain,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) != sK2
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f185])).

fof(f986,plain,
    ( spl6_188
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_26
    | ~ spl6_30
    | ~ spl6_32
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f982,f220,f206,f202,f194,f181,f158,f984])).

fof(f984,plain,
    ( spl6_188
  <=> k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_188])])).

fof(f158,plain,
    ( spl6_18
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f181,plain,
    ( spl6_20
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f194,plain,
    ( spl6_26
  <=> k2_relat_1(sK4) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f202,plain,
    ( spl6_30
  <=> k1_relat_1(sK4) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f206,plain,
    ( spl6_32
  <=> k2_relat_1(sK3) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f220,plain,
    ( spl6_36
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f982,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2
    | ~ spl6_18
    | ~ spl6_20
    | ~ spl6_26
    | ~ spl6_30
    | ~ spl6_32
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f981,f182])).

fof(f182,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f181])).

fof(f981,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2
    | ~ v1_relat_1(sK3)
    | ~ spl6_18
    | ~ spl6_26
    | ~ spl6_30
    | ~ spl6_32
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f979,f221])).

fof(f221,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f220])).

fof(f979,plain,
    ( ~ r1_tarski(sK1,sK1)
    | k2_relat_1(k5_relat_1(sK3,sK4)) = sK2
    | ~ v1_relat_1(sK3)
    | ~ spl6_18
    | ~ spl6_26
    | ~ spl6_30
    | ~ spl6_32 ),
    inference(superposition,[],[f225,f207])).

fof(f207,plain,
    ( k2_relat_1(sK3) = sK1
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f206])).

fof(f225,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,k2_relat_1(X0))
        | k2_relat_1(k5_relat_1(X0,sK4)) = sK2
        | ~ v1_relat_1(X0) )
    | ~ spl6_18
    | ~ spl6_26
    | ~ spl6_30 ),
    inference(forward_demodulation,[],[f224,f195])).

fof(f195,plain,
    ( k2_relat_1(sK4) = sK2
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f194])).

fof(f224,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,k2_relat_1(X0))
        | ~ v1_relat_1(X0)
        | k2_relat_1(sK4) = k2_relat_1(k5_relat_1(X0,sK4)) )
    | ~ spl6_18
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f223,f159])).

fof(f159,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f158])).

fof(f223,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,k2_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK4)
        | k2_relat_1(sK4) = k2_relat_1(k5_relat_1(X0,sK4)) )
    | ~ spl6_30 ),
    inference(superposition,[],[f86,f203])).

fof(f203,plain,
    ( k1_relat_1(sK4) = sK1
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f202])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t20_funct_2.p',t47_relat_1)).

fof(f964,plain,
    ( spl6_186
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f513,f133,f121,f105,f101,f962])).

fof(f101,plain,
    ( spl6_0
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f105,plain,
    ( spl6_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f121,plain,
    ( spl6_10
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f133,plain,
    ( spl6_16
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f513,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f510,f102])).

fof(f102,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f101])).

fof(f510,plain,
    ( ~ v1_funct_1(sK4)
    | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl6_2
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(resolution,[],[f176,f122])).

fof(f122,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f121])).

fof(f176,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ v1_funct_1(X6)
        | k1_partfun1(sK0,sK1,X7,X8,sK3,X6) = k5_relat_1(sK3,X6) )
    | ~ spl6_2
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f164,f106])).

fof(f106,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f105])).

fof(f164,plain,
    ( ! [X6,X8,X7] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | k1_partfun1(sK0,sK1,X7,X8,sK3,X6) = k5_relat_1(sK3,X6) )
    | ~ spl6_16 ),
    inference(resolution,[],[f134,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t20_funct_2.p',redefinition_k1_partfun1)).

fof(f134,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f133])).

fof(f788,plain,
    ( spl6_162
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f527,f133,f121,f105,f101,f786])).

fof(f527,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(forward_demodulation,[],[f526,f513])).

fof(f526,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f522,f102])).

fof(f522,plain,
    ( ~ v1_funct_1(sK4)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_2
    | ~ spl6_10
    | ~ spl6_16 ),
    inference(resolution,[],[f175,f122])).

fof(f175,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X3)
        | m1_subset_1(k1_partfun1(sK0,sK1,X4,X5,sK3,X3),k1_zfmisc_1(k2_zfmisc_1(sK0,X5))) )
    | ~ spl6_2
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f163,f106])).

fof(f163,plain,
    ( ! [X4,X5,X3] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | m1_subset_1(k1_partfun1(sK0,sK1,X4,X5,sK3,X3),k1_zfmisc_1(k2_zfmisc_1(sK0,X5))) )
    | ~ spl6_16 ),
    inference(resolution,[],[f134,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t20_funct_2.p',dt_k1_partfun1)).

fof(f222,plain,
    ( spl6_36
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f217,f198,f220])).

fof(f198,plain,
    ( spl6_28
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f217,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl6_28 ),
    inference(resolution,[],[f199,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t20_funct_2.p',t3_subset)).

fof(f199,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f198])).

fof(f208,plain,
    ( spl6_32
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f179,f133,f125,f206])).

fof(f125,plain,
    ( spl6_12
  <=> k2_relset_1(sK0,sK1,sK3) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f179,plain,
    ( k2_relat_1(sK3) = sK1
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(forward_demodulation,[],[f168,f126])).

fof(f126,plain,
    ( k2_relset_1(sK0,sK1,sK3) = sK1
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f125])).

fof(f168,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl6_16 ),
    inference(resolution,[],[f134,f81])).

fof(f204,plain,
    ( spl6_30
    | spl6_5
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f156,f121,f113,f109,f202])).

fof(f109,plain,
    ( spl6_5
  <=> k1_xboole_0 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f113,plain,
    ( spl6_6
  <=> v1_funct_2(sK4,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f156,plain,
    ( k1_relat_1(sK4) = sK1
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f144,f152])).

fof(f152,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f151,f114])).

fof(f114,plain,
    ( v1_funct_2(sK4,sK1,sK2)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f113])).

fof(f151,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | ~ v1_funct_2(sK4,sK1,sK2)
    | ~ spl6_5
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f140,f110])).

fof(f110,plain,
    ( k1_xboole_0 != sK2
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f109])).

fof(f140,plain,
    ( k1_xboole_0 = sK2
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | ~ v1_funct_2(sK4,sK1,sK2)
    | ~ spl6_10 ),
    inference(resolution,[],[f122,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/funct_2__t20_funct_2.p',d1_funct_2)).

fof(f144,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4)
    | ~ spl6_10 ),
    inference(resolution,[],[f122,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t20_funct_2.p',redefinition_k1_relset_1)).

fof(f200,plain,
    ( spl6_28
    | spl6_5
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f155,f121,f113,f109,f198])).

fof(f155,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f143,f152])).

fof(f143,plain,
    ( m1_subset_1(k1_relset_1(sK1,sK2,sK4),k1_zfmisc_1(sK1))
    | ~ spl6_10 ),
    inference(resolution,[],[f122,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t20_funct_2.p',dt_k1_relset_1)).

fof(f196,plain,
    ( spl6_26
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f154,f129,f121,f194])).

fof(f129,plain,
    ( spl6_14
  <=> k2_relset_1(sK1,sK2,sK4) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f154,plain,
    ( k2_relat_1(sK4) = sK2
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(forward_demodulation,[],[f142,f130])).

fof(f130,plain,
    ( k2_relset_1(sK1,sK2,sK4) = sK2
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f129])).

fof(f142,plain,
    ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4)
    | ~ spl6_10 ),
    inference(resolution,[],[f122,f81])).

fof(f187,plain,(
    ~ spl6_23 ),
    inference(avatar_split_clause,[],[f65,f185])).

fof(f65,plain,(
    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) != sK2 ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
          & k1_xboole_0 != X2
          & k2_relset_1(X1,X2,X4) = X2
          & k2_relset_1(X0,X1,X3) = X1
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
          & k1_xboole_0 != X2
          & k2_relset_1(X1,X2,X4) = X2
          & k2_relset_1(X0,X1,X3) = X1
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2)
              & v1_funct_1(X4) )
           => ( ( k2_relset_1(X1,X2,X4) = X2
                & k2_relset_1(X0,X1,X3) = X1 )
             => ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
                | k1_xboole_0 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X1,X2,X4) = X2
              & k2_relset_1(X0,X1,X3) = X1 )
           => ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
              | k1_xboole_0 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t20_funct_2.p',t20_funct_2)).

fof(f183,plain,
    ( spl6_20
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f171,f133,f181])).

fof(f171,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_16 ),
    inference(resolution,[],[f134,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t20_funct_2.p',cc1_relset_1)).

fof(f160,plain,
    ( spl6_18
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f145,f121,f158])).

fof(f145,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_10 ),
    inference(resolution,[],[f122,f93])).

fof(f135,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f68,f133])).

fof(f68,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f131,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f63,f129])).

fof(f63,plain,(
    k2_relset_1(sK1,sK2,sK4) = sK2 ),
    inference(cnf_transformation,[],[f32])).

fof(f127,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f62,f125])).

fof(f62,plain,(
    k2_relset_1(sK0,sK1,sK3) = sK1 ),
    inference(cnf_transformation,[],[f32])).

fof(f123,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f61,f121])).

fof(f61,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f115,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f60,f113])).

fof(f60,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f111,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f64,f109])).

fof(f64,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f32])).

fof(f107,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f66,f105])).

fof(f66,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f103,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f59,f101])).

fof(f59,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
