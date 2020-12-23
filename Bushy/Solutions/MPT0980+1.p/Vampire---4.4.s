%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t26_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:42 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 277 expanded)
%              Number of leaves         :   33 ( 113 expanded)
%              Depth                    :   13
%              Number of atoms          :  510 (1037 expanded)
%              Number of equality atoms :   72 ( 170 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2344,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f106,f110,f114,f125,f129,f133,f174,f178,f182,f192,f262,f319,f332,f337,f341,f402,f1252,f1331,f1333,f2152,f2340,f2343])).

fof(f2343,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) != k5_relat_1(sK3,sK4)
    | v2_funct_1(k5_relat_1(sK3,sK4))
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    introduced(theory_axiom,[])).

fof(f2340,plain,
    ( ~ spl6_0
    | spl6_3
    | ~ spl6_4
    | ~ spl6_18
    | ~ spl6_22
    | ~ spl6_26
    | ~ spl6_58
    | ~ spl6_270 ),
    inference(avatar_contradiction_clause,[],[f2339])).

fof(f2339,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_18
    | ~ spl6_22
    | ~ spl6_26
    | ~ spl6_58
    | ~ spl6_270 ),
    inference(subsumption_resolution,[],[f2338,f105])).

fof(f105,plain,
    ( ~ v2_funct_1(sK3)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl6_3
  <=> ~ v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f2338,plain,
    ( v2_funct_1(sK3)
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_18
    | ~ spl6_22
    | ~ spl6_26
    | ~ spl6_58
    | ~ spl6_270 ),
    inference(subsumption_resolution,[],[f2337,f1631])).

fof(f1631,plain,
    ( v2_funct_1(k5_relat_1(sK3,sK4))
    | ~ spl6_270 ),
    inference(avatar_component_clause,[],[f1630])).

fof(f1630,plain,
    ( spl6_270
  <=> v2_funct_1(k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_270])])).

fof(f2337,plain,
    ( ~ v2_funct_1(k5_relat_1(sK3,sK4))
    | v2_funct_1(sK3)
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_18
    | ~ spl6_22
    | ~ spl6_26
    | ~ spl6_58 ),
    inference(subsumption_resolution,[],[f2336,f109])).

fof(f109,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl6_4
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f2336,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK3,sK4))
    | v2_funct_1(sK3)
    | ~ spl6_0
    | ~ spl6_18
    | ~ spl6_22
    | ~ spl6_26
    | ~ spl6_58 ),
    inference(subsumption_resolution,[],[f2335,f181])).

fof(f181,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl6_22
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f2335,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK3,sK4))
    | v2_funct_1(sK3)
    | ~ spl6_0
    | ~ spl6_18
    | ~ spl6_26
    | ~ spl6_58 ),
    inference(resolution,[],[f1411,f331])).

fof(f331,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ spl6_58 ),
    inference(avatar_component_clause,[],[f330])).

fof(f330,plain,
    ( spl6_58
  <=> r1_tarski(k2_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f1411,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(X0),sK1)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(k5_relat_1(X0,sK4))
        | v2_funct_1(X0) )
    | ~ spl6_0
    | ~ spl6_18
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f1410,f173])).

fof(f173,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl6_18
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f1410,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(X0),sK1)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(k5_relat_1(X0,sK4))
        | ~ v1_relat_1(sK4)
        | v2_funct_1(X0) )
    | ~ spl6_0
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f1409,f101])).

fof(f101,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl6_0
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f1409,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(X0),sK1)
        | ~ v1_funct_1(sK4)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(k5_relat_1(X0,sK4))
        | ~ v1_relat_1(sK4)
        | v2_funct_1(X0) )
    | ~ spl6_26 ),
    inference(superposition,[],[f76,f191])).

fof(f191,plain,
    ( k1_relat_1(sK4) = sK1
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl6_26
  <=> k1_relat_1(sK4) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0)
      | v2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => v2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t26_funct_2.p',t47_funct_1)).

fof(f2152,plain,
    ( spl6_402
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f570,f131,f127,f108,f100,f2150])).

fof(f2150,plain,
    ( spl6_402
  <=> k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_402])])).

fof(f127,plain,
    ( spl6_14
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f131,plain,
    ( spl6_16
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f570,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f563,f101])).

fof(f563,plain,
    ( ~ v1_funct_1(sK4)
    | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl6_4
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(resolution,[],[f169,f128])).

fof(f128,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f127])).

fof(f169,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ v1_funct_1(X6)
        | k1_partfun1(sK0,sK1,X7,X8,sK3,X6) = k5_relat_1(sK3,X6) )
    | ~ spl6_4
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f158,f109])).

fof(f158,plain,
    ( ! [X6,X8,X7] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | k1_partfun1(sK0,sK1,X7,X8,sK3,X6) = k5_relat_1(sK3,X6) )
    | ~ spl6_16 ),
    inference(resolution,[],[f132,f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    file('/export/starexec/sandbox2/benchmark/funct_2__t26_funct_2.p',redefinition_k1_partfun1)).

fof(f132,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f131])).

fof(f1333,plain,
    ( spl6_30
    | ~ spl6_54
    | ~ spl6_60
    | ~ spl6_288 ),
    inference(avatar_split_clause,[],[f1332,f1329,f335,f317,f206])).

fof(f206,plain,
    ( spl6_30
  <=> k1_xboole_0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f317,plain,
    ( spl6_54
  <=> v1_funct_2(sK4,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f335,plain,
    ( spl6_60
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f1329,plain,
    ( spl6_288
  <=> k1_relset_1(k1_xboole_0,sK2,sK4) = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_288])])).

fof(f1332,plain,
    ( k1_xboole_0 = k1_relat_1(sK4)
    | ~ spl6_54
    | ~ spl6_60
    | ~ spl6_288 ),
    inference(forward_demodulation,[],[f1330,f1286])).

fof(f1286,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,sK4)
    | ~ spl6_54
    | ~ spl6_60 ),
    inference(subsumption_resolution,[],[f366,f318])).

fof(f318,plain,
    ( v1_funct_2(sK4,k1_xboole_0,sK2)
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f317])).

fof(f366,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,sK2,sK4)
    | ~ v1_funct_2(sK4,k1_xboole_0,sK2)
    | ~ spl6_60 ),
    inference(resolution,[],[f336,f94])).

fof(f94,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

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
    file('/export/starexec/sandbox2/benchmark/funct_2__t26_funct_2.p',d1_funct_2)).

fof(f336,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ spl6_60 ),
    inference(avatar_component_clause,[],[f335])).

fof(f1330,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_relat_1(sK4)
    | ~ spl6_288 ),
    inference(avatar_component_clause,[],[f1329])).

fof(f1331,plain,
    ( spl6_288
    | ~ spl6_10
    | ~ spl6_72 ),
    inference(avatar_split_clause,[],[f1281,f400,f120,f1329])).

fof(f120,plain,
    ( spl6_10
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f400,plain,
    ( spl6_72
  <=> k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).

fof(f1281,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_relat_1(sK4)
    | ~ spl6_10
    | ~ spl6_72 ),
    inference(forward_demodulation,[],[f401,f121])).

fof(f121,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f120])).

fof(f401,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4)
    | ~ spl6_72 ),
    inference(avatar_component_clause,[],[f400])).

fof(f1252,plain,
    ( ~ spl6_271
    | ~ spl6_0
    | spl6_3
    | ~ spl6_4
    | ~ spl6_18
    | ~ spl6_22
    | ~ spl6_30
    | ~ spl6_62 ),
    inference(avatar_split_clause,[],[f1151,f339,f206,f180,f172,f108,f104,f100,f1250])).

fof(f1250,plain,
    ( spl6_271
  <=> ~ v2_funct_1(k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_271])])).

fof(f339,plain,
    ( spl6_62
  <=> r1_tarski(k2_relat_1(sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f1151,plain,
    ( ~ v2_funct_1(k5_relat_1(sK3,sK4))
    | ~ spl6_0
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_18
    | ~ spl6_22
    | ~ spl6_30
    | ~ spl6_62 ),
    inference(subsumption_resolution,[],[f1150,f105])).

fof(f1150,plain,
    ( ~ v2_funct_1(k5_relat_1(sK3,sK4))
    | v2_funct_1(sK3)
    | ~ spl6_0
    | ~ spl6_4
    | ~ spl6_18
    | ~ spl6_22
    | ~ spl6_30
    | ~ spl6_62 ),
    inference(subsumption_resolution,[],[f1149,f109])).

fof(f1149,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK3,sK4))
    | v2_funct_1(sK3)
    | ~ spl6_0
    | ~ spl6_18
    | ~ spl6_22
    | ~ spl6_30
    | ~ spl6_62 ),
    inference(subsumption_resolution,[],[f1147,f181])).

fof(f1147,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK3,sK4))
    | v2_funct_1(sK3)
    | ~ spl6_0
    | ~ spl6_18
    | ~ spl6_30
    | ~ spl6_62 ),
    inference(resolution,[],[f324,f340])).

fof(f340,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | ~ spl6_62 ),
    inference(avatar_component_clause,[],[f339])).

fof(f324,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(k5_relat_1(X0,sK4))
        | v2_funct_1(X0) )
    | ~ spl6_0
    | ~ spl6_18
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f323,f173])).

fof(f323,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(k5_relat_1(X0,sK4))
        | ~ v1_relat_1(sK4)
        | v2_funct_1(X0) )
    | ~ spl6_0
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f322,f101])).

fof(f322,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(X0),k1_xboole_0)
        | ~ v1_funct_1(sK4)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(k5_relat_1(X0,sK4))
        | ~ v1_relat_1(sK4)
        | v2_funct_1(X0) )
    | ~ spl6_30 ),
    inference(superposition,[],[f76,f207])).

fof(f207,plain,
    ( k1_xboole_0 = k1_relat_1(sK4)
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f206])).

fof(f402,plain,
    ( spl6_72
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f140,f127,f400])).

fof(f140,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4)
    | ~ spl6_14 ),
    inference(resolution,[],[f128,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t26_funct_2.p',redefinition_k1_relset_1)).

fof(f341,plain,
    ( spl6_62
    | ~ spl6_10
    | ~ spl6_58 ),
    inference(avatar_split_clause,[],[f333,f330,f120,f339])).

fof(f333,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | ~ spl6_10
    | ~ spl6_58 ),
    inference(forward_demodulation,[],[f331,f121])).

fof(f337,plain,
    ( spl6_60
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f280,f127,f120,f335])).

fof(f280,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(superposition,[],[f128,f121])).

fof(f332,plain,
    ( spl6_58
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f269,f260,f330])).

fof(f260,plain,
    ( spl6_42
  <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f269,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ spl6_42 ),
    inference(resolution,[],[f261,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
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
    file('/export/starexec/sandbox2/benchmark/funct_2__t26_funct_2.p',t3_subset)).

fof(f261,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f260])).

fof(f319,plain,
    ( spl6_54
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f278,f120,f112,f317])).

fof(f112,plain,
    ( spl6_6
  <=> v1_funct_2(sK4,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f278,plain,
    ( v1_funct_2(sK4,k1_xboole_0,sK2)
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(superposition,[],[f113,f121])).

fof(f113,plain,
    ( v1_funct_2(sK4,sK1,sK2)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f262,plain,
    ( spl6_42
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f170,f131,f260])).

fof(f170,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ spl6_16 ),
    inference(forward_demodulation,[],[f163,f161])).

fof(f161,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl6_16 ),
    inference(resolution,[],[f132,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t26_funct_2.p',redefinition_k2_relset_1)).

fof(f163,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1))
    | ~ spl6_16 ),
    inference(resolution,[],[f132,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t26_funct_2.p',dt_k2_relset_1)).

fof(f192,plain,
    ( spl6_26
    | ~ spl6_6
    | spl6_13
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f152,f127,f123,f112,f190])).

fof(f123,plain,
    ( spl6_13
  <=> k1_xboole_0 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f152,plain,
    ( k1_relat_1(sK4) = sK1
    | ~ spl6_6
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(forward_demodulation,[],[f140,f147])).

fof(f147,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | ~ spl6_6
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f146,f113])).

fof(f146,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | ~ v1_funct_2(sK4,sK1,sK2)
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f135,f124])).

fof(f124,plain,
    ( k1_xboole_0 != sK2
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f123])).

fof(f135,plain,
    ( k1_xboole_0 = sK2
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | ~ v1_funct_2(sK4,sK1,sK2)
    | ~ spl6_14 ),
    inference(resolution,[],[f128,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f182,plain,
    ( spl6_22
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f162,f131,f180])).

fof(f162,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_16 ),
    inference(resolution,[],[f132,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t26_funct_2.p',cc1_relset_1)).

fof(f178,plain,(
    spl6_20 ),
    inference(avatar_split_clause,[],[f63,f176])).

fof(f176,plain,
    ( spl6_20
  <=> v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f63,plain,(
    v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ v2_funct_1(X3)
          & ( k1_xboole_0 = X1
            | k1_xboole_0 != X2 )
          & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
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
          ( ~ v2_funct_1(X3)
          & ( k1_xboole_0 = X1
            | k1_xboole_0 != X2 )
          & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
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
           => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
             => ( v2_funct_1(X3)
                | ( k1_xboole_0 != X1
                  & k1_xboole_0 = X2 ) ) ) ) ) ),
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
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t26_funct_2.p',t26_funct_2)).

fof(f174,plain,
    ( spl6_18
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f142,f127,f172])).

fof(f142,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_14 ),
    inference(resolution,[],[f128,f90])).

fof(f133,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f67,f131])).

fof(f67,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f129,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f62,f127])).

fof(f62,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f125,plain,
    ( spl6_10
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f59,f123,f120])).

fof(f59,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f32])).

fof(f114,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f61,f112])).

fof(f61,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f110,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f65,f108])).

fof(f65,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f106,plain,(
    ~ spl6_3 ),
    inference(avatar_split_clause,[],[f64,f104])).

fof(f64,plain,(
    ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f102,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f60,f100])).

fof(f60,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
