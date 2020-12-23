%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t76_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:49 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  511 (1509 expanded)
%              Number of leaves         :  125 ( 655 expanded)
%              Depth                    :   11
%              Number of atoms          : 1712 (4582 expanded)
%              Number of equality atoms :  229 ( 542 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1241,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f108,f115,f122,f129,f136,f143,f150,f157,f168,f175,f186,f193,f204,f205,f219,f226,f240,f247,f261,f268,f281,f290,f298,f306,f328,f330,f338,f373,f381,f389,f403,f422,f435,f454,f467,f548,f556,f567,f576,f587,f608,f616,f628,f639,f683,f694,f705,f714,f745,f758,f765,f772,f780,f787,f794,f801,f808,f815,f823,f831,f845,f852,f864,f866,f867,f868,f869,f900,f908,f915,f923,f931,f938,f945,f952,f959,f966,f974,f982,f996,f1003,f1017,f1044,f1058,f1072,f1109,f1122,f1129,f1136,f1144,f1151,f1158,f1165,f1172,f1179,f1187,f1195,f1209,f1216,f1228,f1230,f1231,f1232,f1233,f1240])).

fof(f1240,plain,
    ( ~ spl5_4
    | ~ spl5_8
    | ~ spl5_22
    | ~ spl5_44
    | ~ spl5_142
    | ~ spl5_178 ),
    inference(avatar_contradiction_clause,[],[f1239])).

fof(f1239,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_8
    | ~ spl5_22
    | ~ spl5_44
    | ~ spl5_142
    | ~ spl5_178 ),
    inference(subsumption_resolution,[],[f1238,f114])).

fof(f114,plain,
    ( v1_funct_1(sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl5_4
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f1238,plain,
    ( ~ v1_funct_1(sK1)
    | ~ spl5_8
    | ~ spl5_22
    | ~ spl5_44
    | ~ spl5_142
    | ~ spl5_178 ),
    inference(subsumption_resolution,[],[f1237,f185])).

fof(f185,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl5_22
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f1237,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ spl5_8
    | ~ spl5_44
    | ~ spl5_142
    | ~ spl5_178 ),
    inference(subsumption_resolution,[],[f1236,f128])).

fof(f128,plain,
    ( v2_funct_1(sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl5_8
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f1236,plain,
    ( ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ spl5_44
    | ~ spl5_142
    | ~ spl5_178 ),
    inference(subsumption_resolution,[],[f1235,f297])).

fof(f297,plain,
    ( k1_relat_1(sK1) = sK0
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f296])).

fof(f296,plain,
    ( spl5_44
  <=> k1_relat_1(sK1) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f1235,plain,
    ( k1_relat_1(sK1) != sK0
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ spl5_142
    | ~ spl5_178 ),
    inference(trivial_inequality_removal,[],[f1234])).

fof(f1234,plain,
    ( sK1 != sK1
    | k1_relat_1(sK1) != sK0
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ spl5_142
    | ~ spl5_178 ),
    inference(superposition,[],[f1071,f922])).

fof(f922,plain,
    ( k5_relat_1(sK2,sK1) = sK1
    | ~ spl5_142 ),
    inference(avatar_component_clause,[],[f921])).

fof(f921,plain,
    ( spl5_142
  <=> k5_relat_1(sK2,sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_142])])).

fof(f1071,plain,
    ( ! [X1] :
        ( k5_relat_1(sK2,X1) != X1
        | k1_relat_1(X1) != sK0
        | ~ v2_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1) )
    | ~ spl5_178 ),
    inference(avatar_component_clause,[],[f1070])).

fof(f1070,plain,
    ( spl5_178
  <=> ! [X1] :
        ( k1_relat_1(X1) != sK0
        | k5_relat_1(sK2,X1) != X1
        | ~ v2_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_178])])).

fof(f1233,plain,
    ( spl5_198
    | ~ spl5_212 ),
    inference(avatar_split_clause,[],[f1225,f1214,f1163])).

fof(f1163,plain,
    ( spl5_198
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k5_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_198])])).

fof(f1214,plain,
    ( spl5_212
  <=> r1_tarski(k5_relat_1(sK1,sK2),k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_212])])).

fof(f1225,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k5_relat_1(sK1,sK2))
    | ~ spl5_212 ),
    inference(resolution,[],[f1215,f211])).

fof(f211,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | r2_relset_1(X0,X1,X2,X2) ) ),
    inference(resolution,[],[f94,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t76_funct_2.p',t3_subset)).

fof(f94,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t76_funct_2.p',redefinition_r2_relset_1)).

fof(f1215,plain,
    ( r1_tarski(k5_relat_1(sK1,sK2),k2_zfmisc_1(sK0,sK0))
    | ~ spl5_212 ),
    inference(avatar_component_clause,[],[f1214])).

fof(f1232,plain,
    ( spl5_192
    | ~ spl5_212 ),
    inference(avatar_split_clause,[],[f1224,f1214,f1142])).

fof(f1142,plain,
    ( spl5_192
  <=> k2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2)) = k2_relat_1(k5_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_192])])).

fof(f1224,plain,
    ( k2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2)) = k2_relat_1(k5_relat_1(sK1,sK2))
    | ~ spl5_212 ),
    inference(resolution,[],[f1215,f232])).

fof(f232,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(resolution,[],[f84,f82])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t76_funct_2.p',redefinition_k2_relset_1)).

fof(f1231,plain,
    ( spl5_194
    | ~ spl5_212 ),
    inference(avatar_split_clause,[],[f1223,f1214,f1149])).

fof(f1149,plain,
    ( spl5_194
  <=> k1_relset_1(sK0,sK0,k5_relat_1(sK1,sK2)) = k1_relat_1(k5_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_194])])).

fof(f1223,plain,
    ( k1_relset_1(sK0,sK0,k5_relat_1(sK1,sK2)) = k1_relat_1(k5_relat_1(sK1,sK2))
    | ~ spl5_212 ),
    inference(resolution,[],[f1215,f253])).

fof(f253,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(X0,X1))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(resolution,[],[f85,f82])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t76_funct_2.p',redefinition_k1_relset_1)).

fof(f1230,plain,
    ( spl5_204
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_88
    | ~ spl5_212 ),
    inference(avatar_split_clause,[],[f1229,f1214,f626,f113,f99,f1185])).

fof(f1185,plain,
    ( spl5_204
  <=> k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK1,sK2),sK1) = k5_relat_1(k5_relat_1(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_204])])).

fof(f99,plain,
    ( spl5_0
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f626,plain,
    ( spl5_88
  <=> v1_funct_1(k5_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).

fof(f1229,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK1,sK2),sK1) = k5_relat_1(k5_relat_1(sK1,sK2),sK1)
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_88
    | ~ spl5_212 ),
    inference(subsumption_resolution,[],[f1222,f627])).

fof(f627,plain,
    ( v1_funct_1(k5_relat_1(sK1,sK2))
    | ~ spl5_88 ),
    inference(avatar_component_clause,[],[f626])).

fof(f1222,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK1,sK2),sK1) = k5_relat_1(k5_relat_1(sK1,sK2),sK1)
    | ~ v1_funct_1(k5_relat_1(sK1,sK2))
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_212 ),
    inference(resolution,[],[f1215,f538])).

fof(f538,plain,
    ( ! [X6,X4,X5] :
        ( ~ r1_tarski(X4,k2_zfmisc_1(X5,X6))
        | k1_partfun1(X5,X6,sK0,sK0,X4,sK1) = k5_relat_1(X4,sK1)
        | ~ v1_funct_1(X4) )
    | ~ spl5_0
    | ~ spl5_4 ),
    inference(resolution,[],[f533,f82])).

fof(f533,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | k1_partfun1(X1,X2,sK0,sK0,X0,sK1) = k5_relat_1(X0,sK1) )
    | ~ spl5_0
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f527,f114])).

fof(f527,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(sK1)
        | ~ v1_funct_1(X0)
        | k1_partfun1(X1,X2,sK0,sK0,X0,sK1) = k5_relat_1(X0,sK1) )
    | ~ spl5_0 ),
    inference(resolution,[],[f77,f100])).

fof(f100,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f99])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_1(X4)
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t76_funct_2.p',redefinition_k1_partfun1)).

fof(f1228,plain,
    ( spl5_206
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_88
    | ~ spl5_212 ),
    inference(avatar_split_clause,[],[f1227,f1214,f626,f155,f141,f1193])).

fof(f1193,plain,
    ( spl5_206
  <=> k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK1,sK2),sK2) = k5_relat_1(k5_relat_1(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_206])])).

fof(f141,plain,
    ( spl5_12
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f155,plain,
    ( spl5_16
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f1227,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK1,sK2),sK2) = k5_relat_1(k5_relat_1(sK1,sK2),sK2)
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_88
    | ~ spl5_212 ),
    inference(subsumption_resolution,[],[f1221,f627])).

fof(f1221,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK1,sK2),sK2) = k5_relat_1(k5_relat_1(sK1,sK2),sK2)
    | ~ v1_funct_1(k5_relat_1(sK1,sK2))
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_212 ),
    inference(resolution,[],[f1215,f598])).

fof(f598,plain,
    ( ! [X6,X4,X5] :
        ( ~ r1_tarski(X4,k2_zfmisc_1(X5,X6))
        | k1_partfun1(X5,X6,sK0,sK0,X4,sK2) = k5_relat_1(X4,sK2)
        | ~ v1_funct_1(X4) )
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(resolution,[],[f534,f82])).

fof(f534,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X3)
        | k1_partfun1(X4,X5,sK0,sK0,X3,sK2) = k5_relat_1(X3,sK2) )
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f528,f156])).

fof(f156,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f155])).

fof(f528,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_1(X3)
        | k1_partfun1(X4,X5,sK0,sK0,X3,sK2) = k5_relat_1(X3,sK2) )
    | ~ spl5_12 ),
    inference(resolution,[],[f77,f142])).

fof(f142,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f141])).

fof(f1216,plain,
    ( spl5_212
    | ~ spl5_96 ),
    inference(avatar_split_clause,[],[f1096,f703,f1214])).

fof(f703,plain,
    ( spl5_96
  <=> m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_96])])).

fof(f1096,plain,
    ( r1_tarski(k5_relat_1(sK1,sK2),k2_zfmisc_1(sK0,sK0))
    | ~ spl5_96 ),
    inference(resolution,[],[f704,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f704,plain,
    ( m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_96 ),
    inference(avatar_component_clause,[],[f703])).

fof(f1209,plain,
    ( spl5_208
    | ~ spl5_211
    | ~ spl5_88
    | ~ spl5_96 ),
    inference(avatar_split_clause,[],[f1196,f703,f626,f1207,f1201])).

fof(f1201,plain,
    ( spl5_208
  <=> k1_relset_1(sK0,sK0,k5_relat_1(sK1,sK2)) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_208])])).

fof(f1207,plain,
    ( spl5_211
  <=> ~ v1_funct_2(k5_relat_1(sK1,sK2),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_211])])).

fof(f1196,plain,
    ( ~ v1_funct_2(k5_relat_1(sK1,sK2),sK0,sK0)
    | k1_relset_1(sK0,sK0,k5_relat_1(sK1,sK2)) = sK0
    | ~ spl5_88
    | ~ spl5_96 ),
    inference(subsumption_resolution,[],[f1095,f627])).

fof(f1095,plain,
    ( ~ v1_funct_2(k5_relat_1(sK1,sK2),sK0,sK0)
    | ~ v1_funct_1(k5_relat_1(sK1,sK2))
    | k1_relset_1(sK0,sK0,k5_relat_1(sK1,sK2)) = sK0
    | ~ spl5_96 ),
    inference(resolution,[],[f704,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1)
      | k1_relset_1(X0,X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t76_funct_2.p',t67_funct_2)).

fof(f1195,plain,
    ( spl5_206
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_88
    | ~ spl5_96 ),
    inference(avatar_split_clause,[],[f1188,f703,f626,f155,f141,f1193])).

fof(f1188,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK1,sK2),sK2) = k5_relat_1(k5_relat_1(sK1,sK2),sK2)
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_88
    | ~ spl5_96 ),
    inference(subsumption_resolution,[],[f1094,f627])).

fof(f1094,plain,
    ( ~ v1_funct_1(k5_relat_1(sK1,sK2))
    | k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK1,sK2),sK2) = k5_relat_1(k5_relat_1(sK1,sK2),sK2)
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_96 ),
    inference(resolution,[],[f704,f534])).

fof(f1187,plain,
    ( spl5_204
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_88
    | ~ spl5_96 ),
    inference(avatar_split_clause,[],[f1180,f703,f626,f113,f99,f1185])).

fof(f1180,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK1,sK2),sK1) = k5_relat_1(k5_relat_1(sK1,sK2),sK1)
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_88
    | ~ spl5_96 ),
    inference(subsumption_resolution,[],[f1093,f627])).

fof(f1093,plain,
    ( ~ v1_funct_1(k5_relat_1(sK1,sK2))
    | k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK1,sK2),sK1) = k5_relat_1(k5_relat_1(sK1,sK2),sK1)
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_96 ),
    inference(resolution,[],[f704,f533])).

fof(f1179,plain,
    ( spl5_202
    | ~ spl5_96 ),
    inference(avatar_split_clause,[],[f1092,f703,f1177])).

fof(f1177,plain,
    ( spl5_202
  <=> r1_tarski(k2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_202])])).

fof(f1092,plain,
    ( r1_tarski(k2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2)),sK0)
    | ~ spl5_96 ),
    inference(resolution,[],[f704,f356])).

fof(f356,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r1_tarski(k2_relset_1(X1,X2,X0),X2) ) ),
    inference(resolution,[],[f88,f83])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t76_funct_2.p',dt_k2_relset_1)).

fof(f1172,plain,
    ( spl5_200
    | ~ spl5_96 ),
    inference(avatar_split_clause,[],[f1091,f703,f1170])).

fof(f1170,plain,
    ( spl5_200
  <=> r1_tarski(k1_relset_1(sK0,sK0,k5_relat_1(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_200])])).

fof(f1091,plain,
    ( r1_tarski(k1_relset_1(sK0,sK0,k5_relat_1(sK1,sK2)),sK0)
    | ~ spl5_96 ),
    inference(resolution,[],[f704,f312])).

fof(f312,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r1_tarski(k1_relset_1(X1,X2,X0),X1) ) ),
    inference(resolution,[],[f87,f83])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t76_funct_2.p',dt_k1_relset_1)).

fof(f1165,plain,
    ( spl5_198
    | ~ spl5_96 ),
    inference(avatar_split_clause,[],[f1090,f703,f1163])).

fof(f1090,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),k5_relat_1(sK1,sK2))
    | ~ spl5_96 ),
    inference(resolution,[],[f704,f94])).

fof(f1158,plain,
    ( spl5_196
    | ~ spl5_96 ),
    inference(avatar_split_clause,[],[f1088,f703,f1156])).

fof(f1156,plain,
    ( spl5_196
  <=> v1_relat_1(k5_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_196])])).

fof(f1088,plain,
    ( v1_relat_1(k5_relat_1(sK1,sK2))
    | ~ spl5_96 ),
    inference(resolution,[],[f704,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t76_funct_2.p',cc1_relset_1)).

fof(f1151,plain,
    ( spl5_194
    | ~ spl5_96 ),
    inference(avatar_split_clause,[],[f1087,f703,f1149])).

fof(f1087,plain,
    ( k1_relset_1(sK0,sK0,k5_relat_1(sK1,sK2)) = k1_relat_1(k5_relat_1(sK1,sK2))
    | ~ spl5_96 ),
    inference(resolution,[],[f704,f85])).

fof(f1144,plain,
    ( spl5_192
    | ~ spl5_96 ),
    inference(avatar_split_clause,[],[f1086,f703,f1142])).

fof(f1086,plain,
    ( k2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2)) = k2_relat_1(k5_relat_1(sK1,sK2))
    | ~ spl5_96 ),
    inference(resolution,[],[f704,f84])).

fof(f1136,plain,
    ( ~ spl5_187
    | spl5_190
    | ~ spl5_0
    | ~ spl5_96 ),
    inference(avatar_split_clause,[],[f1082,f703,f99,f1134,f1120])).

fof(f1120,plain,
    ( spl5_187
  <=> ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_187])])).

fof(f1134,plain,
    ( spl5_190
  <=> k5_relat_1(sK1,sK2) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_190])])).

fof(f1082,plain,
    ( k5_relat_1(sK1,sK2) = sK1
    | ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),sK1)
    | ~ spl5_0
    | ~ spl5_96 ),
    inference(resolution,[],[f704,f390])).

fof(f390,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | sK1 = X0
        | ~ r2_relset_1(sK0,sK0,X0,sK1) )
    | ~ spl5_0 ),
    inference(resolution,[],[f72,f100])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f1129,plain,
    ( ~ spl5_183
    | spl5_188
    | ~ spl5_12
    | ~ spl5_96 ),
    inference(avatar_split_clause,[],[f1081,f703,f141,f1127,f1107])).

fof(f1107,plain,
    ( spl5_183
  <=> ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_183])])).

fof(f1127,plain,
    ( spl5_188
  <=> k5_relat_1(sK1,sK2) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_188])])).

fof(f1081,plain,
    ( k5_relat_1(sK1,sK2) = sK2
    | ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),sK2)
    | ~ spl5_12
    | ~ spl5_96 ),
    inference(resolution,[],[f704,f391])).

fof(f391,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | sK2 = X1
        | ~ r2_relset_1(sK0,sK0,X1,sK2) )
    | ~ spl5_12 ),
    inference(resolution,[],[f72,f142])).

fof(f1122,plain,
    ( spl5_184
    | ~ spl5_187
    | ~ spl5_0
    | ~ spl5_96 ),
    inference(avatar_split_clause,[],[f1080,f703,f99,f1120,f1114])).

fof(f1114,plain,
    ( spl5_184
  <=> r2_relset_1(sK0,sK0,sK1,k5_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_184])])).

fof(f1080,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),sK1)
    | r2_relset_1(sK0,sK0,sK1,k5_relat_1(sK1,sK2))
    | ~ spl5_0
    | ~ spl5_96 ),
    inference(resolution,[],[f704,f473])).

fof(f473,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ r2_relset_1(sK0,sK0,X0,sK1)
        | r2_relset_1(sK0,sK0,sK1,X0) )
    | ~ spl5_0 ),
    inference(resolution,[],[f73,f100])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | r2_relset_1(X0,X1,X3,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X3,X2)
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X3,X2)
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
       => r2_relset_1(X0,X1,X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t76_funct_2.p',symmetry_r2_relset_1)).

fof(f1109,plain,
    ( spl5_180
    | ~ spl5_183
    | ~ spl5_12
    | ~ spl5_96 ),
    inference(avatar_split_clause,[],[f1079,f703,f141,f1107,f1101])).

fof(f1101,plain,
    ( spl5_180
  <=> r2_relset_1(sK0,sK0,sK2,k5_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_180])])).

fof(f1079,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK2),sK2)
    | r2_relset_1(sK0,sK0,sK2,k5_relat_1(sK1,sK2))
    | ~ spl5_12
    | ~ spl5_96 ),
    inference(resolution,[],[f704,f474])).

fof(f474,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ r2_relset_1(sK0,sK0,X1,sK2)
        | r2_relset_1(sK0,sK0,sK2,X1) )
    | ~ spl5_12 ),
    inference(resolution,[],[f73,f142])).

fof(f1072,plain,
    ( spl5_176
    | spl5_178
    | ~ spl5_16
    | ~ spl5_24
    | ~ spl5_46
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f1062,f401,f304,f191,f155,f1070,f1067])).

fof(f1067,plain,
    ( spl5_176
  <=> k6_relat_1(sK0) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_176])])).

fof(f191,plain,
    ( spl5_24
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f304,plain,
    ( spl5_46
  <=> k1_relat_1(sK2) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f401,plain,
    ( spl5_58
  <=> r1_tarski(k2_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f1062,plain,
    ( ! [X1] :
        ( k1_relat_1(X1) != sK0
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v2_funct_1(X1)
        | k5_relat_1(sK2,X1) != X1
        | k6_relat_1(sK0) = sK2 )
    | ~ spl5_16
    | ~ spl5_24
    | ~ spl5_46
    | ~ spl5_58 ),
    inference(subsumption_resolution,[],[f1061,f402])).

fof(f402,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0)
    | ~ spl5_58 ),
    inference(avatar_component_clause,[],[f401])).

fof(f1061,plain,
    ( ! [X1] :
        ( k1_relat_1(X1) != sK0
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(sK2),sK0)
        | ~ v2_funct_1(X1)
        | k5_relat_1(sK2,X1) != X1
        | k6_relat_1(sK0) = sK2 )
    | ~ spl5_16
    | ~ spl5_24
    | ~ spl5_46 ),
    inference(inner_rewriting,[],[f1060])).

fof(f1060,plain,
    ( ! [X1] :
        ( k1_relat_1(X1) != sK0
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(sK2),k1_relat_1(X1))
        | ~ v2_funct_1(X1)
        | k5_relat_1(sK2,X1) != X1
        | k6_relat_1(k1_relat_1(X1)) = sK2 )
    | ~ spl5_16
    | ~ spl5_24
    | ~ spl5_46 ),
    inference(subsumption_resolution,[],[f1059,f156])).

fof(f1059,plain,
    ( ! [X1] :
        ( k1_relat_1(X1) != sK0
        | ~ v1_funct_1(X1)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(sK2),k1_relat_1(X1))
        | ~ v2_funct_1(X1)
        | k5_relat_1(sK2,X1) != X1
        | k6_relat_1(k1_relat_1(X1)) = sK2 )
    | ~ spl5_24
    | ~ spl5_46 ),
    inference(subsumption_resolution,[],[f1023,f192])).

fof(f192,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f191])).

fof(f1023,plain,
    ( ! [X1] :
        ( k1_relat_1(X1) != sK0
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(sK2),k1_relat_1(X1))
        | ~ v2_funct_1(X1)
        | k5_relat_1(sK2,X1) != X1
        | k6_relat_1(k1_relat_1(X1)) = sK2 )
    | ~ spl5_46 ),
    inference(superposition,[],[f90,f305])).

fof(f305,plain,
    ( k1_relat_1(sK2) = sK0
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f304])).

fof(f90,plain,(
    ! [X2,X1] :
      ( k1_relat_1(X1) != k1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X2),k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | k5_relat_1(X2,X1) != X1
      | k6_relat_1(k1_relat_1(X1)) = X2 ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X1) != X0
      | k1_relat_1(X2) != X0
      | ~ r1_tarski(k2_relat_1(X2),X0)
      | ~ v2_funct_1(X1)
      | k5_relat_1(X2,X1) != X1
      | k6_relat_1(X0) = X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k6_relat_1(X0) = X2
          | k5_relat_1(X2,X1) != X1
          | ~ v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X0
          | k1_relat_1(X1) != X0
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k6_relat_1(X0) = X2
          | k5_relat_1(X2,X1) != X1
          | ~ v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X0
          | k1_relat_1(X1) != X0
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( ( k5_relat_1(X2,X1) = X1
              & v2_funct_1(X1)
              & r1_tarski(k2_relat_1(X2),X0)
              & k1_relat_1(X2) = X0
              & k1_relat_1(X1) = X0 )
           => k6_relat_1(X0) = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t76_funct_2.p',t50_funct_1)).

fof(f1058,plain,
    ( spl5_172
    | spl5_174
    | ~ spl5_4
    | ~ spl5_22
    | ~ spl5_44
    | ~ spl5_56 ),
    inference(avatar_split_clause,[],[f1048,f387,f296,f184,f113,f1056,f1053])).

fof(f1053,plain,
    ( spl5_172
  <=> k6_relat_1(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_172])])).

fof(f1056,plain,
    ( spl5_174
  <=> ! [X0] :
        ( k1_relat_1(X0) != sK0
        | k5_relat_1(sK1,X0) != X0
        | ~ v2_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_174])])).

fof(f387,plain,
    ( spl5_56
  <=> r1_tarski(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f1048,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v2_funct_1(X0)
        | k5_relat_1(sK1,X0) != X0
        | k6_relat_1(sK0) = sK1 )
    | ~ spl5_4
    | ~ spl5_22
    | ~ spl5_44
    | ~ spl5_56 ),
    inference(subsumption_resolution,[],[f1047,f388])).

fof(f388,plain,
    ( r1_tarski(k2_relat_1(sK1),sK0)
    | ~ spl5_56 ),
    inference(avatar_component_clause,[],[f387])).

fof(f1047,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(k2_relat_1(sK1),sK0)
        | ~ v2_funct_1(X0)
        | k5_relat_1(sK1,X0) != X0
        | k6_relat_1(sK0) = sK1 )
    | ~ spl5_4
    | ~ spl5_22
    | ~ spl5_44 ),
    inference(inner_rewriting,[],[f1046])).

fof(f1046,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(k2_relat_1(sK1),k1_relat_1(X0))
        | ~ v2_funct_1(X0)
        | k5_relat_1(sK1,X0) != X0
        | k6_relat_1(k1_relat_1(X0)) = sK1 )
    | ~ spl5_4
    | ~ spl5_22
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f1045,f114])).

fof(f1045,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | ~ v1_funct_1(X0)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(k2_relat_1(sK1),k1_relat_1(X0))
        | ~ v2_funct_1(X0)
        | k5_relat_1(sK1,X0) != X0
        | k6_relat_1(k1_relat_1(X0)) = sK1 )
    | ~ spl5_22
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f1022,f185])).

fof(f1022,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(sK1)
        | ~ v1_funct_1(sK1)
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(k2_relat_1(sK1),k1_relat_1(X0))
        | ~ v2_funct_1(X0)
        | k5_relat_1(sK1,X0) != X0
        | k6_relat_1(k1_relat_1(X0)) = sK1 )
    | ~ spl5_44 ),
    inference(superposition,[],[f90,f297])).

fof(f1044,plain,
    ( ~ spl5_169
    | spl5_170
    | ~ spl5_16
    | ~ spl5_24
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f1034,f304,f191,f155,f1042,f1039])).

fof(f1039,plain,
    ( spl5_169
  <=> ~ v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_169])])).

fof(f1042,plain,
    ( spl5_170
  <=> ! [X1] :
        ( k6_relat_1(sK0) = X1
        | k5_relat_1(X1,sK2) != sK2
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | k1_relat_1(X1) != sK0
        | ~ r1_tarski(k2_relat_1(X1),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_170])])).

fof(f1034,plain,
    ( ! [X1] :
        ( k6_relat_1(sK0) = X1
        | ~ r1_tarski(k2_relat_1(X1),sK0)
        | k1_relat_1(X1) != sK0
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v2_funct_1(sK2)
        | k5_relat_1(X1,sK2) != sK2 )
    | ~ spl5_16
    | ~ spl5_24
    | ~ spl5_46 ),
    inference(forward_demodulation,[],[f1033,f305])).

fof(f1033,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_relat_1(X1),sK0)
        | k1_relat_1(X1) != sK0
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v2_funct_1(sK2)
        | k5_relat_1(X1,sK2) != sK2
        | k6_relat_1(k1_relat_1(sK2)) = X1 )
    | ~ spl5_16
    | ~ spl5_24
    | ~ spl5_46 ),
    inference(forward_demodulation,[],[f1032,f305])).

fof(f1032,plain,
    ( ! [X1] :
        ( k1_relat_1(X1) != sK0
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(sK2))
        | ~ v2_funct_1(sK2)
        | k5_relat_1(X1,sK2) != sK2
        | k6_relat_1(k1_relat_1(sK2)) = X1 )
    | ~ spl5_16
    | ~ spl5_24
    | ~ spl5_46 ),
    inference(subsumption_resolution,[],[f1031,f192])).

fof(f1031,plain,
    ( ! [X1] :
        ( k1_relat_1(X1) != sK0
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(sK2)
        | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(sK2))
        | ~ v2_funct_1(sK2)
        | k5_relat_1(X1,sK2) != sK2
        | k6_relat_1(k1_relat_1(sK2)) = X1 )
    | ~ spl5_16
    | ~ spl5_46 ),
    inference(subsumption_resolution,[],[f1021,f156])).

fof(f1021,plain,
    ( ! [X1] :
        ( k1_relat_1(X1) != sK0
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(sK2)
        | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(sK2))
        | ~ v2_funct_1(sK2)
        | k5_relat_1(X1,sK2) != sK2
        | k6_relat_1(k1_relat_1(sK2)) = X1 )
    | ~ spl5_46 ),
    inference(superposition,[],[f90,f305])).

fof(f1017,plain,
    ( spl5_166
    | ~ spl5_76
    | ~ spl5_142 ),
    inference(avatar_split_clause,[],[f1009,f921,f554,f1015])).

fof(f1015,plain,
    ( spl5_166
  <=> k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_166])])).

fof(f554,plain,
    ( spl5_76
  <=> k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f1009,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = sK1
    | ~ spl5_76
    | ~ spl5_142 ),
    inference(backward_demodulation,[],[f922,f555])).

fof(f555,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1)
    | ~ spl5_76 ),
    inference(avatar_component_clause,[],[f554])).

fof(f1003,plain,
    ( spl5_164
    | ~ spl5_94 ),
    inference(avatar_split_clause,[],[f887,f692,f1001])).

fof(f1001,plain,
    ( spl5_164
  <=> r1_tarski(k5_relat_1(sK2,sK1),k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_164])])).

fof(f692,plain,
    ( spl5_94
  <=> m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).

fof(f887,plain,
    ( r1_tarski(k5_relat_1(sK2,sK1),k2_zfmisc_1(sK0,sK0))
    | ~ spl5_94 ),
    inference(resolution,[],[f693,f83])).

fof(f693,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_94 ),
    inference(avatar_component_clause,[],[f692])).

fof(f996,plain,
    ( spl5_160
    | ~ spl5_163
    | ~ spl5_82
    | ~ spl5_94 ),
    inference(avatar_split_clause,[],[f983,f692,f585,f994,f988])).

fof(f988,plain,
    ( spl5_160
  <=> k1_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_160])])).

fof(f994,plain,
    ( spl5_163
  <=> ~ v1_funct_2(k5_relat_1(sK2,sK1),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_163])])).

fof(f585,plain,
    ( spl5_82
  <=> v1_funct_1(k5_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).

fof(f983,plain,
    ( ~ v1_funct_2(k5_relat_1(sK2,sK1),sK0,sK0)
    | k1_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) = sK0
    | ~ spl5_82
    | ~ spl5_94 ),
    inference(subsumption_resolution,[],[f886,f586])).

fof(f586,plain,
    ( v1_funct_1(k5_relat_1(sK2,sK1))
    | ~ spl5_82 ),
    inference(avatar_component_clause,[],[f585])).

fof(f886,plain,
    ( ~ v1_funct_2(k5_relat_1(sK2,sK1),sK0,sK0)
    | ~ v1_funct_1(k5_relat_1(sK2,sK1))
    | k1_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) = sK0
    | ~ spl5_94 ),
    inference(resolution,[],[f693,f79])).

fof(f982,plain,
    ( spl5_158
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_82
    | ~ spl5_94 ),
    inference(avatar_split_clause,[],[f975,f692,f585,f155,f141,f980])).

fof(f980,plain,
    ( spl5_158
  <=> k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK2,sK1),sK2) = k5_relat_1(k5_relat_1(sK2,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_158])])).

fof(f975,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK2,sK1),sK2) = k5_relat_1(k5_relat_1(sK2,sK1),sK2)
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_82
    | ~ spl5_94 ),
    inference(subsumption_resolution,[],[f885,f586])).

fof(f885,plain,
    ( ~ v1_funct_1(k5_relat_1(sK2,sK1))
    | k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK2,sK1),sK2) = k5_relat_1(k5_relat_1(sK2,sK1),sK2)
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_94 ),
    inference(resolution,[],[f693,f534])).

fof(f974,plain,
    ( spl5_156
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_82
    | ~ spl5_94 ),
    inference(avatar_split_clause,[],[f967,f692,f585,f113,f99,f972])).

fof(f972,plain,
    ( spl5_156
  <=> k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK2,sK1),sK1) = k5_relat_1(k5_relat_1(sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_156])])).

fof(f967,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK2,sK1),sK1) = k5_relat_1(k5_relat_1(sK2,sK1),sK1)
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_82
    | ~ spl5_94 ),
    inference(subsumption_resolution,[],[f884,f586])).

fof(f884,plain,
    ( ~ v1_funct_1(k5_relat_1(sK2,sK1))
    | k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK2,sK1),sK1) = k5_relat_1(k5_relat_1(sK2,sK1),sK1)
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_94 ),
    inference(resolution,[],[f693,f533])).

fof(f966,plain,
    ( spl5_154
    | ~ spl5_94 ),
    inference(avatar_split_clause,[],[f883,f692,f964])).

fof(f964,plain,
    ( spl5_154
  <=> r1_tarski(k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_154])])).

fof(f883,plain,
    ( r1_tarski(k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)),sK0)
    | ~ spl5_94 ),
    inference(resolution,[],[f693,f356])).

fof(f959,plain,
    ( spl5_152
    | ~ spl5_94 ),
    inference(avatar_split_clause,[],[f882,f692,f957])).

fof(f957,plain,
    ( spl5_152
  <=> r1_tarski(k1_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_152])])).

fof(f882,plain,
    ( r1_tarski(k1_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)),sK0)
    | ~ spl5_94 ),
    inference(resolution,[],[f693,f312])).

fof(f952,plain,
    ( spl5_150
    | ~ spl5_94 ),
    inference(avatar_split_clause,[],[f881,f692,f950])).

fof(f950,plain,
    ( spl5_150
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1),k5_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_150])])).

fof(f881,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1),k5_relat_1(sK2,sK1))
    | ~ spl5_94 ),
    inference(resolution,[],[f693,f94])).

fof(f945,plain,
    ( spl5_148
    | ~ spl5_94 ),
    inference(avatar_split_clause,[],[f879,f692,f943])).

fof(f943,plain,
    ( spl5_148
  <=> v1_relat_1(k5_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_148])])).

fof(f879,plain,
    ( v1_relat_1(k5_relat_1(sK2,sK1))
    | ~ spl5_94 ),
    inference(resolution,[],[f693,f86])).

fof(f938,plain,
    ( spl5_146
    | ~ spl5_94 ),
    inference(avatar_split_clause,[],[f878,f692,f936])).

fof(f936,plain,
    ( spl5_146
  <=> k1_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) = k1_relat_1(k5_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_146])])).

fof(f878,plain,
    ( k1_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) = k1_relat_1(k5_relat_1(sK2,sK1))
    | ~ spl5_94 ),
    inference(resolution,[],[f693,f85])).

fof(f931,plain,
    ( spl5_144
    | ~ spl5_94 ),
    inference(avatar_split_clause,[],[f877,f692,f929])).

fof(f929,plain,
    ( spl5_144
  <=> k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) = k2_relat_1(k5_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_144])])).

fof(f877,plain,
    ( k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) = k2_relat_1(k5_relat_1(sK2,sK1))
    | ~ spl5_94 ),
    inference(resolution,[],[f693,f84])).

fof(f923,plain,
    ( spl5_142
    | ~ spl5_0
    | ~ spl5_80
    | ~ spl5_94 ),
    inference(avatar_split_clause,[],[f916,f692,f574,f99,f921])).

fof(f574,plain,
    ( spl5_80
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_80])])).

fof(f916,plain,
    ( k5_relat_1(sK2,sK1) = sK1
    | ~ spl5_0
    | ~ spl5_80
    | ~ spl5_94 ),
    inference(subsumption_resolution,[],[f873,f575])).

fof(f575,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1),sK1)
    | ~ spl5_80 ),
    inference(avatar_component_clause,[],[f574])).

fof(f873,plain,
    ( k5_relat_1(sK2,sK1) = sK1
    | ~ r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1),sK1)
    | ~ spl5_0
    | ~ spl5_94 ),
    inference(resolution,[],[f693,f390])).

fof(f915,plain,
    ( ~ spl5_137
    | spl5_140
    | ~ spl5_12
    | ~ spl5_94 ),
    inference(avatar_split_clause,[],[f872,f692,f141,f913,f898])).

fof(f898,plain,
    ( spl5_137
  <=> ~ r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_137])])).

fof(f913,plain,
    ( spl5_140
  <=> k5_relat_1(sK2,sK1) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_140])])).

fof(f872,plain,
    ( k5_relat_1(sK2,sK1) = sK2
    | ~ r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1),sK2)
    | ~ spl5_12
    | ~ spl5_94 ),
    inference(resolution,[],[f693,f391])).

fof(f908,plain,
    ( spl5_138
    | ~ spl5_0
    | ~ spl5_80
    | ~ spl5_94 ),
    inference(avatar_split_clause,[],[f901,f692,f574,f99,f906])).

fof(f906,plain,
    ( spl5_138
  <=> r2_relset_1(sK0,sK0,sK1,k5_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_138])])).

fof(f901,plain,
    ( r2_relset_1(sK0,sK0,sK1,k5_relat_1(sK2,sK1))
    | ~ spl5_0
    | ~ spl5_80
    | ~ spl5_94 ),
    inference(subsumption_resolution,[],[f871,f575])).

fof(f871,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1),sK1)
    | r2_relset_1(sK0,sK0,sK1,k5_relat_1(sK2,sK1))
    | ~ spl5_0
    | ~ spl5_94 ),
    inference(resolution,[],[f693,f473])).

fof(f900,plain,
    ( spl5_134
    | ~ spl5_137
    | ~ spl5_12
    | ~ spl5_94 ),
    inference(avatar_split_clause,[],[f870,f692,f141,f898,f892])).

fof(f892,plain,
    ( spl5_134
  <=> r2_relset_1(sK0,sK0,sK2,k5_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_134])])).

fof(f870,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1),sK2)
    | r2_relset_1(sK0,sK0,sK2,k5_relat_1(sK2,sK1))
    | ~ spl5_12
    | ~ spl5_94 ),
    inference(resolution,[],[f693,f474])).

fof(f869,plain,
    ( spl5_118
    | ~ spl5_132 ),
    inference(avatar_split_clause,[],[f861,f850,f799])).

fof(f799,plain,
    ( spl5_118
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK1),k5_relat_1(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_118])])).

fof(f850,plain,
    ( spl5_132
  <=> r1_tarski(k5_relat_1(sK1,sK1),k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_132])])).

fof(f861,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK1),k5_relat_1(sK1,sK1))
    | ~ spl5_132 ),
    inference(resolution,[],[f851,f211])).

fof(f851,plain,
    ( r1_tarski(k5_relat_1(sK1,sK1),k2_zfmisc_1(sK0,sK0))
    | ~ spl5_132 ),
    inference(avatar_component_clause,[],[f850])).

fof(f868,plain,
    ( spl5_112
    | ~ spl5_132 ),
    inference(avatar_split_clause,[],[f860,f850,f778])).

fof(f778,plain,
    ( spl5_112
  <=> k2_relset_1(sK0,sK0,k5_relat_1(sK1,sK1)) = k2_relat_1(k5_relat_1(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_112])])).

fof(f860,plain,
    ( k2_relset_1(sK0,sK0,k5_relat_1(sK1,sK1)) = k2_relat_1(k5_relat_1(sK1,sK1))
    | ~ spl5_132 ),
    inference(resolution,[],[f851,f232])).

fof(f867,plain,
    ( spl5_114
    | ~ spl5_132 ),
    inference(avatar_split_clause,[],[f859,f850,f785])).

fof(f785,plain,
    ( spl5_114
  <=> k1_relset_1(sK0,sK0,k5_relat_1(sK1,sK1)) = k1_relat_1(k5_relat_1(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).

fof(f859,plain,
    ( k1_relset_1(sK0,sK0,k5_relat_1(sK1,sK1)) = k1_relat_1(k5_relat_1(sK1,sK1))
    | ~ spl5_132 ),
    inference(resolution,[],[f851,f253])).

fof(f866,plain,
    ( spl5_124
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_78
    | ~ spl5_132 ),
    inference(avatar_split_clause,[],[f865,f850,f565,f113,f99,f821])).

fof(f821,plain,
    ( spl5_124
  <=> k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK1,sK1),sK1) = k5_relat_1(k5_relat_1(sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_124])])).

fof(f565,plain,
    ( spl5_78
  <=> v1_funct_1(k5_relat_1(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).

fof(f865,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK1,sK1),sK1) = k5_relat_1(k5_relat_1(sK1,sK1),sK1)
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_78
    | ~ spl5_132 ),
    inference(subsumption_resolution,[],[f858,f566])).

fof(f566,plain,
    ( v1_funct_1(k5_relat_1(sK1,sK1))
    | ~ spl5_78 ),
    inference(avatar_component_clause,[],[f565])).

fof(f858,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK1,sK1),sK1) = k5_relat_1(k5_relat_1(sK1,sK1),sK1)
    | ~ v1_funct_1(k5_relat_1(sK1,sK1))
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_132 ),
    inference(resolution,[],[f851,f538])).

fof(f864,plain,
    ( spl5_126
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_78
    | ~ spl5_132 ),
    inference(avatar_split_clause,[],[f863,f850,f565,f155,f141,f829])).

fof(f829,plain,
    ( spl5_126
  <=> k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK1,sK1),sK2) = k5_relat_1(k5_relat_1(sK1,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_126])])).

fof(f863,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK1,sK1),sK2) = k5_relat_1(k5_relat_1(sK1,sK1),sK2)
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_78
    | ~ spl5_132 ),
    inference(subsumption_resolution,[],[f857,f566])).

fof(f857,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK1,sK1),sK2) = k5_relat_1(k5_relat_1(sK1,sK1),sK2)
    | ~ v1_funct_1(k5_relat_1(sK1,sK1))
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_132 ),
    inference(resolution,[],[f851,f598])).

fof(f852,plain,
    ( spl5_132
    | ~ spl5_92 ),
    inference(avatar_split_clause,[],[f732,f681,f850])).

fof(f681,plain,
    ( spl5_92
  <=> m1_subset_1(k5_relat_1(sK1,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).

fof(f732,plain,
    ( r1_tarski(k5_relat_1(sK1,sK1),k2_zfmisc_1(sK0,sK0))
    | ~ spl5_92 ),
    inference(resolution,[],[f682,f83])).

fof(f682,plain,
    ( m1_subset_1(k5_relat_1(sK1,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_92 ),
    inference(avatar_component_clause,[],[f681])).

fof(f845,plain,
    ( spl5_128
    | ~ spl5_131
    | ~ spl5_78
    | ~ spl5_92 ),
    inference(avatar_split_clause,[],[f832,f681,f565,f843,f837])).

fof(f837,plain,
    ( spl5_128
  <=> k1_relset_1(sK0,sK0,k5_relat_1(sK1,sK1)) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_128])])).

fof(f843,plain,
    ( spl5_131
  <=> ~ v1_funct_2(k5_relat_1(sK1,sK1),sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_131])])).

fof(f832,plain,
    ( ~ v1_funct_2(k5_relat_1(sK1,sK1),sK0,sK0)
    | k1_relset_1(sK0,sK0,k5_relat_1(sK1,sK1)) = sK0
    | ~ spl5_78
    | ~ spl5_92 ),
    inference(subsumption_resolution,[],[f731,f566])).

fof(f731,plain,
    ( ~ v1_funct_2(k5_relat_1(sK1,sK1),sK0,sK0)
    | ~ v1_funct_1(k5_relat_1(sK1,sK1))
    | k1_relset_1(sK0,sK0,k5_relat_1(sK1,sK1)) = sK0
    | ~ spl5_92 ),
    inference(resolution,[],[f682,f79])).

fof(f831,plain,
    ( spl5_126
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_78
    | ~ spl5_92 ),
    inference(avatar_split_clause,[],[f824,f681,f565,f155,f141,f829])).

fof(f824,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK1,sK1),sK2) = k5_relat_1(k5_relat_1(sK1,sK1),sK2)
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_78
    | ~ spl5_92 ),
    inference(subsumption_resolution,[],[f730,f566])).

fof(f730,plain,
    ( ~ v1_funct_1(k5_relat_1(sK1,sK1))
    | k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK1,sK1),sK2) = k5_relat_1(k5_relat_1(sK1,sK1),sK2)
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_92 ),
    inference(resolution,[],[f682,f534])).

fof(f823,plain,
    ( spl5_124
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_78
    | ~ spl5_92 ),
    inference(avatar_split_clause,[],[f816,f681,f565,f113,f99,f821])).

fof(f816,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK1,sK1),sK1) = k5_relat_1(k5_relat_1(sK1,sK1),sK1)
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_78
    | ~ spl5_92 ),
    inference(subsumption_resolution,[],[f729,f566])).

fof(f729,plain,
    ( ~ v1_funct_1(k5_relat_1(sK1,sK1))
    | k1_partfun1(sK0,sK0,sK0,sK0,k5_relat_1(sK1,sK1),sK1) = k5_relat_1(k5_relat_1(sK1,sK1),sK1)
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_92 ),
    inference(resolution,[],[f682,f533])).

fof(f815,plain,
    ( spl5_122
    | ~ spl5_92 ),
    inference(avatar_split_clause,[],[f728,f681,f813])).

fof(f813,plain,
    ( spl5_122
  <=> r1_tarski(k2_relset_1(sK0,sK0,k5_relat_1(sK1,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_122])])).

fof(f728,plain,
    ( r1_tarski(k2_relset_1(sK0,sK0,k5_relat_1(sK1,sK1)),sK0)
    | ~ spl5_92 ),
    inference(resolution,[],[f682,f356])).

fof(f808,plain,
    ( spl5_120
    | ~ spl5_92 ),
    inference(avatar_split_clause,[],[f727,f681,f806])).

fof(f806,plain,
    ( spl5_120
  <=> r1_tarski(k1_relset_1(sK0,sK0,k5_relat_1(sK1,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_120])])).

fof(f727,plain,
    ( r1_tarski(k1_relset_1(sK0,sK0,k5_relat_1(sK1,sK1)),sK0)
    | ~ spl5_92 ),
    inference(resolution,[],[f682,f312])).

fof(f801,plain,
    ( spl5_118
    | ~ spl5_92 ),
    inference(avatar_split_clause,[],[f726,f681,f799])).

fof(f726,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK1),k5_relat_1(sK1,sK1))
    | ~ spl5_92 ),
    inference(resolution,[],[f682,f94])).

fof(f794,plain,
    ( spl5_116
    | ~ spl5_92 ),
    inference(avatar_split_clause,[],[f724,f681,f792])).

fof(f792,plain,
    ( spl5_116
  <=> v1_relat_1(k5_relat_1(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_116])])).

fof(f724,plain,
    ( v1_relat_1(k5_relat_1(sK1,sK1))
    | ~ spl5_92 ),
    inference(resolution,[],[f682,f86])).

fof(f787,plain,
    ( spl5_114
    | ~ spl5_92 ),
    inference(avatar_split_clause,[],[f723,f681,f785])).

fof(f723,plain,
    ( k1_relset_1(sK0,sK0,k5_relat_1(sK1,sK1)) = k1_relat_1(k5_relat_1(sK1,sK1))
    | ~ spl5_92 ),
    inference(resolution,[],[f682,f85])).

fof(f780,plain,
    ( spl5_112
    | ~ spl5_92 ),
    inference(avatar_split_clause,[],[f722,f681,f778])).

fof(f722,plain,
    ( k2_relset_1(sK0,sK0,k5_relat_1(sK1,sK1)) = k2_relat_1(k5_relat_1(sK1,sK1))
    | ~ spl5_92 ),
    inference(resolution,[],[f682,f84])).

fof(f772,plain,
    ( ~ spl5_107
    | spl5_110
    | ~ spl5_0
    | ~ spl5_92 ),
    inference(avatar_split_clause,[],[f718,f681,f99,f770,f756])).

fof(f756,plain,
    ( spl5_107
  <=> ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_107])])).

fof(f770,plain,
    ( spl5_110
  <=> k5_relat_1(sK1,sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_110])])).

fof(f718,plain,
    ( k5_relat_1(sK1,sK1) = sK1
    | ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK1),sK1)
    | ~ spl5_0
    | ~ spl5_92 ),
    inference(resolution,[],[f682,f390])).

fof(f765,plain,
    ( ~ spl5_103
    | spl5_108
    | ~ spl5_12
    | ~ spl5_92 ),
    inference(avatar_split_clause,[],[f717,f681,f141,f763,f743])).

fof(f743,plain,
    ( spl5_103
  <=> ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_103])])).

fof(f763,plain,
    ( spl5_108
  <=> k5_relat_1(sK1,sK1) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_108])])).

fof(f717,plain,
    ( k5_relat_1(sK1,sK1) = sK2
    | ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK1),sK2)
    | ~ spl5_12
    | ~ spl5_92 ),
    inference(resolution,[],[f682,f391])).

fof(f758,plain,
    ( spl5_104
    | ~ spl5_107
    | ~ spl5_0
    | ~ spl5_92 ),
    inference(avatar_split_clause,[],[f716,f681,f99,f756,f750])).

fof(f750,plain,
    ( spl5_104
  <=> r2_relset_1(sK0,sK0,sK1,k5_relat_1(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_104])])).

fof(f716,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK1),sK1)
    | r2_relset_1(sK0,sK0,sK1,k5_relat_1(sK1,sK1))
    | ~ spl5_0
    | ~ spl5_92 ),
    inference(resolution,[],[f682,f473])).

fof(f745,plain,
    ( spl5_100
    | ~ spl5_103
    | ~ spl5_12
    | ~ spl5_92 ),
    inference(avatar_split_clause,[],[f715,f681,f141,f743,f737])).

fof(f737,plain,
    ( spl5_100
  <=> r2_relset_1(sK0,sK0,sK2,k5_relat_1(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_100])])).

fof(f715,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK1,sK1),sK2)
    | r2_relset_1(sK0,sK0,sK2,k5_relat_1(sK1,sK1))
    | ~ spl5_12
    | ~ spl5_92 ),
    inference(resolution,[],[f682,f474])).

fof(f714,plain,
    ( spl5_98
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_86 ),
    inference(avatar_split_clause,[],[f707,f614,f155,f141,f712])).

fof(f712,plain,
    ( spl5_98
  <=> m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).

fof(f614,plain,
    ( spl5_86
  <=> k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK2) = k5_relat_1(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_86])])).

fof(f707,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_86 ),
    inference(subsumption_resolution,[],[f706,f156])).

fof(f706,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl5_12
    | ~ spl5_86 ),
    inference(subsumption_resolution,[],[f669,f142])).

fof(f669,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl5_86 ),
    inference(duplicate_literal_removal,[],[f668])).

fof(f668,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl5_86 ),
    inference(superposition,[],[f76,f615])).

fof(f615,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK2) = k5_relat_1(sK2,sK2)
    | ~ spl5_86 ),
    inference(avatar_component_clause,[],[f614])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    file('/export/starexec/sandbox2/benchmark/funct_2__t76_funct_2.p',dt_k1_partfun1)).

fof(f705,plain,
    ( spl5_96
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_84 ),
    inference(avatar_split_clause,[],[f698,f606,f155,f141,f113,f99,f703])).

fof(f606,plain,
    ( spl5_84
  <=> k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).

fof(f698,plain,
    ( m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_84 ),
    inference(subsumption_resolution,[],[f697,f114])).

fof(f697,plain,
    ( m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_84 ),
    inference(subsumption_resolution,[],[f696,f142])).

fof(f696,plain,
    ( m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl5_0
    | ~ spl5_16
    | ~ spl5_84 ),
    inference(subsumption_resolution,[],[f695,f156])).

fof(f695,plain,
    ( m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl5_0
    | ~ spl5_84 ),
    inference(subsumption_resolution,[],[f667,f100])).

fof(f667,plain,
    ( m1_subset_1(k5_relat_1(sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl5_84 ),
    inference(superposition,[],[f76,f607])).

fof(f607,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)
    | ~ spl5_84 ),
    inference(avatar_component_clause,[],[f606])).

fof(f694,plain,
    ( spl5_94
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f687,f554,f155,f141,f113,f99,f692])).

fof(f687,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_76 ),
    inference(subsumption_resolution,[],[f686,f156])).

fof(f686,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_76 ),
    inference(subsumption_resolution,[],[f685,f100])).

fof(f685,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_76 ),
    inference(subsumption_resolution,[],[f684,f114])).

fof(f684,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl5_12
    | ~ spl5_76 ),
    inference(subsumption_resolution,[],[f666,f142])).

fof(f666,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl5_76 ),
    inference(superposition,[],[f76,f555])).

fof(f683,plain,
    ( spl5_92
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_74 ),
    inference(avatar_split_clause,[],[f676,f546,f113,f99,f681])).

fof(f546,plain,
    ( spl5_74
  <=> k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK1) = k5_relat_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).

fof(f676,plain,
    ( m1_subset_1(k5_relat_1(sK1,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_74 ),
    inference(subsumption_resolution,[],[f675,f114])).

fof(f675,plain,
    ( m1_subset_1(k5_relat_1(sK1,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl5_0
    | ~ spl5_74 ),
    inference(subsumption_resolution,[],[f670,f100])).

fof(f670,plain,
    ( m1_subset_1(k5_relat_1(sK1,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl5_74 ),
    inference(duplicate_literal_removal,[],[f665])).

fof(f665,plain,
    ( m1_subset_1(k5_relat_1(sK1,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl5_74 ),
    inference(superposition,[],[f76,f547])).

fof(f547,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK1) = k5_relat_1(sK1,sK1)
    | ~ spl5_74 ),
    inference(avatar_component_clause,[],[f546])).

fof(f639,plain,
    ( spl5_90
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_86 ),
    inference(avatar_split_clause,[],[f632,f614,f155,f141,f637])).

fof(f637,plain,
    ( spl5_90
  <=> v1_funct_1(k5_relat_1(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_90])])).

fof(f632,plain,
    ( v1_funct_1(k5_relat_1(sK2,sK2))
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_86 ),
    inference(subsumption_resolution,[],[f631,f156])).

fof(f631,plain,
    ( v1_funct_1(k5_relat_1(sK2,sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl5_12
    | ~ spl5_86 ),
    inference(subsumption_resolution,[],[f630,f142])).

fof(f630,plain,
    ( v1_funct_1(k5_relat_1(sK2,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl5_86 ),
    inference(duplicate_literal_removal,[],[f629])).

fof(f629,plain,
    ( v1_funct_1(k5_relat_1(sK2,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl5_86 ),
    inference(superposition,[],[f75,f615])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f628,plain,
    ( spl5_88
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_84 ),
    inference(avatar_split_clause,[],[f621,f606,f155,f141,f113,f99,f626])).

fof(f621,plain,
    ( v1_funct_1(k5_relat_1(sK1,sK2))
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_84 ),
    inference(subsumption_resolution,[],[f620,f114])).

fof(f620,plain,
    ( v1_funct_1(k5_relat_1(sK1,sK2))
    | ~ v1_funct_1(sK1)
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_84 ),
    inference(subsumption_resolution,[],[f619,f142])).

fof(f619,plain,
    ( v1_funct_1(k5_relat_1(sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl5_0
    | ~ spl5_16
    | ~ spl5_84 ),
    inference(subsumption_resolution,[],[f618,f156])).

fof(f618,plain,
    ( v1_funct_1(k5_relat_1(sK1,sK2))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl5_0
    | ~ spl5_84 ),
    inference(subsumption_resolution,[],[f617,f100])).

fof(f617,plain,
    ( v1_funct_1(k5_relat_1(sK1,sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl5_84 ),
    inference(superposition,[],[f75,f607])).

fof(f616,plain,
    ( spl5_86
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f609,f155,f141,f614])).

fof(f609,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK2) = k5_relat_1(sK2,sK2)
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f596,f156])).

fof(f596,plain,
    ( ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK2) = k5_relat_1(sK2,sK2)
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(resolution,[],[f534,f142])).

fof(f608,plain,
    ( spl5_84
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f601,f155,f141,f113,f99,f606])).

fof(f601,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f595,f114])).

fof(f595,plain,
    ( ~ v1_funct_1(sK1)
    | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK2) = k5_relat_1(sK1,sK2)
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(resolution,[],[f534,f100])).

fof(f587,plain,
    ( spl5_82
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f580,f554,f155,f141,f113,f99,f585])).

fof(f580,plain,
    ( v1_funct_1(k5_relat_1(sK2,sK1))
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_76 ),
    inference(subsumption_resolution,[],[f579,f156])).

fof(f579,plain,
    ( v1_funct_1(k5_relat_1(sK2,sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_76 ),
    inference(subsumption_resolution,[],[f578,f100])).

fof(f578,plain,
    ( v1_funct_1(k5_relat_1(sK2,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_76 ),
    inference(subsumption_resolution,[],[f577,f114])).

fof(f577,plain,
    ( v1_funct_1(k5_relat_1(sK2,sK1))
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl5_12
    | ~ spl5_76 ),
    inference(subsumption_resolution,[],[f569,f142])).

fof(f569,plain,
    ( v1_funct_1(k5_relat_1(sK2,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl5_76 ),
    inference(superposition,[],[f75,f555])).

fof(f576,plain,
    ( spl5_80
    | ~ spl5_10
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f568,f554,f134,f574])).

fof(f134,plain,
    ( spl5_10
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f568,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1),sK1)
    | ~ spl5_10
    | ~ spl5_76 ),
    inference(backward_demodulation,[],[f555,f135])).

fof(f135,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f134])).

fof(f567,plain,
    ( spl5_78
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_74 ),
    inference(avatar_split_clause,[],[f560,f546,f113,f99,f565])).

fof(f560,plain,
    ( v1_funct_1(k5_relat_1(sK1,sK1))
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_74 ),
    inference(subsumption_resolution,[],[f559,f114])).

fof(f559,plain,
    ( v1_funct_1(k5_relat_1(sK1,sK1))
    | ~ v1_funct_1(sK1)
    | ~ spl5_0
    | ~ spl5_74 ),
    inference(subsumption_resolution,[],[f558,f100])).

fof(f558,plain,
    ( v1_funct_1(k5_relat_1(sK1,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl5_74 ),
    inference(duplicate_literal_removal,[],[f557])).

fof(f557,plain,
    ( v1_funct_1(k5_relat_1(sK1,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ spl5_74 ),
    inference(superposition,[],[f75,f547])).

fof(f556,plain,
    ( spl5_76
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f549,f155,f141,f113,f99,f554])).

fof(f549,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1)
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f536,f156])).

fof(f536,plain,
    ( ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1)
    | ~ spl5_0
    | ~ spl5_4
    | ~ spl5_12 ),
    inference(resolution,[],[f533,f142])).

fof(f548,plain,
    ( spl5_74
    | ~ spl5_0
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f541,f113,f99,f546])).

fof(f541,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK1) = k5_relat_1(sK1,sK1)
    | ~ spl5_0
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f535,f114])).

fof(f535,plain,
    ( ~ v1_funct_1(sK1)
    | k1_partfun1(sK0,sK0,sK0,sK0,sK1,sK1) = k5_relat_1(sK1,sK1)
    | ~ spl5_0
    | ~ spl5_4 ),
    inference(resolution,[],[f533,f100])).

fof(f467,plain,
    ( ~ spl5_71
    | spl5_72
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f446,f141,f465,f459])).

fof(f459,plain,
    ( spl5_71
  <=> ~ r2_relset_1(sK0,sK0,sK3(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).

fof(f465,plain,
    ( spl5_72
  <=> sK2 = sK3(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).

fof(f446,plain,
    ( sK2 = sK3(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ r2_relset_1(sK0,sK0,sK3(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),sK2)
    | ~ spl5_12 ),
    inference(resolution,[],[f391,f78])).

fof(f78,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t76_funct_2.p',existence_m1_subset_1)).

fof(f454,plain,
    ( ~ spl5_69
    | ~ spl5_0
    | ~ spl5_12
    | spl5_63 ),
    inference(avatar_split_clause,[],[f447,f417,f141,f99,f452])).

fof(f452,plain,
    ( spl5_69
  <=> ~ r2_relset_1(sK0,sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_69])])).

fof(f417,plain,
    ( spl5_63
  <=> sK1 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).

fof(f447,plain,
    ( ~ r2_relset_1(sK0,sK0,sK1,sK2)
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_63 ),
    inference(subsumption_resolution,[],[f441,f418])).

fof(f418,plain,
    ( sK1 != sK2
    | ~ spl5_63 ),
    inference(avatar_component_clause,[],[f417])).

fof(f441,plain,
    ( sK1 = sK2
    | ~ r2_relset_1(sK0,sK0,sK1,sK2)
    | ~ spl5_0
    | ~ spl5_12 ),
    inference(resolution,[],[f391,f100])).

fof(f435,plain,
    ( ~ spl5_65
    | spl5_66
    | ~ spl5_0 ),
    inference(avatar_split_clause,[],[f409,f99,f433,f427])).

fof(f427,plain,
    ( spl5_65
  <=> ~ r2_relset_1(sK0,sK0,sK3(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).

fof(f433,plain,
    ( spl5_66
  <=> sK1 = sK3(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).

fof(f409,plain,
    ( sK1 = sK3(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ r2_relset_1(sK0,sK0,sK3(k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))),sK1)
    | ~ spl5_0 ),
    inference(resolution,[],[f390,f78])).

fof(f422,plain,
    ( ~ spl5_61
    | spl5_62
    | ~ spl5_0
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f405,f141,f99,f420,f414])).

fof(f414,plain,
    ( spl5_61
  <=> ~ r2_relset_1(sK0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).

fof(f420,plain,
    ( spl5_62
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f405,plain,
    ( sK1 = sK2
    | ~ r2_relset_1(sK0,sK0,sK2,sK1)
    | ~ spl5_0
    | ~ spl5_12 ),
    inference(resolution,[],[f390,f142])).

fof(f403,plain,
    ( spl5_58
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f396,f379,f401])).

fof(f379,plain,
    ( spl5_54
  <=> m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f396,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0)
    | ~ spl5_54 ),
    inference(resolution,[],[f380,f83])).

fof(f380,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl5_54 ),
    inference(avatar_component_clause,[],[f379])).

fof(f389,plain,
    ( spl5_56
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f382,f371,f387])).

fof(f371,plain,
    ( spl5_52
  <=> m1_subset_1(k2_relat_1(sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f382,plain,
    ( r1_tarski(k2_relat_1(sK1),sK0)
    | ~ spl5_52 ),
    inference(resolution,[],[f372,f83])).

fof(f372,plain,
    ( m1_subset_1(k2_relat_1(sK1),k1_zfmisc_1(sK0))
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f371])).

fof(f381,plain,
    ( spl5_54
    | ~ spl5_12
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f374,f245,f141,f379])).

fof(f245,plain,
    ( spl5_34
  <=> k2_relset_1(sK0,sK0,sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f374,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl5_12
    | ~ spl5_34 ),
    inference(subsumption_resolution,[],[f365,f142])).

fof(f365,plain,
    ( m1_subset_1(k2_relat_1(sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_34 ),
    inference(superposition,[],[f88,f246])).

fof(f246,plain,
    ( k2_relset_1(sK0,sK0,sK2) = k2_relat_1(sK2)
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f245])).

fof(f373,plain,
    ( spl5_52
    | ~ spl5_0
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f366,f238,f99,f371])).

fof(f238,plain,
    ( spl5_32
  <=> k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f366,plain,
    ( m1_subset_1(k2_relat_1(sK1),k1_zfmisc_1(sK0))
    | ~ spl5_0
    | ~ spl5_32 ),
    inference(subsumption_resolution,[],[f364,f100])).

fof(f364,plain,
    ( m1_subset_1(k2_relat_1(sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_32 ),
    inference(superposition,[],[f88,f239])).

fof(f239,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1)
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f238])).

fof(f338,plain,
    ( spl5_50
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f331,f326,f336])).

fof(f336,plain,
    ( spl5_50
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f326,plain,
    ( spl5_48
  <=> m1_subset_1(sK0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f331,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl5_48 ),
    inference(resolution,[],[f327,f83])).

fof(f327,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl5_48 ),
    inference(avatar_component_clause,[],[f326])).

fof(f330,plain,
    ( spl5_48
    | ~ spl5_12
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f329,f288,f141,f326])).

fof(f288,plain,
    ( spl5_42
  <=> k1_relset_1(sK0,sK0,sK2) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f329,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl5_12
    | ~ spl5_42 ),
    inference(subsumption_resolution,[],[f320,f142])).

fof(f320,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_42 ),
    inference(superposition,[],[f87,f289])).

fof(f289,plain,
    ( k1_relset_1(sK0,sK0,sK2) = sK0
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f288])).

fof(f328,plain,
    ( spl5_48
    | ~ spl5_0
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f321,f279,f99,f326])).

fof(f279,plain,
    ( spl5_40
  <=> k1_relset_1(sK0,sK0,sK1) = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f321,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl5_0
    | ~ spl5_40 ),
    inference(subsumption_resolution,[],[f319,f100])).

fof(f319,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl5_40 ),
    inference(superposition,[],[f87,f280])).

fof(f280,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f279])).

fof(f306,plain,
    ( spl5_46
    | ~ spl5_38
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f299,f288,f266,f304])).

fof(f266,plain,
    ( spl5_38
  <=> k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f299,plain,
    ( k1_relat_1(sK2) = sK0
    | ~ spl5_38
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f267,f289])).

fof(f267,plain,
    ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2)
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f266])).

fof(f298,plain,
    ( spl5_44
    | ~ spl5_36
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f291,f279,f259,f296])).

fof(f259,plain,
    ( spl5_36
  <=> k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f291,plain,
    ( k1_relat_1(sK1) = sK0
    | ~ spl5_36
    | ~ spl5_40 ),
    inference(forward_demodulation,[],[f260,f280])).

fof(f260,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f259])).

fof(f290,plain,
    ( spl5_42
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f283,f155,f148,f141,f288])).

fof(f148,plain,
    ( spl5_14
  <=> v1_funct_2(sK2,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f283,plain,
    ( k1_relset_1(sK0,sK0,sK2) = sK0
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f282,f156])).

fof(f282,plain,
    ( ~ v1_funct_1(sK2)
    | k1_relset_1(sK0,sK0,sK2) = sK0
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f270,f149])).

fof(f149,plain,
    ( v1_funct_2(sK2,sK0,sK0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f148])).

fof(f270,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2)
    | k1_relset_1(sK0,sK0,sK2) = sK0
    | ~ spl5_12 ),
    inference(resolution,[],[f79,f142])).

fof(f281,plain,
    ( spl5_40
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f274,f113,f106,f99,f279])).

fof(f106,plain,
    ( spl5_2
  <=> v1_funct_2(sK1,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f274,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f273,f114])).

fof(f273,plain,
    ( ~ v1_funct_1(sK1)
    | k1_relset_1(sK0,sK0,sK1) = sK0
    | ~ spl5_0
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f269,f107])).

fof(f107,plain,
    ( v1_funct_2(sK1,sK0,sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f269,plain,
    ( ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1)
    | k1_relset_1(sK0,sK0,sK1) = sK0
    | ~ spl5_0 ),
    inference(resolution,[],[f79,f100])).

fof(f268,plain,
    ( spl5_38
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f252,f141,f266])).

fof(f252,plain,
    ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2)
    | ~ spl5_12 ),
    inference(resolution,[],[f85,f142])).

fof(f261,plain,
    ( spl5_36
    | ~ spl5_0 ),
    inference(avatar_split_clause,[],[f251,f99,f259])).

fof(f251,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1)
    | ~ spl5_0 ),
    inference(resolution,[],[f85,f100])).

fof(f247,plain,
    ( spl5_34
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f231,f141,f245])).

fof(f231,plain,
    ( k2_relset_1(sK0,sK0,sK2) = k2_relat_1(sK2)
    | ~ spl5_12 ),
    inference(resolution,[],[f84,f142])).

fof(f240,plain,
    ( spl5_32
    | ~ spl5_0 ),
    inference(avatar_split_clause,[],[f230,f99,f238])).

fof(f230,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1)
    | ~ spl5_0 ),
    inference(resolution,[],[f84,f100])).

fof(f226,plain,
    ( spl5_30
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f210,f141,f224])).

fof(f224,plain,
    ( spl5_30
  <=> r2_relset_1(sK0,sK0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f210,plain,
    ( r2_relset_1(sK0,sK0,sK2,sK2)
    | ~ spl5_12 ),
    inference(resolution,[],[f94,f142])).

fof(f219,plain,
    ( spl5_28
    | ~ spl5_0 ),
    inference(avatar_split_clause,[],[f209,f99,f217])).

fof(f217,plain,
    ( spl5_28
  <=> r2_relset_1(sK0,sK0,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f209,plain,
    ( r2_relset_1(sK0,sK0,sK1,sK1)
    | ~ spl5_0 ),
    inference(resolution,[],[f94,f100])).

fof(f205,plain,
    ( ~ spl5_27
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f195,f141,f202])).

fof(f202,plain,
    ( spl5_27
  <=> ~ sP4(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f195,plain,
    ( ~ sP4(sK0,sK0)
    | ~ spl5_12 ),
    inference(resolution,[],[f93,f142])).

fof(f93,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ sP4(X1,X0) ) ),
    inference(general_splitting,[],[f74,f92_D])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2)
      | sP4(X1,X0) ) ),
    inference(cnf_transformation,[],[f92_D])).

fof(f92_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | r2_relset_1(X0,X1,X2,X2) )
    <=> ~ sP4(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t76_funct_2.p',reflexivity_r2_relset_1)).

fof(f204,plain,
    ( ~ spl5_27
    | ~ spl5_0 ),
    inference(avatar_split_clause,[],[f194,f99,f202])).

fof(f194,plain,
    ( ~ sP4(sK0,sK0)
    | ~ spl5_0 ),
    inference(resolution,[],[f93,f100])).

fof(f193,plain,
    ( spl5_24
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f177,f141,f191])).

fof(f177,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_12 ),
    inference(resolution,[],[f86,f142])).

fof(f186,plain,
    ( spl5_22
    | ~ spl5_0 ),
    inference(avatar_split_clause,[],[f176,f99,f184])).

fof(f176,plain,
    ( v1_relat_1(sK1)
    | ~ spl5_0 ),
    inference(resolution,[],[f86,f100])).

fof(f175,plain,
    ( spl5_20
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f159,f141,f173])).

fof(f173,plain,
    ( spl5_20
  <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f159,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK0))
    | ~ spl5_12 ),
    inference(resolution,[],[f83,f142])).

fof(f168,plain,
    ( spl5_18
    | ~ spl5_0 ),
    inference(avatar_split_clause,[],[f158,f99,f166])).

fof(f166,plain,
    ( spl5_18
  <=> r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f158,plain,
    ( r1_tarski(sK1,k2_zfmisc_1(sK0,sK0))
    | ~ spl5_0 ),
    inference(resolution,[],[f83,f100])).

fof(f157,plain,(
    spl5_16 ),
    inference(avatar_split_clause,[],[f60,f155])).

fof(f60,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( ( v2_funct_1(X1)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) )
             => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) )
           => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t76_funct_2.p',t76_funct_2)).

fof(f150,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f61,f148])).

fof(f61,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f143,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f62,f141])).

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f136,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f63,f134])).

fof(f63,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f129,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f64,f127])).

fof(f64,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f122,plain,(
    ~ spl5_7 ),
    inference(avatar_split_clause,[],[f89,f120])).

fof(f120,plain,
    ( spl5_7
  <=> ~ r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f89,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f65,f69])).

fof(f69,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t76_funct_2.p',redefinition_k6_partfun1)).

fof(f65,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f115,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f66,f113])).

fof(f66,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f108,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f67,f106])).

fof(f67,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f101,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f68,f99])).

fof(f68,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
