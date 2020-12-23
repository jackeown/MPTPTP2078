%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:42 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 313 expanded)
%              Number of leaves         :   51 ( 143 expanded)
%              Depth                    :    8
%              Number of atoms          :  605 (1214 expanded)
%              Number of equality atoms :   76 ( 170 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1311,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f91,f96,f101,f106,f111,f116,f121,f126,f131,f136,f176,f214,f258,f279,f296,f326,f349,f371,f392,f409,f701,f920,f931,f932,f1002,f1051,f1082,f1172,f1206,f1307,f1308,f1310])).

fof(f1310,plain,
    ( ~ spl8_6
    | ~ spl8_5
    | spl8_1
    | spl8_131
    | ~ spl8_32
    | ~ spl8_51 ),
    inference(avatar_split_clause,[],[f1021,f407,f276,f1029,f83,f103,f108])).

fof(f108,plain,
    ( spl8_6
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f103,plain,
    ( spl8_5
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f83,plain,
    ( spl8_1
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f1029,plain,
    ( spl8_131
  <=> ! [X1] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,X1),k1_relat_1(sK4))
        | ~ v1_funct_2(X1,sK1,sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | ~ v1_funct_1(X1)
        | k1_funct_1(k8_funct_2(sK1,sK2,sK0,X1,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(X1,sK5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_131])])).

fof(f276,plain,
    ( spl8_32
  <=> k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f407,plain,
    ( spl8_51
  <=> ! [X1,X3,X0,X2] :
        ( ~ v1_funct_1(X0)
        | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k1_funct_1(X2,k1_funct_1(X0,sK5))
        | ~ r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2))
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).

fof(f1021,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,X1),k1_relat_1(sK4))
        | k1_funct_1(k8_funct_2(sK1,sK2,sK0,X1,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(X1,sK5))
        | ~ v1_funct_1(X1)
        | v1_xboole_0(sK2)
        | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | ~ v1_funct_2(X1,sK1,sK2) )
    | ~ spl8_32
    | ~ spl8_51 ),
    inference(superposition,[],[f408,f278])).

fof(f278,plain,
    ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f276])).

fof(f408,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2))
        | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k1_funct_1(X2,k1_funct_1(X0,sK5))
        | ~ v1_funct_1(X0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) )
    | ~ spl8_51 ),
    inference(avatar_component_clause,[],[f407])).

fof(f1308,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1307,plain,
    ( spl8_168
    | ~ spl8_4
    | ~ spl8_2
    | ~ spl8_3
    | ~ spl8_39
    | ~ spl8_131 ),
    inference(avatar_split_clause,[],[f1302,f1029,f323,f93,f88,f98,f1304])).

fof(f1304,plain,
    ( spl8_168
  <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_168])])).

fof(f98,plain,
    ( spl8_4
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f88,plain,
    ( spl8_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f93,plain,
    ( spl8_3
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f323,plain,
    ( spl8_39
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f1302,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK3)
    | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl8_39
    | ~ spl8_131 ),
    inference(resolution,[],[f1030,f325])).

fof(f325,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))
    | ~ spl8_39 ),
    inference(avatar_component_clause,[],[f323])).

fof(f1030,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,X1),k1_relat_1(sK4))
        | ~ v1_funct_2(X1,sK1,sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | ~ v1_funct_1(X1)
        | k1_funct_1(k8_funct_2(sK1,sK2,sK0,X1,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(X1,sK5)) )
    | ~ spl8_131 ),
    inference(avatar_component_clause,[],[f1029])).

fof(f1206,plain,
    ( spl8_154
    | ~ spl8_38
    | ~ spl8_149 ),
    inference(avatar_split_clause,[],[f1198,f1169,f313,f1203])).

fof(f1203,plain,
    ( spl8_154
  <=> k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_154])])).

fof(f313,plain,
    ( spl8_38
  <=> ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK4))
        | k7_partfun1(sK0,sK4,X1) = k1_funct_1(sK4,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f1169,plain,
    ( spl8_149
  <=> r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_149])])).

fof(f1198,plain,
    ( k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | ~ spl8_38
    | ~ spl8_149 ),
    inference(resolution,[],[f314,f1171])).

fof(f1171,plain,
    ( r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ spl8_149 ),
    inference(avatar_component_clause,[],[f1169])).

fof(f314,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK4))
        | k7_partfun1(sK0,sK4,X1) = k1_funct_1(sK4,X1) )
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f313])).

fof(f1172,plain,
    ( spl8_149
    | ~ spl8_17
    | ~ spl8_104 ),
    inference(avatar_split_clause,[],[f1165,f844,f169,f1169])).

fof(f169,plain,
    ( spl8_17
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f844,plain,
    ( spl8_104
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_104])])).

fof(f1165,plain,
    ( r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))
    | ~ spl8_17
    | ~ spl8_104 ),
    inference(resolution,[],[f845,f171])).

fof(f171,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f169])).

fof(f845,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) )
    | ~ spl8_104 ),
    inference(avatar_component_clause,[],[f844])).

fof(f1082,plain,
    ( spl8_103
    | spl8_104
    | ~ spl8_4
    | ~ spl8_97
    | ~ spl8_99 ),
    inference(avatar_split_clause,[],[f1074,f810,f793,f98,f844,f840])).

fof(f840,plain,
    ( spl8_103
  <=> k1_xboole_0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_103])])).

fof(f793,plain,
    ( spl8_97
  <=> v1_funct_2(sK3,sK1,k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_97])])).

fof(f810,plain,
    ( spl8_99
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_99])])).

fof(f1074,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,sK1,k1_relat_1(sK4))
        | ~ v1_funct_1(sK3)
        | ~ r2_hidden(X0,sK1)
        | k1_xboole_0 = k1_relat_1(sK4)
        | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)) )
    | ~ spl8_99 ),
    inference(resolution,[],[f812,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | r2_hidden(k1_funct_1(X3,X2),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),X1)
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),X1)
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

fof(f812,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4))))
    | ~ spl8_99 ),
    inference(avatar_component_clause,[],[f810])).

fof(f1051,plain,
    ( spl8_8
    | ~ spl8_11
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f1049,f173,f133,f118])).

fof(f118,plain,
    ( spl8_8
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f133,plain,
    ( spl8_11
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f173,plain,
    ( spl8_18
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f1049,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_11
    | ~ spl8_18 ),
    inference(resolution,[],[f1042,f219])).

fof(f219,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k1_xboole_0)
        | k1_xboole_0 = X1 )
    | ~ spl8_11 ),
    inference(resolution,[],[f60,f200])).

fof(f200,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl8_11 ),
    inference(resolution,[],[f197,f135])).

fof(f135,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f133])).

fof(f197,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f62,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1042,plain,
    ( ! [X0] : r1_tarski(sK1,X0)
    | ~ spl8_18 ),
    inference(resolution,[],[f175,f197])).

fof(f175,plain,
    ( v1_xboole_0(sK1)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f173])).

fof(f1002,plain,
    ( spl8_13
    | ~ spl8_11
    | ~ spl8_118 ),
    inference(avatar_split_clause,[],[f999,f917,f133,f148])).

fof(f148,plain,
    ( spl8_13
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f917,plain,
    ( spl8_118
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_118])])).

fof(f999,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK3)
    | ~ spl8_118 ),
    inference(resolution,[],[f919,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f919,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_118 ),
    inference(avatar_component_clause,[],[f917])).

fof(f932,plain,
    ( spl8_97
    | ~ spl8_39
    | ~ spl8_46 ),
    inference(avatar_split_clause,[],[f927,f369,f323,f793])).

fof(f369,plain,
    ( spl8_46
  <=> ! [X0] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X0)
        | v1_funct_2(sK3,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f927,plain,
    ( v1_funct_2(sK3,sK1,k1_relat_1(sK4))
    | ~ spl8_39
    | ~ spl8_46 ),
    inference(resolution,[],[f325,f370])).

fof(f370,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X0)
        | v1_funct_2(sK3,sK1,X0) )
    | ~ spl8_46 ),
    inference(avatar_component_clause,[],[f369])).

fof(f931,plain,
    ( spl8_99
    | ~ spl8_39
    | ~ spl8_49 ),
    inference(avatar_split_clause,[],[f926,f390,f323,f810])).

fof(f390,plain,
    ( spl8_49
  <=> ! [X0] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).

fof(f926,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4))))
    | ~ spl8_39
    | ~ spl8_49 ),
    inference(resolution,[],[f325,f391])).

fof(f391,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) )
    | ~ spl8_49 ),
    inference(avatar_component_clause,[],[f390])).

fof(f920,plain,
    ( spl8_118
    | ~ spl8_99
    | ~ spl8_103 ),
    inference(avatar_split_clause,[],[f915,f840,f810,f917])).

fof(f915,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_99
    | ~ spl8_103 ),
    inference(forward_demodulation,[],[f888,f78])).

fof(f78,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f888,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl8_99
    | ~ spl8_103 ),
    inference(backward_demodulation,[],[f812,f842])).

fof(f842,plain,
    ( k1_xboole_0 = k1_relat_1(sK4)
    | ~ spl8_103 ),
    inference(avatar_component_clause,[],[f840])).

fof(f701,plain,
    ( spl8_38
    | ~ spl8_6
    | ~ spl8_24
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f700,f255,f211,f108,f313])).

fof(f211,plain,
    ( spl8_24
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f255,plain,
    ( spl8_30
  <=> v5_relat_1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f700,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK4)
        | ~ v1_funct_1(sK4)
        | ~ r2_hidden(X0,k1_relat_1(sK4))
        | k7_partfun1(sK0,sK4,X0) = k1_funct_1(sK4,X0) )
    | ~ spl8_30 ),
    inference(resolution,[],[f257,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).

fof(f257,plain,
    ( v5_relat_1(sK4,sK0)
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f255])).

fof(f409,plain,
    ( spl8_8
    | spl8_51
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f403,f128,f407,f118])).

fof(f128,plain,
    ( spl8_10
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f403,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK1,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
        | v1_xboole_0(X1)
        | ~ r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2))
        | k1_xboole_0 = sK1
        | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k1_funct_1(X2,k1_funct_1(X0,sK5)) )
    | ~ spl8_10 ),
    inference(resolution,[],[f67,f130])).

fof(f130,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f128])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | k1_xboole_0 = X1
      | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f392,plain,
    ( spl8_42
    | spl8_49
    | ~ spl8_4
    | ~ spl8_3
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f385,f88,f93,f98,f390,f342])).

fof(f342,plain,
    ( spl8_42
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f385,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,sK1,sK2)
        | ~ v1_funct_1(sK3)
        | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X0)
        | k1_xboole_0 = sK2
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) )
    | ~ spl8_2 ),
    inference(resolution,[],[f75,f90])).

fof(f90,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | k1_xboole_0 = X1
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

fof(f371,plain,
    ( spl8_42
    | spl8_46
    | ~ spl8_4
    | ~ spl8_3
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f364,f88,f93,f98,f369,f342])).

fof(f364,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,sK1,sK2)
        | ~ v1_funct_1(sK3)
        | ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),X0)
        | k1_xboole_0 = sK2
        | v1_funct_2(sK3,sK1,X0) )
    | ~ spl8_2 ),
    inference(resolution,[],[f74,f90])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | k1_xboole_0 = X1
      | v1_funct_2(X3,X0,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f349,plain,
    ( k1_xboole_0 != sK2
    | v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f326,plain,
    ( spl8_39
    | ~ spl8_9
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f321,f276,f123,f323])).

fof(f123,plain,
    ( spl8_9
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f321,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))
    | ~ spl8_9
    | ~ spl8_32 ),
    inference(backward_demodulation,[],[f125,f278])).

fof(f125,plain,
    ( r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f123])).

fof(f296,plain,
    ( ~ spl8_13
    | ~ spl8_3
    | spl8_18
    | spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f292,f88,f83,f173,f93,f148])).

fof(f292,plain,
    ( v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_xboole_0(sK3)
    | ~ spl8_2 ),
    inference(resolution,[],[f137,f90])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(global_subsumption,[],[f51,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_funct_2(X2,X0,X1)
              & ~ v1_xboole_0(X2)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_funct_2)).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f279,plain,
    ( spl8_32
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f267,f103,f276])).

fof(f267,plain,
    ( k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)
    | ~ spl8_5 ),
    inference(resolution,[],[f69,f105])).

fof(f105,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f103])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f258,plain,
    ( spl8_30
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f246,f103,f255])).

fof(f246,plain,
    ( v5_relat_1(sK4,sK0)
    | ~ spl8_5 ),
    inference(resolution,[],[f70,f105])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f214,plain,
    ( spl8_24
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f202,f103,f211])).

fof(f202,plain,
    ( v1_relat_1(sK4)
    | ~ spl8_5 ),
    inference(resolution,[],[f68,f105])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f176,plain,
    ( spl8_17
    | spl8_18
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f165,f128,f173,f169])).

fof(f165,plain,
    ( v1_xboole_0(sK1)
    | r2_hidden(sK5,sK1)
    | ~ spl8_10 ),
    inference(resolution,[],[f55,f130])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f136,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f50,f133])).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f131,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f40,f128])).

fof(f40,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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

fof(f126,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f41,f123])).

fof(f41,plain,(
    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) ),
    inference(cnf_transformation,[],[f21])).

fof(f121,plain,(
    ~ spl8_8 ),
    inference(avatar_split_clause,[],[f42,f118])).

fof(f42,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f21])).

fof(f116,plain,(
    ~ spl8_7 ),
    inference(avatar_split_clause,[],[f43,f113])).

fof(f113,plain,
    ( spl8_7
  <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f43,plain,(
    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) ),
    inference(cnf_transformation,[],[f21])).

fof(f111,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f44,f108])).

fof(f44,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f106,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f45,f103])).

fof(f45,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f101,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f46,f98])).

fof(f46,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f96,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f47,f93])).

fof(f47,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f91,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f48,f88])).

fof(f48,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f21])).

fof(f86,plain,(
    ~ spl8_1 ),
    inference(avatar_split_clause,[],[f49,f83])).

fof(f49,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:45:52 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.22/0.50  % (24418)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (24410)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (24430)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.52  % (24422)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.53  % (24414)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (24404)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (24412)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (24421)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  % (24428)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (24429)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (24411)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.55  % (24420)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (24431)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (24413)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (24407)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.56  % (24417)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (24405)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.56  % (24408)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.56  % (24426)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.50/0.56  % (24432)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.50/0.56  % (24425)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.50/0.56  % (24423)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.50/0.56  % (24419)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.50/0.57  % (24433)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.50/0.57  % (24415)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.50/0.57  % (24421)Refutation not found, incomplete strategy% (24421)------------------------------
% 1.50/0.57  % (24421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (24421)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.57  
% 1.50/0.57  % (24421)Memory used [KB]: 10746
% 1.50/0.57  % (24421)Time elapsed: 0.136 s
% 1.50/0.57  % (24421)------------------------------
% 1.50/0.57  % (24421)------------------------------
% 1.50/0.57  % (24424)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.50/0.57  % (24406)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.50/0.57  % (24416)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.64/0.58  % (24427)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.64/0.58  % (24426)Refutation not found, incomplete strategy% (24426)------------------------------
% 1.64/0.58  % (24426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.58  % (24426)Termination reason: Refutation not found, incomplete strategy
% 1.64/0.58  
% 1.64/0.58  % (24426)Memory used [KB]: 11001
% 1.64/0.58  % (24426)Time elapsed: 0.139 s
% 1.64/0.58  % (24426)------------------------------
% 1.64/0.58  % (24426)------------------------------
% 1.64/0.59  % (24409)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.64/0.60  % (24420)Refutation found. Thanks to Tanya!
% 1.64/0.60  % SZS status Theorem for theBenchmark
% 1.64/0.62  % SZS output start Proof for theBenchmark
% 1.64/0.62  fof(f1311,plain,(
% 1.64/0.62    $false),
% 1.64/0.62    inference(avatar_sat_refutation,[],[f86,f91,f96,f101,f106,f111,f116,f121,f126,f131,f136,f176,f214,f258,f279,f296,f326,f349,f371,f392,f409,f701,f920,f931,f932,f1002,f1051,f1082,f1172,f1206,f1307,f1308,f1310])).
% 1.64/0.62  fof(f1310,plain,(
% 1.64/0.62    ~spl8_6 | ~spl8_5 | spl8_1 | spl8_131 | ~spl8_32 | ~spl8_51),
% 1.64/0.62    inference(avatar_split_clause,[],[f1021,f407,f276,f1029,f83,f103,f108])).
% 1.64/0.62  fof(f108,plain,(
% 1.64/0.62    spl8_6 <=> v1_funct_1(sK4)),
% 1.64/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.64/0.62  fof(f103,plain,(
% 1.64/0.62    spl8_5 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 1.64/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.64/0.62  fof(f83,plain,(
% 1.64/0.62    spl8_1 <=> v1_xboole_0(sK2)),
% 1.64/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.64/0.62  fof(f1029,plain,(
% 1.64/0.62    spl8_131 <=> ! [X1] : (~r1_tarski(k2_relset_1(sK1,sK2,X1),k1_relat_1(sK4)) | ~v1_funct_2(X1,sK1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(X1) | k1_funct_1(k8_funct_2(sK1,sK2,sK0,X1,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(X1,sK5)))),
% 1.64/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_131])])).
% 1.64/0.62  fof(f276,plain,(
% 1.64/0.62    spl8_32 <=> k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4)),
% 1.64/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 1.64/0.62  fof(f407,plain,(
% 1.64/0.62    spl8_51 <=> ! [X1,X3,X0,X2] : (~v1_funct_1(X0) | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k1_funct_1(X2,k1_funct_1(X0,sK5)) | ~r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2)) | v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_1(X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1))),
% 1.64/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).
% 1.64/0.62  fof(f1021,plain,(
% 1.64/0.62    ( ! [X1] : (~r1_tarski(k2_relset_1(sK1,sK2,X1),k1_relat_1(sK4)) | k1_funct_1(k8_funct_2(sK1,sK2,sK0,X1,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(X1,sK5)) | ~v1_funct_1(X1) | v1_xboole_0(sK2) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~v1_funct_1(sK4) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(X1,sK1,sK2)) ) | (~spl8_32 | ~spl8_51)),
% 1.64/0.62    inference(superposition,[],[f408,f278])).
% 1.64/0.62  fof(f278,plain,(
% 1.64/0.62    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) | ~spl8_32),
% 1.64/0.62    inference(avatar_component_clause,[],[f276])).
% 1.64/0.62  fof(f408,plain,(
% 1.64/0.62    ( ! [X2,X0,X3,X1] : (~r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2)) | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k1_funct_1(X2,k1_funct_1(X0,sK5)) | ~v1_funct_1(X0) | v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_1(X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1)) ) | ~spl8_51),
% 1.64/0.62    inference(avatar_component_clause,[],[f407])).
% 1.64/0.62  fof(f1308,plain,(
% 1.64/0.62    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 1.64/0.62    introduced(theory_tautology_sat_conflict,[])).
% 1.64/0.62  fof(f1307,plain,(
% 1.64/0.62    spl8_168 | ~spl8_4 | ~spl8_2 | ~spl8_3 | ~spl8_39 | ~spl8_131),
% 1.64/0.62    inference(avatar_split_clause,[],[f1302,f1029,f323,f93,f88,f98,f1304])).
% 1.64/0.62  fof(f1304,plain,(
% 1.64/0.62    spl8_168 <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 1.64/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_168])])).
% 1.64/0.62  fof(f98,plain,(
% 1.64/0.62    spl8_4 <=> v1_funct_1(sK3)),
% 1.64/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.64/0.62  fof(f88,plain,(
% 1.64/0.62    spl8_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.64/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.64/0.62  fof(f93,plain,(
% 1.64/0.62    spl8_3 <=> v1_funct_2(sK3,sK1,sK2)),
% 1.64/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.64/0.62  fof(f323,plain,(
% 1.64/0.62    spl8_39 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4))),
% 1.64/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).
% 1.64/0.62  fof(f1302,plain,(
% 1.64/0.62    ~v1_funct_2(sK3,sK1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK3) | k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (~spl8_39 | ~spl8_131)),
% 1.64/0.62    inference(resolution,[],[f1030,f325])).
% 1.64/0.62  fof(f325,plain,(
% 1.64/0.62    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) | ~spl8_39),
% 1.64/0.62    inference(avatar_component_clause,[],[f323])).
% 1.64/0.62  fof(f1030,plain,(
% 1.64/0.62    ( ! [X1] : (~r1_tarski(k2_relset_1(sK1,sK2,X1),k1_relat_1(sK4)) | ~v1_funct_2(X1,sK1,sK2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(X1) | k1_funct_1(k8_funct_2(sK1,sK2,sK0,X1,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(X1,sK5))) ) | ~spl8_131),
% 1.64/0.62    inference(avatar_component_clause,[],[f1029])).
% 1.64/0.62  fof(f1206,plain,(
% 1.64/0.62    spl8_154 | ~spl8_38 | ~spl8_149),
% 1.64/0.62    inference(avatar_split_clause,[],[f1198,f1169,f313,f1203])).
% 1.64/0.62  fof(f1203,plain,(
% 1.64/0.62    spl8_154 <=> k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 1.64/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_154])])).
% 1.64/0.62  fof(f313,plain,(
% 1.64/0.62    spl8_38 <=> ! [X1] : (~r2_hidden(X1,k1_relat_1(sK4)) | k7_partfun1(sK0,sK4,X1) = k1_funct_1(sK4,X1))),
% 1.64/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).
% 1.64/0.62  fof(f1169,plain,(
% 1.64/0.62    spl8_149 <=> r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4))),
% 1.64/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_149])])).
% 1.64/0.62  fof(f1198,plain,(
% 1.64/0.62    k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5)) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (~spl8_38 | ~spl8_149)),
% 1.64/0.62    inference(resolution,[],[f314,f1171])).
% 1.64/0.62  fof(f1171,plain,(
% 1.64/0.62    r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | ~spl8_149),
% 1.64/0.62    inference(avatar_component_clause,[],[f1169])).
% 1.64/0.62  fof(f314,plain,(
% 1.64/0.62    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK4)) | k7_partfun1(sK0,sK4,X1) = k1_funct_1(sK4,X1)) ) | ~spl8_38),
% 1.64/0.62    inference(avatar_component_clause,[],[f313])).
% 1.64/0.62  fof(f1172,plain,(
% 1.64/0.62    spl8_149 | ~spl8_17 | ~spl8_104),
% 1.64/0.62    inference(avatar_split_clause,[],[f1165,f844,f169,f1169])).
% 1.64/0.62  fof(f169,plain,(
% 1.64/0.62    spl8_17 <=> r2_hidden(sK5,sK1)),
% 1.64/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 1.64/0.62  fof(f844,plain,(
% 1.64/0.62    spl8_104 <=> ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4)))),
% 1.64/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_104])])).
% 1.64/0.62  fof(f1165,plain,(
% 1.64/0.62    r2_hidden(k1_funct_1(sK3,sK5),k1_relat_1(sK4)) | (~spl8_17 | ~spl8_104)),
% 1.64/0.62    inference(resolution,[],[f845,f171])).
% 1.64/0.62  fof(f171,plain,(
% 1.64/0.62    r2_hidden(sK5,sK1) | ~spl8_17),
% 1.64/0.62    inference(avatar_component_clause,[],[f169])).
% 1.64/0.62  fof(f845,plain,(
% 1.64/0.62    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4))) ) | ~spl8_104),
% 1.64/0.62    inference(avatar_component_clause,[],[f844])).
% 1.64/0.62  fof(f1082,plain,(
% 1.64/0.62    spl8_103 | spl8_104 | ~spl8_4 | ~spl8_97 | ~spl8_99),
% 1.64/0.62    inference(avatar_split_clause,[],[f1074,f810,f793,f98,f844,f840])).
% 1.64/0.62  fof(f840,plain,(
% 1.64/0.62    spl8_103 <=> k1_xboole_0 = k1_relat_1(sK4)),
% 1.64/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_103])])).
% 1.64/0.62  fof(f793,plain,(
% 1.64/0.62    spl8_97 <=> v1_funct_2(sK3,sK1,k1_relat_1(sK4))),
% 1.64/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_97])])).
% 1.64/0.62  fof(f810,plain,(
% 1.64/0.62    spl8_99 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4))))),
% 1.64/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_99])])).
% 1.64/0.62  fof(f1074,plain,(
% 1.64/0.62    ( ! [X0] : (~v1_funct_2(sK3,sK1,k1_relat_1(sK4)) | ~v1_funct_1(sK3) | ~r2_hidden(X0,sK1) | k1_xboole_0 = k1_relat_1(sK4) | r2_hidden(k1_funct_1(sK3,X0),k1_relat_1(sK4))) ) | ~spl8_99),
% 1.64/0.62    inference(resolution,[],[f812,f71])).
% 1.64/0.62  fof(f71,plain,(
% 1.64/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | r2_hidden(k1_funct_1(X3,X2),X1)) )),
% 1.64/0.62    inference(cnf_transformation,[],[f37])).
% 1.64/0.62  fof(f37,plain,(
% 1.64/0.62    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.64/0.62    inference(flattening,[],[f36])).
% 1.64/0.62  fof(f36,plain,(
% 1.64/0.62    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.64/0.62    inference(ennf_transformation,[],[f15])).
% 1.64/0.62  fof(f15,axiom,(
% 1.64/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),X1) | k1_xboole_0 = X1)))),
% 1.64/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).
% 1.64/0.62  fof(f812,plain,(
% 1.64/0.62    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4)))) | ~spl8_99),
% 1.64/0.62    inference(avatar_component_clause,[],[f810])).
% 1.64/0.62  fof(f1051,plain,(
% 1.64/0.62    spl8_8 | ~spl8_11 | ~spl8_18),
% 1.64/0.62    inference(avatar_split_clause,[],[f1049,f173,f133,f118])).
% 1.64/0.62  fof(f118,plain,(
% 1.64/0.62    spl8_8 <=> k1_xboole_0 = sK1),
% 1.64/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.64/0.62  fof(f133,plain,(
% 1.64/0.62    spl8_11 <=> v1_xboole_0(k1_xboole_0)),
% 1.64/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 1.64/0.62  fof(f173,plain,(
% 1.64/0.62    spl8_18 <=> v1_xboole_0(sK1)),
% 1.64/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 1.64/0.62  fof(f1049,plain,(
% 1.64/0.62    k1_xboole_0 = sK1 | (~spl8_11 | ~spl8_18)),
% 1.64/0.62    inference(resolution,[],[f1042,f219])).
% 1.64/0.62  fof(f219,plain,(
% 1.64/0.62    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) ) | ~spl8_11),
% 1.64/0.62    inference(resolution,[],[f60,f200])).
% 1.64/0.62  fof(f200,plain,(
% 1.64/0.62    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl8_11),
% 1.64/0.62    inference(resolution,[],[f197,f135])).
% 1.64/0.62  fof(f135,plain,(
% 1.64/0.62    v1_xboole_0(k1_xboole_0) | ~spl8_11),
% 1.64/0.62    inference(avatar_component_clause,[],[f133])).
% 1.64/0.62  fof(f197,plain,(
% 1.64/0.62    ( ! [X0,X1] : (~v1_xboole_0(X0) | r1_tarski(X0,X1)) )),
% 1.64/0.62    inference(resolution,[],[f62,f54])).
% 1.64/0.62  fof(f54,plain,(
% 1.64/0.62    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.64/0.62    inference(cnf_transformation,[],[f1])).
% 1.64/0.62  fof(f1,axiom,(
% 1.64/0.62    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.64/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.64/0.62  fof(f62,plain,(
% 1.64/0.62    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.64/0.62    inference(cnf_transformation,[],[f30])).
% 1.64/0.62  fof(f30,plain,(
% 1.64/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.64/0.62    inference(ennf_transformation,[],[f2])).
% 1.64/0.62  fof(f2,axiom,(
% 1.64/0.62    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.64/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.64/0.62  fof(f60,plain,(
% 1.64/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.64/0.62    inference(cnf_transformation,[],[f4])).
% 1.64/0.62  fof(f4,axiom,(
% 1.64/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.64/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.64/0.62  fof(f1042,plain,(
% 1.64/0.62    ( ! [X0] : (r1_tarski(sK1,X0)) ) | ~spl8_18),
% 1.64/0.62    inference(resolution,[],[f175,f197])).
% 1.64/0.62  fof(f175,plain,(
% 1.64/0.62    v1_xboole_0(sK1) | ~spl8_18),
% 1.64/0.62    inference(avatar_component_clause,[],[f173])).
% 1.64/0.62  fof(f1002,plain,(
% 1.64/0.62    spl8_13 | ~spl8_11 | ~spl8_118),
% 1.64/0.62    inference(avatar_split_clause,[],[f999,f917,f133,f148])).
% 1.64/0.62  fof(f148,plain,(
% 1.64/0.62    spl8_13 <=> v1_xboole_0(sK3)),
% 1.64/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 1.64/0.62  fof(f917,plain,(
% 1.64/0.62    spl8_118 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 1.64/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_118])])).
% 1.64/0.62  fof(f999,plain,(
% 1.64/0.62    ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK3) | ~spl8_118),
% 1.64/0.62    inference(resolution,[],[f919,f52])).
% 1.64/0.62  fof(f52,plain,(
% 1.64/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0) | v1_xboole_0(X1)) )),
% 1.64/0.62    inference(cnf_transformation,[],[f23])).
% 1.64/0.62  fof(f23,plain,(
% 1.64/0.62    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.64/0.62    inference(ennf_transformation,[],[f6])).
% 1.64/0.62  fof(f6,axiom,(
% 1.64/0.62    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.64/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.64/0.62  fof(f919,plain,(
% 1.64/0.62    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl8_118),
% 1.64/0.62    inference(avatar_component_clause,[],[f917])).
% 1.64/0.62  fof(f932,plain,(
% 1.64/0.62    spl8_97 | ~spl8_39 | ~spl8_46),
% 1.64/0.62    inference(avatar_split_clause,[],[f927,f369,f323,f793])).
% 1.64/0.62  fof(f369,plain,(
% 1.64/0.62    spl8_46 <=> ! [X0] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),X0) | v1_funct_2(sK3,sK1,X0))),
% 1.64/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).
% 1.64/0.62  fof(f927,plain,(
% 1.64/0.62    v1_funct_2(sK3,sK1,k1_relat_1(sK4)) | (~spl8_39 | ~spl8_46)),
% 1.64/0.62    inference(resolution,[],[f325,f370])).
% 1.64/0.62  fof(f370,plain,(
% 1.64/0.62    ( ! [X0] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),X0) | v1_funct_2(sK3,sK1,X0)) ) | ~spl8_46),
% 1.64/0.62    inference(avatar_component_clause,[],[f369])).
% 1.64/0.62  fof(f931,plain,(
% 1.64/0.62    spl8_99 | ~spl8_39 | ~spl8_49),
% 1.64/0.62    inference(avatar_split_clause,[],[f926,f390,f323,f810])).
% 1.64/0.62  fof(f390,plain,(
% 1.64/0.62    spl8_49 <=> ! [X0] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))))),
% 1.64/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).
% 1.64/0.62  fof(f926,plain,(
% 1.64/0.62    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK4)))) | (~spl8_39 | ~spl8_49)),
% 1.64/0.62    inference(resolution,[],[f325,f391])).
% 1.64/0.62  fof(f391,plain,(
% 1.64/0.62    ( ! [X0] : (~r1_tarski(k2_relset_1(sK1,sK2,sK3),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | ~spl8_49),
% 1.64/0.62    inference(avatar_component_clause,[],[f390])).
% 1.64/0.62  fof(f920,plain,(
% 1.64/0.62    spl8_118 | ~spl8_99 | ~spl8_103),
% 1.64/0.62    inference(avatar_split_clause,[],[f915,f840,f810,f917])).
% 1.64/0.62  fof(f915,plain,(
% 1.64/0.62    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl8_99 | ~spl8_103)),
% 1.64/0.62    inference(forward_demodulation,[],[f888,f78])).
% 1.64/0.62  fof(f78,plain,(
% 1.64/0.62    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.64/0.62    inference(equality_resolution,[],[f66])).
% 1.64/0.62  fof(f66,plain,(
% 1.64/0.62    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.64/0.62    inference(cnf_transformation,[],[f5])).
% 1.64/0.62  fof(f5,axiom,(
% 1.64/0.62    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.64/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.64/0.62  fof(f888,plain,(
% 1.64/0.62    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | (~spl8_99 | ~spl8_103)),
% 1.64/0.62    inference(backward_demodulation,[],[f812,f842])).
% 1.64/0.62  fof(f842,plain,(
% 1.64/0.62    k1_xboole_0 = k1_relat_1(sK4) | ~spl8_103),
% 1.64/0.62    inference(avatar_component_clause,[],[f840])).
% 1.64/0.62  fof(f701,plain,(
% 1.64/0.62    spl8_38 | ~spl8_6 | ~spl8_24 | ~spl8_30),
% 1.64/0.62    inference(avatar_split_clause,[],[f700,f255,f211,f108,f313])).
% 1.64/0.62  fof(f211,plain,(
% 1.64/0.62    spl8_24 <=> v1_relat_1(sK4)),
% 1.64/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 1.64/0.62  fof(f255,plain,(
% 1.64/0.62    spl8_30 <=> v5_relat_1(sK4,sK0)),
% 1.64/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 1.64/0.62  fof(f700,plain,(
% 1.64/0.62    ( ! [X0] : (~v1_relat_1(sK4) | ~v1_funct_1(sK4) | ~r2_hidden(X0,k1_relat_1(sK4)) | k7_partfun1(sK0,sK4,X0) = k1_funct_1(sK4,X0)) ) | ~spl8_30),
% 1.64/0.62    inference(resolution,[],[f257,f57])).
% 1.64/0.62  fof(f57,plain,(
% 1.64/0.62    ( ! [X2,X0,X1] : (~v5_relat_1(X1,X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)) )),
% 1.64/0.62    inference(cnf_transformation,[],[f29])).
% 1.64/0.62  fof(f29,plain,(
% 1.64/0.62    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.64/0.62    inference(flattening,[],[f28])).
% 1.64/0.62  fof(f28,plain,(
% 1.64/0.62    ! [X0,X1] : (! [X2] : (k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.64/0.62    inference(ennf_transformation,[],[f13])).
% 1.64/0.62  fof(f13,axiom,(
% 1.64/0.62    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => k7_partfun1(X0,X1,X2) = k1_funct_1(X1,X2)))),
% 1.64/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_partfun1)).
% 1.64/0.62  fof(f257,plain,(
% 1.64/0.62    v5_relat_1(sK4,sK0) | ~spl8_30),
% 1.64/0.62    inference(avatar_component_clause,[],[f255])).
% 1.64/0.62  fof(f409,plain,(
% 1.64/0.62    spl8_8 | spl8_51 | ~spl8_10),
% 1.64/0.62    inference(avatar_split_clause,[],[f403,f128,f407,f118])).
% 1.64/0.62  fof(f128,plain,(
% 1.64/0.62    spl8_10 <=> m1_subset_1(sK5,sK1)),
% 1.64/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.64/0.62  fof(f403,plain,(
% 1.64/0.62    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | v1_xboole_0(X1) | ~r1_tarski(k2_relset_1(sK1,X1,X0),k1_relset_1(X1,X3,X2)) | k1_xboole_0 = sK1 | k1_funct_1(k8_funct_2(sK1,X1,X3,X0,X2),sK5) = k1_funct_1(X2,k1_funct_1(X0,sK5))) ) | ~spl8_10),
% 1.64/0.62    inference(resolution,[],[f67,f130])).
% 1.64/0.62  fof(f130,plain,(
% 1.64/0.62    m1_subset_1(sK5,sK1) | ~spl8_10),
% 1.64/0.62    inference(avatar_component_clause,[],[f128])).
% 1.64/0.62  fof(f67,plain,(
% 1.64/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | k1_xboole_0 = X1 | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))) )),
% 1.64/0.62    inference(cnf_transformation,[],[f32])).
% 1.64/0.62  fof(f32,plain,(
% 1.64/0.62    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 1.64/0.62    inference(flattening,[],[f31])).
% 1.64/0.62  fof(f31,plain,(
% 1.64/0.62    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 1.64/0.62    inference(ennf_transformation,[],[f14])).
% 1.64/0.62  fof(f14,axiom,(
% 1.64/0.62    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 1.64/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).
% 1.64/0.62  fof(f392,plain,(
% 1.64/0.62    spl8_42 | spl8_49 | ~spl8_4 | ~spl8_3 | ~spl8_2),
% 1.64/0.62    inference(avatar_split_clause,[],[f385,f88,f93,f98,f390,f342])).
% 1.64/0.62  fof(f342,plain,(
% 1.64/0.62    spl8_42 <=> k1_xboole_0 = sK2),
% 1.64/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).
% 1.64/0.62  fof(f385,plain,(
% 1.64/0.62    ( ! [X0] : (~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X0) | k1_xboole_0 = sK2 | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | ~spl8_2),
% 1.64/0.62    inference(resolution,[],[f75,f90])).
% 1.64/0.62  fof(f90,plain,(
% 1.64/0.62    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl8_2),
% 1.64/0.62    inference(avatar_component_clause,[],[f88])).
% 1.64/0.62  fof(f75,plain,(
% 1.64/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | k1_xboole_0 = X1 | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 1.64/0.62    inference(cnf_transformation,[],[f39])).
% 1.64/0.62  fof(f39,plain,(
% 1.64/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.64/0.62    inference(flattening,[],[f38])).
% 1.64/0.62  fof(f38,plain,(
% 1.64/0.62    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.64/0.62    inference(ennf_transformation,[],[f16])).
% 1.64/0.62  fof(f16,axiom,(
% 1.64/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.64/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).
% 1.64/0.62  fof(f371,plain,(
% 1.64/0.62    spl8_42 | spl8_46 | ~spl8_4 | ~spl8_3 | ~spl8_2),
% 1.64/0.62    inference(avatar_split_clause,[],[f364,f88,f93,f98,f369,f342])).
% 1.64/0.62  fof(f364,plain,(
% 1.64/0.62    ( ! [X0] : (~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | ~r1_tarski(k2_relset_1(sK1,sK2,sK3),X0) | k1_xboole_0 = sK2 | v1_funct_2(sK3,sK1,X0)) ) | ~spl8_2),
% 1.64/0.62    inference(resolution,[],[f74,f90])).
% 1.64/0.62  fof(f74,plain,(
% 1.64/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | k1_xboole_0 = X1 | v1_funct_2(X3,X0,X2)) )),
% 1.64/0.62    inference(cnf_transformation,[],[f39])).
% 1.64/0.62  fof(f349,plain,(
% 1.64/0.62    k1_xboole_0 != sK2 | v1_xboole_0(sK2) | ~v1_xboole_0(k1_xboole_0)),
% 1.64/0.62    introduced(theory_tautology_sat_conflict,[])).
% 1.64/0.62  fof(f326,plain,(
% 1.64/0.62    spl8_39 | ~spl8_9 | ~spl8_32),
% 1.64/0.62    inference(avatar_split_clause,[],[f321,f276,f123,f323])).
% 1.64/0.62  fof(f123,plain,(
% 1.64/0.62    spl8_9 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 1.64/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.64/0.62  fof(f321,plain,(
% 1.64/0.62    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relat_1(sK4)) | (~spl8_9 | ~spl8_32)),
% 1.64/0.62    inference(backward_demodulation,[],[f125,f278])).
% 1.64/0.62  fof(f125,plain,(
% 1.64/0.62    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4)) | ~spl8_9),
% 1.64/0.62    inference(avatar_component_clause,[],[f123])).
% 1.64/0.62  fof(f296,plain,(
% 1.64/0.62    ~spl8_13 | ~spl8_3 | spl8_18 | spl8_1 | ~spl8_2),
% 1.64/0.62    inference(avatar_split_clause,[],[f292,f88,f83,f173,f93,f148])).
% 1.64/0.62  fof(f292,plain,(
% 1.64/0.62    v1_xboole_0(sK2) | v1_xboole_0(sK1) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_xboole_0(sK3) | ~spl8_2),
% 1.64/0.62    inference(resolution,[],[f137,f90])).
% 1.64/0.62  fof(f137,plain,(
% 1.64/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0) | ~v1_funct_2(X2,X0,X1) | ~v1_xboole_0(X2)) )),
% 1.64/0.62    inference(global_subsumption,[],[f51,f56])).
% 1.64/0.62  fof(f56,plain,(
% 1.64/0.62    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~v1_xboole_0(X2)) )),
% 1.64/0.62    inference(cnf_transformation,[],[f27])).
% 1.64/0.62  fof(f27,plain,(
% 1.64/0.62    ! [X0,X1] : (! [X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.64/0.62    inference(flattening,[],[f26])).
% 1.64/0.62  fof(f26,plain,(
% 1.64/0.62    ! [X0,X1] : (! [X2] : (((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.64/0.62    inference(ennf_transformation,[],[f12])).
% 1.64/0.62  fof(f12,axiom,(
% 1.64/0.62    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)))))),
% 1.64/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_funct_2)).
% 1.64/0.62  fof(f51,plain,(
% 1.64/0.62    ( ! [X0] : (~v1_xboole_0(X0) | v1_funct_1(X0)) )),
% 1.64/0.62    inference(cnf_transformation,[],[f22])).
% 1.64/0.62  fof(f22,plain,(
% 1.64/0.62    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 1.64/0.62    inference(ennf_transformation,[],[f8])).
% 1.64/0.62  fof(f8,axiom,(
% 1.64/0.62    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 1.64/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).
% 1.64/0.62  fof(f279,plain,(
% 1.64/0.62    spl8_32 | ~spl8_5),
% 1.64/0.62    inference(avatar_split_clause,[],[f267,f103,f276])).
% 1.64/0.62  fof(f267,plain,(
% 1.64/0.62    k1_relset_1(sK2,sK0,sK4) = k1_relat_1(sK4) | ~spl8_5),
% 1.64/0.62    inference(resolution,[],[f69,f105])).
% 1.64/0.62  fof(f105,plain,(
% 1.64/0.62    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) | ~spl8_5),
% 1.64/0.62    inference(avatar_component_clause,[],[f103])).
% 1.64/0.62  fof(f69,plain,(
% 1.64/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.64/0.62    inference(cnf_transformation,[],[f34])).
% 1.64/0.62  fof(f34,plain,(
% 1.64/0.62    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/0.62    inference(ennf_transformation,[],[f11])).
% 1.64/0.62  fof(f11,axiom,(
% 1.64/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.64/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.64/0.62  fof(f258,plain,(
% 1.64/0.62    spl8_30 | ~spl8_5),
% 1.64/0.62    inference(avatar_split_clause,[],[f246,f103,f255])).
% 1.64/0.62  fof(f246,plain,(
% 1.64/0.62    v5_relat_1(sK4,sK0) | ~spl8_5),
% 1.64/0.62    inference(resolution,[],[f70,f105])).
% 1.64/0.62  fof(f70,plain,(
% 1.64/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.64/0.62    inference(cnf_transformation,[],[f35])).
% 1.64/0.62  fof(f35,plain,(
% 1.64/0.62    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/0.62    inference(ennf_transformation,[],[f19])).
% 1.64/0.62  fof(f19,plain,(
% 1.64/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.64/0.62    inference(pure_predicate_removal,[],[f10])).
% 1.64/0.62  fof(f10,axiom,(
% 1.64/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.64/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.64/0.62  fof(f214,plain,(
% 1.64/0.62    spl8_24 | ~spl8_5),
% 1.64/0.62    inference(avatar_split_clause,[],[f202,f103,f211])).
% 1.64/0.62  fof(f202,plain,(
% 1.64/0.62    v1_relat_1(sK4) | ~spl8_5),
% 1.64/0.62    inference(resolution,[],[f68,f105])).
% 1.64/0.62  fof(f68,plain,(
% 1.64/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.64/0.62    inference(cnf_transformation,[],[f33])).
% 1.64/0.62  fof(f33,plain,(
% 1.64/0.62    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/0.62    inference(ennf_transformation,[],[f9])).
% 1.64/0.62  fof(f9,axiom,(
% 1.64/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.64/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.64/0.62  fof(f176,plain,(
% 1.64/0.62    spl8_17 | spl8_18 | ~spl8_10),
% 1.64/0.62    inference(avatar_split_clause,[],[f165,f128,f173,f169])).
% 1.64/0.62  fof(f165,plain,(
% 1.64/0.62    v1_xboole_0(sK1) | r2_hidden(sK5,sK1) | ~spl8_10),
% 1.64/0.62    inference(resolution,[],[f55,f130])).
% 1.64/0.62  fof(f55,plain,(
% 1.64/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.64/0.62    inference(cnf_transformation,[],[f25])).
% 1.64/0.62  fof(f25,plain,(
% 1.64/0.62    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.64/0.62    inference(flattening,[],[f24])).
% 1.64/0.62  fof(f24,plain,(
% 1.64/0.62    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.64/0.62    inference(ennf_transformation,[],[f7])).
% 1.64/0.62  fof(f7,axiom,(
% 1.64/0.62    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.64/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.64/0.62  fof(f136,plain,(
% 1.64/0.62    spl8_11),
% 1.64/0.62    inference(avatar_split_clause,[],[f50,f133])).
% 1.64/0.62  fof(f50,plain,(
% 1.64/0.62    v1_xboole_0(k1_xboole_0)),
% 1.64/0.62    inference(cnf_transformation,[],[f3])).
% 1.64/0.62  fof(f3,axiom,(
% 1.64/0.62    v1_xboole_0(k1_xboole_0)),
% 1.64/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.64/0.62  fof(f131,plain,(
% 1.64/0.62    spl8_10),
% 1.64/0.62    inference(avatar_split_clause,[],[f40,f128])).
% 1.64/0.62  fof(f40,plain,(
% 1.64/0.62    m1_subset_1(sK5,sK1)),
% 1.64/0.62    inference(cnf_transformation,[],[f21])).
% 1.64/0.62  fof(f21,plain,(
% 1.64/0.62    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1 & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2))),
% 1.64/0.62    inference(flattening,[],[f20])).
% 1.64/0.62  fof(f20,plain,(
% 1.64/0.62    ? [X0,X1,X2] : (? [X3] : (? [X4] : (? [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) != k7_partfun1(X0,X4,k1_funct_1(X3,X5)) & k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2))),
% 1.64/0.62    inference(ennf_transformation,[],[f18])).
% 1.64/0.62  fof(f18,negated_conjecture,(
% 1.64/0.62    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 1.64/0.62    inference(negated_conjecture,[],[f17])).
% 1.64/0.62  fof(f17,conjecture,(
% 1.64/0.62    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k7_partfun1(X0,X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 1.64/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_funct_2)).
% 1.64/0.62  fof(f126,plain,(
% 1.64/0.62    spl8_9),
% 1.64/0.62    inference(avatar_split_clause,[],[f41,f123])).
% 1.64/0.62  fof(f41,plain,(
% 1.64/0.62    r1_tarski(k2_relset_1(sK1,sK2,sK3),k1_relset_1(sK2,sK0,sK4))),
% 1.64/0.62    inference(cnf_transformation,[],[f21])).
% 1.64/0.62  fof(f121,plain,(
% 1.64/0.62    ~spl8_8),
% 1.64/0.62    inference(avatar_split_clause,[],[f42,f118])).
% 1.64/0.62  fof(f42,plain,(
% 1.64/0.62    k1_xboole_0 != sK1),
% 1.64/0.62    inference(cnf_transformation,[],[f21])).
% 1.64/0.62  fof(f116,plain,(
% 1.64/0.62    ~spl8_7),
% 1.64/0.62    inference(avatar_split_clause,[],[f43,f113])).
% 1.64/0.62  fof(f113,plain,(
% 1.64/0.62    spl8_7 <=> k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) = k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 1.64/0.62    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.64/0.62  fof(f43,plain,(
% 1.64/0.62    k1_funct_1(k8_funct_2(sK1,sK2,sK0,sK3,sK4),sK5) != k7_partfun1(sK0,sK4,k1_funct_1(sK3,sK5))),
% 1.64/0.62    inference(cnf_transformation,[],[f21])).
% 1.64/0.62  fof(f111,plain,(
% 1.64/0.62    spl8_6),
% 1.64/0.62    inference(avatar_split_clause,[],[f44,f108])).
% 1.64/0.62  fof(f44,plain,(
% 1.64/0.62    v1_funct_1(sK4)),
% 1.64/0.62    inference(cnf_transformation,[],[f21])).
% 1.64/0.62  fof(f106,plain,(
% 1.64/0.62    spl8_5),
% 1.64/0.62    inference(avatar_split_clause,[],[f45,f103])).
% 1.64/0.62  fof(f45,plain,(
% 1.64/0.62    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 1.64/0.62    inference(cnf_transformation,[],[f21])).
% 1.64/0.62  fof(f101,plain,(
% 1.64/0.62    spl8_4),
% 1.64/0.62    inference(avatar_split_clause,[],[f46,f98])).
% 1.64/0.62  fof(f46,plain,(
% 1.64/0.62    v1_funct_1(sK3)),
% 1.64/0.62    inference(cnf_transformation,[],[f21])).
% 1.64/0.62  fof(f96,plain,(
% 1.64/0.62    spl8_3),
% 1.64/0.62    inference(avatar_split_clause,[],[f47,f93])).
% 1.64/0.62  fof(f47,plain,(
% 1.64/0.62    v1_funct_2(sK3,sK1,sK2)),
% 1.64/0.62    inference(cnf_transformation,[],[f21])).
% 1.64/0.62  fof(f91,plain,(
% 1.64/0.62    spl8_2),
% 1.64/0.62    inference(avatar_split_clause,[],[f48,f88])).
% 1.64/0.62  fof(f48,plain,(
% 1.64/0.62    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.64/0.62    inference(cnf_transformation,[],[f21])).
% 1.64/0.62  fof(f86,plain,(
% 1.64/0.62    ~spl8_1),
% 1.64/0.62    inference(avatar_split_clause,[],[f49,f83])).
% 1.64/0.62  fof(f49,plain,(
% 1.64/0.62    ~v1_xboole_0(sK2)),
% 1.64/0.62    inference(cnf_transformation,[],[f21])).
% 1.64/0.62  % SZS output end Proof for theBenchmark
% 1.64/0.62  % (24420)------------------------------
% 1.64/0.62  % (24420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.62  % (24420)Termination reason: Refutation
% 1.64/0.62  
% 1.64/0.62  % (24420)Memory used [KB]: 11641
% 1.64/0.62  % (24420)Time elapsed: 0.169 s
% 1.64/0.62  % (24420)------------------------------
% 1.64/0.62  % (24420)------------------------------
% 1.64/0.62  % (24403)Success in time 0.252 s
%------------------------------------------------------------------------------
