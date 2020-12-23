%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t166_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:35 EDT 2019

% Result     : Theorem 10.95s
% Output     : Refutation 10.95s
% Verified   : 
% Statistics : Number of formulae       :  495 (1033 expanded)
%              Number of leaves         :  119 ( 458 expanded)
%              Depth                    :   17
%              Number of atoms          : 2058 (4170 expanded)
%              Number of equality atoms :  222 ( 455 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f358721,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f218,f225,f232,f239,f249,f263,f267,f275,f282,f320,f332,f359,f360,f367,f386,f459,f466,f543,f552,f556,f636,f670,f700,f704,f722,f748,f807,f817,f829,f854,f862,f1055,f1092,f1175,f1190,f1266,f1306,f1485,f1502,f1616,f1697,f1842,f1850,f2376,f2411,f2536,f3367,f4026,f4373,f4667,f4984,f4985,f5301,f5742,f6047,f6190,f6319,f6458,f8388,f10299,f18116,f61450,f61936,f81979,f83665,f84019,f112759,f126085,f139145,f139577,f142180,f143063,f144034,f144991,f150469,f232884,f358496,f358717])).

fof(f358717,plain,
    ( ~ spl15_120
    | spl15_1883
    | ~ spl15_3968 ),
    inference(avatar_contradiction_clause,[],[f358704])).

fof(f358704,plain,
    ( $false
    | ~ spl15_120
    | ~ spl15_1883
    | ~ spl15_3968 ),
    inference(unit_resulting_resolution,[],[f139576,f853,f358476,f180])).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t166_funct_2.p',t4_subset)).

fof(f358476,plain,
    ( r2_hidden(sK7(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK2))
    | ~ spl15_3968 ),
    inference(avatar_component_clause,[],[f358475])).

fof(f358475,plain,
    ( spl15_3968
  <=> r2_hidden(sK7(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_3968])])).

fof(f853,plain,
    ( m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k5_partfun1(sK0,sK1,sK3)))
    | ~ spl15_120 ),
    inference(avatar_component_clause,[],[f852])).

fof(f852,plain,
    ( spl15_120
  <=> m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k5_partfun1(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_120])])).

fof(f139576,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))
    | ~ spl15_1883 ),
    inference(avatar_component_clause,[],[f139575])).

fof(f139575,plain,
    ( spl15_1883
  <=> ~ m1_subset_1(sK7(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1883])])).

fof(f358496,plain,
    ( spl15_3968
    | ~ spl15_0
    | ~ spl15_18
    | ~ spl15_82
    | spl15_277
    | ~ spl15_3016 ),
    inference(avatar_split_clause,[],[f277888,f232140,f2365,f634,f273,f216,f358475])).

fof(f216,plain,
    ( spl15_0
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_0])])).

fof(f273,plain,
    ( spl15_18
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_18])])).

fof(f634,plain,
    ( spl15_82
  <=> ! [X1,X0,X2] :
        ( o_0_0_xboole_0 = X1
        | r1_partfun1(X2,sK7(X0,X1,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_82])])).

fof(f2365,plain,
    ( spl15_277
  <=> o_0_0_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_277])])).

fof(f232140,plain,
    ( spl15_3016
  <=> ! [X0] :
        ( ~ r1_partfun1(X0,sK7(sK0,sK1,sK2))
        | r2_hidden(sK7(sK0,sK1,sK2),k5_partfun1(sK0,sK1,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_3016])])).

fof(f277888,plain,
    ( r2_hidden(sK7(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK2))
    | ~ spl15_0
    | ~ spl15_18
    | ~ spl15_82
    | ~ spl15_277
    | ~ spl15_3016 ),
    inference(subsumption_resolution,[],[f277887,f2366])).

fof(f2366,plain,
    ( o_0_0_xboole_0 != sK1
    | ~ spl15_277 ),
    inference(avatar_component_clause,[],[f2365])).

fof(f277887,plain,
    ( r2_hidden(sK7(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK2))
    | o_0_0_xboole_0 = sK1
    | ~ spl15_0
    | ~ spl15_18
    | ~ spl15_82
    | ~ spl15_3016 ),
    inference(subsumption_resolution,[],[f277886,f217])).

fof(f217,plain,
    ( v1_funct_1(sK2)
    | ~ spl15_0 ),
    inference(avatar_component_clause,[],[f216])).

fof(f277886,plain,
    ( r2_hidden(sK7(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK2))
    | ~ v1_funct_1(sK2)
    | o_0_0_xboole_0 = sK1
    | ~ spl15_18
    | ~ spl15_82
    | ~ spl15_3016 ),
    inference(subsumption_resolution,[],[f277885,f274])).

fof(f274,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl15_18 ),
    inference(avatar_component_clause,[],[f273])).

fof(f277885,plain,
    ( r2_hidden(sK7(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | o_0_0_xboole_0 = sK1
    | ~ spl15_82
    | ~ spl15_3016 ),
    inference(duplicate_literal_removal,[],[f277881])).

fof(f277881,plain,
    ( r2_hidden(sK7(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | o_0_0_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl15_82
    | ~ spl15_3016 ),
    inference(resolution,[],[f232141,f635])).

fof(f635,plain,
    ( ! [X2,X0,X1] :
        ( r1_partfun1(X2,sK7(X0,X1,X2))
        | o_0_0_xboole_0 = X1
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl15_82 ),
    inference(avatar_component_clause,[],[f634])).

fof(f232141,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(X0,sK7(sK0,sK1,sK2))
        | r2_hidden(sK7(sK0,sK1,sK2),k5_partfun1(sK0,sK1,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X0) )
    | ~ spl15_3016 ),
    inference(avatar_component_clause,[],[f232140])).

fof(f232884,plain,
    ( spl15_3016
    | ~ spl15_0
    | ~ spl15_18
    | spl15_277
    | ~ spl15_420
    | ~ spl15_942 ),
    inference(avatar_split_clause,[],[f138087,f61448,f4982,f2365,f273,f216,f232140])).

fof(f4982,plain,
    ( spl15_420
  <=> m1_subset_1(sK7(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_420])])).

fof(f61448,plain,
    ( spl15_942
  <=> ! [X9,X7,X8,X10,X6] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ v1_funct_1(X6)
        | o_0_0_xboole_0 = X8
        | ~ r1_partfun1(X9,sK7(X7,X8,X6))
        | r2_hidden(sK7(X7,X8,X6),k5_partfun1(X7,X10,X9))
        | ~ m1_subset_1(sK7(X7,X8,X6),k1_zfmisc_1(k2_zfmisc_1(X7,X10)))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X10)))
        | ~ v1_funct_1(X9) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_942])])).

fof(f138087,plain,
    ( ! [X2] :
        ( ~ r1_partfun1(X2,sK7(sK0,sK1,sK2))
        | r2_hidden(sK7(sK0,sK1,sK2),k5_partfun1(sK0,sK1,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X2) )
    | ~ spl15_0
    | ~ spl15_18
    | ~ spl15_277
    | ~ spl15_420
    | ~ spl15_942 ),
    inference(subsumption_resolution,[],[f138086,f274])).

fof(f138086,plain,
    ( ! [X2] :
        ( ~ r1_partfun1(X2,sK7(sK0,sK1,sK2))
        | r2_hidden(sK7(sK0,sK1,sK2),k5_partfun1(sK0,sK1,X2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X2) )
    | ~ spl15_0
    | ~ spl15_277
    | ~ spl15_420
    | ~ spl15_942 ),
    inference(subsumption_resolution,[],[f138085,f2366])).

fof(f138085,plain,
    ( ! [X2] :
        ( o_0_0_xboole_0 = sK1
        | ~ r1_partfun1(X2,sK7(sK0,sK1,sK2))
        | r2_hidden(sK7(sK0,sK1,sK2),k5_partfun1(sK0,sK1,X2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X2) )
    | ~ spl15_0
    | ~ spl15_420
    | ~ spl15_942 ),
    inference(subsumption_resolution,[],[f138033,f217])).

fof(f138033,plain,
    ( ! [X2] :
        ( ~ v1_funct_1(sK2)
        | o_0_0_xboole_0 = sK1
        | ~ r1_partfun1(X2,sK7(sK0,sK1,sK2))
        | r2_hidden(sK7(sK0,sK1,sK2),k5_partfun1(sK0,sK1,X2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X2) )
    | ~ spl15_420
    | ~ spl15_942 ),
    inference(resolution,[],[f4983,f61449])).

fof(f61449,plain,
    ( ! [X6,X10,X8,X7,X9] :
        ( ~ m1_subset_1(sK7(X7,X8,X6),k1_zfmisc_1(k2_zfmisc_1(X7,X10)))
        | ~ v1_funct_1(X6)
        | o_0_0_xboole_0 = X8
        | ~ r1_partfun1(X9,sK7(X7,X8,X6))
        | r2_hidden(sK7(X7,X8,X6),k5_partfun1(X7,X10,X9))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X10)))
        | ~ v1_funct_1(X9) )
    | ~ spl15_942 ),
    inference(avatar_component_clause,[],[f61448])).

fof(f4983,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl15_420 ),
    inference(avatar_component_clause,[],[f4982])).

fof(f150469,plain,
    ( ~ spl15_0
    | ~ spl15_18
    | spl15_277
    | ~ spl15_420
    | ~ spl15_444
    | ~ spl15_942
    | ~ spl15_1900 ),
    inference(avatar_contradiction_clause,[],[f150166])).

fof(f150166,plain,
    ( $false
    | ~ spl15_0
    | ~ spl15_18
    | ~ spl15_277
    | ~ spl15_420
    | ~ spl15_444
    | ~ spl15_942
    | ~ spl15_1900 ),
    inference(unit_resulting_resolution,[],[f217,f217,f2366,f274,f274,f6457,f4983,f144990,f61449])).

fof(f144990,plain,
    ( ! [X0] : ~ r2_hidden(X0,k5_partfun1(sK0,sK1,sK2))
    | ~ spl15_1900 ),
    inference(avatar_component_clause,[],[f144989])).

fof(f144989,plain,
    ( spl15_1900
  <=> ! [X0] : ~ r2_hidden(X0,k5_partfun1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1900])])).

fof(f6457,plain,
    ( r1_partfun1(sK2,sK7(sK0,sK1,sK2))
    | ~ spl15_444 ),
    inference(avatar_component_clause,[],[f6456])).

fof(f6456,plain,
    ( spl15_444
  <=> r1_partfun1(sK2,sK7(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_444])])).

fof(f144991,plain,
    ( spl15_1900
    | ~ spl15_1896 ),
    inference(avatar_split_clause,[],[f144945,f144032,f144989])).

fof(f144032,plain,
    ( spl15_1896
  <=> sP14(k5_partfun1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1896])])).

fof(f144945,plain,
    ( ! [X0] : ~ r2_hidden(X0,k5_partfun1(sK0,sK1,sK2))
    | ~ spl15_1896 ),
    inference(resolution,[],[f144033,f211])).

fof(f211,plain,(
    ! [X0,X1] :
      ( ~ sP14(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(general_splitting,[],[f187,f210_D])).

fof(f210,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | sP14(X1) ) ),
    inference(cnf_transformation,[],[f210_D])).

fof(f210_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ v1_xboole_0(X2)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) )
    <=> ~ sP14(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP14])])).

fof(f187,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t166_funct_2.p',t5_subset)).

fof(f144033,plain,
    ( sP14(k5_partfun1(sK0,sK1,sK2))
    | ~ spl15_1896 ),
    inference(avatar_component_clause,[],[f144032])).

fof(f144034,plain,
    ( spl15_1896
    | ~ spl15_40
    | ~ spl15_1892 ),
    inference(avatar_split_clause,[],[f143986,f143061,f384,f144032])).

fof(f384,plain,
    ( spl15_40
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | sP14(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_40])])).

fof(f143061,plain,
    ( spl15_1892
  <=> m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1892])])).

fof(f143986,plain,
    ( sP14(k5_partfun1(sK0,sK1,sK2))
    | ~ spl15_40
    | ~ spl15_1892 ),
    inference(resolution,[],[f143062,f385])).

fof(f385,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | sP14(X0) )
    | ~ spl15_40 ),
    inference(avatar_component_clause,[],[f384])).

fof(f143062,plain,
    ( m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl15_1892 ),
    inference(avatar_component_clause,[],[f143061])).

fof(f143063,plain,
    ( spl15_1892
    | ~ spl15_1888 ),
    inference(avatar_split_clause,[],[f143042,f142178,f143061])).

fof(f142178,plain,
    ( spl15_1888
  <=> r1_tarski(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1888])])).

fof(f143042,plain,
    ( m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl15_1888 ),
    inference(resolution,[],[f142179,f148])).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t166_funct_2.p',t3_subset)).

fof(f142179,plain,
    ( r1_tarski(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)
    | ~ spl15_1888 ),
    inference(avatar_component_clause,[],[f142178])).

fof(f142180,plain,
    ( spl15_1888
    | ~ spl15_36
    | ~ spl15_1878 ),
    inference(avatar_split_clause,[],[f142143,f139143,f365,f142178])).

fof(f365,plain,
    ( spl15_36
  <=> r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_36])])).

fof(f139143,plain,
    ( spl15_1878
  <=> k5_partfun1(sK0,sK1,sK3) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1878])])).

fof(f142143,plain,
    ( r1_tarski(k5_partfun1(sK0,sK1,sK2),o_0_0_xboole_0)
    | ~ spl15_36
    | ~ spl15_1878 ),
    inference(backward_demodulation,[],[f139144,f366])).

fof(f366,plain,
    ( r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))
    | ~ spl15_36 ),
    inference(avatar_component_clause,[],[f365])).

fof(f139144,plain,
    ( k5_partfun1(sK0,sK1,sK3) = o_0_0_xboole_0
    | ~ spl15_1878 ),
    inference(avatar_component_clause,[],[f139143])).

fof(f139577,plain,
    ( ~ spl15_1883
    | spl15_1445
    | spl15_1743 ),
    inference(avatar_split_clause,[],[f139570,f130332,f112757,f139575])).

fof(f112757,plain,
    ( spl15_1445
  <=> ~ r2_hidden(sK7(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1445])])).

fof(f130332,plain,
    ( spl15_1743
  <=> ~ v1_xboole_0(k5_partfun1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1743])])).

fof(f139570,plain,
    ( ~ m1_subset_1(sK7(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))
    | ~ spl15_1445
    | ~ spl15_1743 ),
    inference(subsumption_resolution,[],[f139569,f130333])).

fof(f130333,plain,
    ( ~ v1_xboole_0(k5_partfun1(sK0,sK1,sK3))
    | ~ spl15_1743 ),
    inference(avatar_component_clause,[],[f130332])).

fof(f139569,plain,
    ( v1_xboole_0(k5_partfun1(sK0,sK1,sK3))
    | ~ m1_subset_1(sK7(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))
    | ~ spl15_1445 ),
    inference(resolution,[],[f112758,f144])).

fof(f144,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t166_funct_2.p',t2_subset)).

fof(f112758,plain,
    ( ~ r2_hidden(sK7(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))
    | ~ spl15_1445 ),
    inference(avatar_component_clause,[],[f112757])).

fof(f139145,plain,
    ( spl15_1878
    | ~ spl15_14
    | ~ spl15_1742 ),
    inference(avatar_split_clause,[],[f139026,f130335,f261,f139143])).

fof(f261,plain,
    ( spl15_14
  <=> ! [X0] :
        ( o_0_0_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_14])])).

fof(f130335,plain,
    ( spl15_1742
  <=> v1_xboole_0(k5_partfun1(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1742])])).

fof(f139026,plain,
    ( k5_partfun1(sK0,sK1,sK3) = o_0_0_xboole_0
    | ~ spl15_14
    | ~ spl15_1742 ),
    inference(resolution,[],[f130336,f262])).

fof(f262,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl15_14 ),
    inference(avatar_component_clause,[],[f261])).

fof(f130336,plain,
    ( v1_xboole_0(k5_partfun1(sK0,sK1,sK3))
    | ~ spl15_1742 ),
    inference(avatar_component_clause,[],[f130335])).

fof(f126085,plain,
    ( ~ spl15_0
    | ~ spl15_2
    | ~ spl15_18
    | ~ spl15_20
    | spl15_277
    | ~ spl15_420
    | ~ spl15_444
    | spl15_535
    | ~ spl15_944
    | ~ spl15_1442 ),
    inference(avatar_contradiction_clause,[],[f126082])).

fof(f126082,plain,
    ( $false
    | ~ spl15_0
    | ~ spl15_2
    | ~ spl15_18
    | ~ spl15_20
    | ~ spl15_277
    | ~ spl15_420
    | ~ spl15_444
    | ~ spl15_535
    | ~ spl15_944
    | ~ spl15_1442 ),
    inference(unit_resulting_resolution,[],[f217,f217,f224,f7775,f2366,f274,f6457,f281,f274,f4983,f112752,f61935])).

fof(f61935,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(sK7(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X5)))
        | ~ v1_funct_1(X0)
        | o_0_0_xboole_0 = X2
        | r1_partfun1(X3,X4)
        | ~ r1_partfun1(X4,sK7(X1,X2,X0))
        | ~ r1_partfun1(X3,sK7(X1,X2,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))
        | ~ v1_funct_1(X3) )
    | ~ spl15_944 ),
    inference(avatar_component_clause,[],[f61934])).

fof(f61934,plain,
    ( spl15_944
  <=> ! [X1,X3,X5,X0,X2,X4] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | o_0_0_xboole_0 = X2
        | r1_partfun1(X3,X4)
        | ~ r1_partfun1(X4,sK7(X1,X2,X0))
        | ~ r1_partfun1(X3,sK7(X1,X2,X0))
        | ~ m1_subset_1(sK7(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X5)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))
        | ~ v1_funct_1(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_944])])).

fof(f112752,plain,
    ( r1_partfun1(sK3,sK7(sK0,sK1,sK2))
    | ~ spl15_1442 ),
    inference(avatar_component_clause,[],[f112751])).

fof(f112751,plain,
    ( spl15_1442
  <=> r1_partfun1(sK3,sK7(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1442])])).

fof(f281,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl15_20 ),
    inference(avatar_component_clause,[],[f280])).

fof(f280,plain,
    ( spl15_20
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_20])])).

fof(f7775,plain,
    ( ~ r1_partfun1(sK2,sK3)
    | ~ spl15_535 ),
    inference(avatar_component_clause,[],[f7774])).

fof(f7774,plain,
    ( spl15_535
  <=> ~ r1_partfun1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_535])])).

fof(f224,plain,
    ( v1_funct_1(sK3)
    | ~ spl15_2 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl15_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_2])])).

fof(f112759,plain,
    ( spl15_1442
    | ~ spl15_1445
    | ~ spl15_278
    | ~ spl15_426
    | ~ spl15_574 ),
    inference(avatar_split_clause,[],[f8441,f8128,f5740,f2374,f112757,f112751])).

fof(f2374,plain,
    ( spl15_278
  <=> v1_funct_1(sK7(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_278])])).

fof(f5740,plain,
    ( spl15_426
  <=> v1_relat_1(sK7(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_426])])).

fof(f8128,plain,
    ( spl15_574
  <=> ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(X0,k5_partfun1(sK0,sK1,sK3))
        | r1_partfun1(sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_574])])).

fof(f8441,plain,
    ( ~ r2_hidden(sK7(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))
    | r1_partfun1(sK3,sK7(sK0,sK1,sK2))
    | ~ spl15_278
    | ~ spl15_426
    | ~ spl15_574 ),
    inference(subsumption_resolution,[],[f8439,f5741])).

fof(f5741,plain,
    ( v1_relat_1(sK7(sK0,sK1,sK2))
    | ~ spl15_426 ),
    inference(avatar_component_clause,[],[f5740])).

fof(f8439,plain,
    ( ~ v1_relat_1(sK7(sK0,sK1,sK2))
    | ~ r2_hidden(sK7(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))
    | r1_partfun1(sK3,sK7(sK0,sK1,sK2))
    | ~ spl15_278
    | ~ spl15_574 ),
    inference(resolution,[],[f8129,f2375])).

fof(f2375,plain,
    ( v1_funct_1(sK7(sK0,sK1,sK2))
    | ~ spl15_278 ),
    inference(avatar_component_clause,[],[f2374])).

fof(f8129,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(X0,k5_partfun1(sK0,sK1,sK3))
        | r1_partfun1(sK3,X0) )
    | ~ spl15_574 ),
    inference(avatar_component_clause,[],[f8128])).

fof(f84019,plain,
    ( ~ spl15_0
    | ~ spl15_2
    | ~ spl15_26
    | ~ spl15_28
    | ~ spl15_70
    | spl15_101
    | ~ spl15_1182 ),
    inference(avatar_contradiction_clause,[],[f84018])).

fof(f84018,plain,
    ( $false
    | ~ spl15_0
    | ~ spl15_2
    | ~ spl15_26
    | ~ spl15_28
    | ~ spl15_70
    | ~ spl15_101
    | ~ spl15_1182 ),
    inference(subsumption_resolution,[],[f84017,f331])).

fof(f331,plain,
    ( v1_relat_1(sK3)
    | ~ spl15_28 ),
    inference(avatar_component_clause,[],[f330])).

fof(f330,plain,
    ( spl15_28
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_28])])).

fof(f84017,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl15_0
    | ~ spl15_2
    | ~ spl15_26
    | ~ spl15_70
    | ~ spl15_101
    | ~ spl15_1182 ),
    inference(subsumption_resolution,[],[f84016,f224])).

fof(f84016,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl15_0
    | ~ spl15_26
    | ~ spl15_70
    | ~ spl15_101
    | ~ spl15_1182 ),
    inference(subsumption_resolution,[],[f84015,f319])).

fof(f319,plain,
    ( v1_relat_1(sK2)
    | ~ spl15_26 ),
    inference(avatar_component_clause,[],[f318])).

fof(f318,plain,
    ( spl15_26
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_26])])).

fof(f84015,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl15_0
    | ~ spl15_70
    | ~ spl15_101
    | ~ spl15_1182 ),
    inference(subsumption_resolution,[],[f84014,f217])).

fof(f84014,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl15_70
    | ~ spl15_101
    | ~ spl15_1182 ),
    inference(subsumption_resolution,[],[f84013,f542])).

fof(f542,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK2))
    | ~ spl15_70 ),
    inference(avatar_component_clause,[],[f541])).

fof(f541,plain,
    ( spl15_70
  <=> r1_tarski(k1_relat_1(sK3),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_70])])).

fof(f84013,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl15_101
    | ~ spl15_1182 ),
    inference(subsumption_resolution,[],[f84011,f721])).

fof(f721,plain,
    ( ~ r1_tarski(sK3,sK2)
    | ~ spl15_101 ),
    inference(avatar_component_clause,[],[f720])).

fof(f720,plain,
    ( spl15_101
  <=> ~ r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_101])])).

fof(f84011,plain,
    ( r1_tarski(sK3,sK2)
    | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl15_1182 ),
    inference(trivial_inequality_removal,[],[f84010])).

fof(f84010,plain,
    ( k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | r1_tarski(sK3,sK2)
    | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl15_1182 ),
    inference(superposition,[],[f131,f83664])).

fof(f83664,plain,
    ( k1_funct_1(sK2,sK4(sK3,sK2)) = k1_funct_1(sK3,sK4(sK3,sK2))
    | ~ spl15_1182 ),
    inference(avatar_component_clause,[],[f83663])).

fof(f83663,plain,
    ( spl15_1182
  <=> k1_funct_1(sK2,sK4(sK3,sK2)) = k1_funct_1(sK3,sK4(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1182])])).

fof(f131,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | r1_tarski(X0,X1)
      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tarski(X0,X1)
              | ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
                & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
              | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
            & ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
              | ~ r1_tarski(X0,X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f94,f95])).

fof(f95,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f94,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tarski(X0,X1)
              | ? [X2] :
                  ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
                  & r2_hidden(X2,k1_relat_1(X0)) )
              | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
            & ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
              | ~ r1_tarski(X0,X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f93])).

fof(f93,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tarski(X0,X1)
              | ? [X2] :
                  ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
                  & r2_hidden(X2,k1_relat_1(X0)) )
              | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
            & ( ( ! [X2] :
                    ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                    | ~ r2_hidden(X2,k1_relat_1(X0)) )
                & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
              | ~ r1_tarski(X0,X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f92])).

fof(f92,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tarski(X0,X1)
              | ? [X2] :
                  ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
                  & r2_hidden(X2,k1_relat_1(X0)) )
              | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
            & ( ( ! [X2] :
                    ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                    | ~ r2_hidden(X2,k1_relat_1(X0)) )
                & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
              | ~ r1_tarski(X0,X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
          <=> ( ! [X2] :
                  ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                  | ~ r2_hidden(X2,k1_relat_1(X0)) )
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
          <=> ( ! [X2] :
                  ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                  | ~ r2_hidden(X2,k1_relat_1(X0)) )
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( r1_tarski(X0,X1)
          <=> ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t166_funct_2.p',t8_grfunc_1)).

fof(f83665,plain,
    ( spl15_1182
    | ~ spl15_102
    | ~ spl15_1160 ),
    inference(avatar_split_clause,[],[f82984,f81977,f746,f83663])).

fof(f746,plain,
    ( spl15_102
  <=> r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_102])])).

fof(f81977,plain,
    ( spl15_1160
  <=> ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK3))
        | k1_funct_1(sK2,X1) = k1_funct_1(sK3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1160])])).

fof(f82984,plain,
    ( k1_funct_1(sK2,sK4(sK3,sK2)) = k1_funct_1(sK3,sK4(sK3,sK2))
    | ~ spl15_102
    | ~ spl15_1160 ),
    inference(resolution,[],[f81978,f747])).

fof(f747,plain,
    ( r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3))
    | ~ spl15_102 ),
    inference(avatar_component_clause,[],[f746])).

fof(f81978,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK3))
        | k1_funct_1(sK2,X1) = k1_funct_1(sK3,X1) )
    | ~ spl15_1160 ),
    inference(avatar_component_clause,[],[f81977])).

fof(f81979,plain,
    ( spl15_1160
    | spl15_401
    | ~ spl15_686
    | ~ spl15_828 ),
    inference(avatar_split_clause,[],[f81958,f17542,f10297,f3898,f81977])).

fof(f3898,plain,
    ( spl15_401
  <=> ~ v1_xboole_0(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_401])])).

fof(f10297,plain,
    ( spl15_686
  <=> ! [X1] :
        ( ~ r2_hidden(X1,k3_xboole_0(k1_relat_1(sK2),k1_relat_1(sK3)))
        | k1_funct_1(sK2,X1) = k1_funct_1(sK3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_686])])).

fof(f17542,plain,
    ( spl15_828
  <=> ! [X9,X10] :
        ( k3_xboole_0(X9,X10) = k1_relat_1(sK3)
        | r2_hidden(sK11(X9,X10,k1_relat_1(sK3)),X9)
        | m1_subset_1(sK11(X9,X10,k1_relat_1(sK3)),k1_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_828])])).

fof(f81958,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK3))
        | k1_funct_1(sK2,X1) = k1_funct_1(sK3,X1) )
    | ~ spl15_401
    | ~ spl15_686
    | ~ spl15_828 ),
    inference(backward_demodulation,[],[f80611,f10298])).

fof(f10298,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k3_xboole_0(k1_relat_1(sK2),k1_relat_1(sK3)))
        | k1_funct_1(sK2,X1) = k1_funct_1(sK3,X1) )
    | ~ spl15_686 ),
    inference(avatar_component_clause,[],[f10297])).

fof(f80611,plain,
    ( k3_xboole_0(k1_relat_1(sK2),k1_relat_1(sK3)) = k1_relat_1(sK3)
    | ~ spl15_401
    | ~ spl15_828 ),
    inference(subsumption_resolution,[],[f80610,f987])).

fof(f987,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK11(X0,X1,X1),X0)
      | k3_xboole_0(X0,X1) = X1 ) ),
    inference(subsumption_resolution,[],[f986,f185])).

fof(f185,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK11(X0,X1,X2),X1)
      | r2_hidden(sK11(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f116])).

fof(f116,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK11(X0,X1,X2),X1)
            | ~ r2_hidden(sK11(X0,X1,X2),X0)
            | ~ r2_hidden(sK11(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK11(X0,X1,X2),X1)
              & r2_hidden(sK11(X0,X1,X2),X0) )
            | r2_hidden(sK11(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f114,f115])).

fof(f115,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK11(X0,X1,X2),X1)
          | ~ r2_hidden(sK11(X0,X1,X2),X0)
          | ~ r2_hidden(sK11(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK11(X0,X1,X2),X1)
            & r2_hidden(sK11(X0,X1,X2),X0) )
          | r2_hidden(sK11(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f114,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f113])).

fof(f113,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f112])).

fof(f112,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t166_funct_2.p',d4_xboole_0)).

fof(f986,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X1
      | ~ r2_hidden(sK11(X0,X1,X1),X1)
      | ~ r2_hidden(sK11(X0,X1,X1),X0) ) ),
    inference(duplicate_literal_removal,[],[f975])).

fof(f975,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X1
      | ~ r2_hidden(sK11(X0,X1,X1),X1)
      | ~ r2_hidden(sK11(X0,X1,X1),X0)
      | k3_xboole_0(X0,X1) = X1 ) ),
    inference(resolution,[],[f619,f186])).

fof(f186,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK11(X0,X1,X2),X2)
      | ~ r2_hidden(sK11(X0,X1,X2),X1)
      | ~ r2_hidden(sK11(X0,X1,X2),X0)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f116])).

fof(f619,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK11(X0,X1,X1),X1)
      | k3_xboole_0(X0,X1) = X1 ) ),
    inference(factoring,[],[f185])).

fof(f80610,plain,
    ( k3_xboole_0(k1_relat_1(sK2),k1_relat_1(sK3)) = k1_relat_1(sK3)
    | r2_hidden(sK11(k1_relat_1(sK2),k1_relat_1(sK3),k1_relat_1(sK3)),k1_relat_1(sK2))
    | ~ spl15_401
    | ~ spl15_828 ),
    inference(subsumption_resolution,[],[f80586,f3899])).

fof(f3899,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK2))
    | ~ spl15_401 ),
    inference(avatar_component_clause,[],[f3898])).

fof(f80586,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | k3_xboole_0(k1_relat_1(sK2),k1_relat_1(sK3)) = k1_relat_1(sK3)
    | r2_hidden(sK11(k1_relat_1(sK2),k1_relat_1(sK3),k1_relat_1(sK3)),k1_relat_1(sK2))
    | ~ spl15_828 ),
    inference(duplicate_literal_removal,[],[f80507])).

fof(f80507,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | k3_xboole_0(k1_relat_1(sK2),k1_relat_1(sK3)) = k1_relat_1(sK3)
    | r2_hidden(sK11(k1_relat_1(sK2),k1_relat_1(sK3),k1_relat_1(sK3)),k1_relat_1(sK2))
    | k3_xboole_0(k1_relat_1(sK2),k1_relat_1(sK3)) = k1_relat_1(sK3)
    | ~ spl15_828 ),
    inference(resolution,[],[f7478,f17543])).

fof(f17543,plain,
    ( ! [X10,X9] :
        ( r2_hidden(sK11(X9,X10,k1_relat_1(sK3)),X9)
        | m1_subset_1(sK11(X9,X10,k1_relat_1(sK3)),k1_relat_1(sK2))
        | k3_xboole_0(X9,X10) = k1_relat_1(sK3) )
    | ~ spl15_828 ),
    inference(avatar_component_clause,[],[f17542])).

fof(f7478,plain,(
    ! [X43,X42] :
      ( ~ m1_subset_1(sK11(X42,X43,X43),X42)
      | v1_xboole_0(X42)
      | k3_xboole_0(X42,X43) = X43 ) ),
    inference(resolution,[],[f987,f144])).

fof(f61936,plain,
    ( spl15_944
    | ~ spl15_74
    | ~ spl15_318 ),
    inference(avatar_split_clause,[],[f3380,f3365,f554,f61934])).

fof(f554,plain,
    ( spl15_74
  <=> ! [X1,X0,X2] :
        ( o_0_0_xboole_0 = X1
        | v1_funct_1(sK7(X0,X1,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_74])])).

fof(f3365,plain,
    ( spl15_318
  <=> ! [X1,X0,X2] :
        ( o_0_0_xboole_0 = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ v1_funct_1(X1)
        | v1_partfun1(sK7(X2,X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_318])])).

fof(f3380,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | o_0_0_xboole_0 = X2
        | r1_partfun1(X3,X4)
        | ~ r1_partfun1(X4,sK7(X1,X2,X0))
        | ~ r1_partfun1(X3,sK7(X1,X2,X0))
        | ~ m1_subset_1(sK7(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X5)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))
        | ~ v1_funct_1(X3) )
    | ~ spl15_74
    | ~ spl15_318 ),
    inference(subsumption_resolution,[],[f3378,f555])).

fof(f555,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X2)
        | v1_funct_1(sK7(X0,X1,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | o_0_0_xboole_0 = X1 )
    | ~ spl15_74 ),
    inference(avatar_component_clause,[],[f554])).

fof(f3378,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | o_0_0_xboole_0 = X2
        | r1_partfun1(X3,X4)
        | ~ r1_partfun1(X4,sK7(X1,X2,X0))
        | ~ r1_partfun1(X3,sK7(X1,X2,X0))
        | ~ m1_subset_1(sK7(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X5)))
        | ~ v1_funct_1(sK7(X1,X2,X0))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X5)))
        | ~ v1_funct_1(X3) )
    | ~ spl15_318 ),
    inference(resolution,[],[f3366,f167])).

fof(f167,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_partfun1(X4,X0)
      | r1_partfun1(X2,X3)
      | ~ r1_partfun1(X3,X4)
      | ~ r1_partfun1(X2,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( r1_partfun1(X2,X3)
              | ~ v1_partfun1(X4,X0)
              | ~ r1_partfun1(X3,X4)
              | ~ r1_partfun1(X2,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( r1_partfun1(X2,X3)
              | ~ v1_partfun1(X4,X0)
              | ~ r1_partfun1(X3,X4)
              | ~ r1_partfun1(X2,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_1(X4) )
             => ( ( v1_partfun1(X4,X0)
                  & r1_partfun1(X3,X4)
                  & r1_partfun1(X2,X4) )
               => r1_partfun1(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t166_funct_2.p',t158_partfun1)).

fof(f3366,plain,
    ( ! [X2,X0,X1] :
        ( v1_partfun1(sK7(X2,X0,X1),X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ v1_funct_1(X1)
        | o_0_0_xboole_0 = X0 )
    | ~ spl15_318 ),
    inference(avatar_component_clause,[],[f3365])).

fof(f61450,plain,
    ( spl15_942
    | ~ spl15_74
    | ~ spl15_318 ),
    inference(avatar_split_clause,[],[f3381,f3365,f554,f61448])).

fof(f3381,plain,
    ( ! [X6,X10,X8,X7,X9] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ v1_funct_1(X6)
        | o_0_0_xboole_0 = X8
        | ~ r1_partfun1(X9,sK7(X7,X8,X6))
        | r2_hidden(sK7(X7,X8,X6),k5_partfun1(X7,X10,X9))
        | ~ m1_subset_1(sK7(X7,X8,X6),k1_zfmisc_1(k2_zfmisc_1(X7,X10)))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X10)))
        | ~ v1_funct_1(X9) )
    | ~ spl15_74
    | ~ spl15_318 ),
    inference(subsumption_resolution,[],[f3379,f555])).

fof(f3379,plain,
    ( ! [X6,X10,X8,X7,X9] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ v1_funct_1(X6)
        | o_0_0_xboole_0 = X8
        | ~ r1_partfun1(X9,sK7(X7,X8,X6))
        | r2_hidden(sK7(X7,X8,X6),k5_partfun1(X7,X10,X9))
        | ~ m1_subset_1(sK7(X7,X8,X6),k1_zfmisc_1(k2_zfmisc_1(X7,X10)))
        | ~ v1_funct_1(sK7(X7,X8,X6))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X10)))
        | ~ v1_funct_1(X9) )
    | ~ spl15_318 ),
    inference(resolution,[],[f3366,f197])).

fof(f197,plain,(
    ! [X2,X0,X8,X1] :
      ( ~ v1_partfun1(X8,X0)
      | ~ r1_partfun1(X2,X8)
      | r2_hidden(X8,k5_partfun1(X0,X1,X2))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f196])).

fof(f196,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,X3)
      | ~ r1_partfun1(X2,X8)
      | ~ v1_partfun1(X8,X0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X8)
      | k5_partfun1(X0,X1,X2) != X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f173])).

fof(f173,plain,(
    ! [X2,X0,X8,X7,X3,X1] :
      ( r2_hidden(X7,X3)
      | ~ r1_partfun1(X2,X8)
      | ~ v1_partfun1(X8,X0)
      | X7 != X8
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X8)
      | k5_partfun1(X0,X1,X2) != X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f111])).

fof(f111,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ( ( ! [X5] :
                    ( ~ r1_partfun1(X2,X5)
                    | ~ v1_partfun1(X5,X0)
                    | sK8(X0,X1,X2,X3) != X5
                    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    | ~ v1_funct_1(X5) )
                | ~ r2_hidden(sK8(X0,X1,X2,X3),X3) )
              & ( ( r1_partfun1(X2,sK9(X0,X1,X2,X3))
                  & v1_partfun1(sK9(X0,X1,X2,X3),X0)
                  & sK8(X0,X1,X2,X3) = sK9(X0,X1,X2,X3)
                  & m1_subset_1(sK9(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(sK9(X0,X1,X2,X3)) )
                | r2_hidden(sK8(X0,X1,X2,X3),X3) ) ) )
          & ( ! [X7] :
                ( ( r2_hidden(X7,X3)
                  | ! [X8] :
                      ( ~ r1_partfun1(X2,X8)
                      | ~ v1_partfun1(X8,X0)
                      | X7 != X8
                      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_1(X8) ) )
                & ( ( r1_partfun1(X2,sK10(X0,X1,X2,X7))
                    & v1_partfun1(sK10(X0,X1,X2,X7),X0)
                    & sK10(X0,X1,X2,X7) = X7
                    & m1_subset_1(sK10(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_1(sK10(X0,X1,X2,X7)) )
                  | ~ r2_hidden(X7,X3) ) )
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f107,f110,f109,f108])).

fof(f108,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r1_partfun1(X2,X5)
                | ~ v1_partfun1(X5,X0)
                | X4 != X5
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                | ~ v1_funct_1(X5) )
            | ~ r2_hidden(X4,X3) )
          & ( ? [X6] :
                ( r1_partfun1(X2,X6)
                & v1_partfun1(X6,X0)
                & X4 = X6
                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_1(X6) )
            | r2_hidden(X4,X3) ) )
     => ( ( ! [X5] :
              ( ~ r1_partfun1(X2,X5)
              | ~ v1_partfun1(X5,X0)
              | sK8(X0,X1,X2,X3) != X5
              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_1(X5) )
          | ~ r2_hidden(sK8(X0,X1,X2,X3),X3) )
        & ( ? [X6] :
              ( r1_partfun1(X2,X6)
              & v1_partfun1(X6,X0)
              & sK8(X0,X1,X2,X3) = X6
              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X6) )
          | r2_hidden(sK8(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f109,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r1_partfun1(X2,X6)
          & v1_partfun1(X6,X0)
          & X4 = X6
          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X6) )
     => ( r1_partfun1(X2,sK9(X0,X1,X2,X3))
        & v1_partfun1(sK9(X0,X1,X2,X3),X0)
        & sK9(X0,X1,X2,X3) = X4
        & m1_subset_1(sK9(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(sK9(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f110,plain,(
    ! [X7,X2,X1,X0] :
      ( ? [X9] :
          ( r1_partfun1(X2,X9)
          & v1_partfun1(X9,X0)
          & X7 = X9
          & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X9) )
     => ( r1_partfun1(X2,sK10(X0,X1,X2,X7))
        & v1_partfun1(sK10(X0,X1,X2,X7),X0)
        & sK10(X0,X1,X2,X7) = X7
        & m1_subset_1(sK10(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(sK10(X0,X1,X2,X7)) ) ) ),
    introduced(choice_axiom,[])).

fof(f107,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ? [X4] :
                ( ( ! [X5] :
                      ( ~ r1_partfun1(X2,X5)
                      | ~ v1_partfun1(X5,X0)
                      | X4 != X5
                      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_1(X5) )
                  | ~ r2_hidden(X4,X3) )
                & ( ? [X6] :
                      ( r1_partfun1(X2,X6)
                      & v1_partfun1(X6,X0)
                      & X4 = X6
                      & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_1(X6) )
                  | r2_hidden(X4,X3) ) ) )
          & ( ! [X7] :
                ( ( r2_hidden(X7,X3)
                  | ! [X8] :
                      ( ~ r1_partfun1(X2,X8)
                      | ~ v1_partfun1(X8,X0)
                      | X7 != X8
                      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_1(X8) ) )
                & ( ? [X9] :
                      ( r1_partfun1(X2,X9)
                      & v1_partfun1(X9,X0)
                      & X7 = X9
                      & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_1(X9) )
                  | ~ r2_hidden(X7,X3) ) )
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(rectify,[],[f106])).

fof(f106,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ? [X4] :
                ( ( ! [X5] :
                      ( ~ r1_partfun1(X2,X5)
                      | ~ v1_partfun1(X5,X0)
                      | X4 != X5
                      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_1(X5) )
                  | ~ r2_hidden(X4,X3) )
                & ( ? [X5] :
                      ( r1_partfun1(X2,X5)
                      & v1_partfun1(X5,X0)
                      & X4 = X5
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_1(X5) )
                  | r2_hidden(X4,X3) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X3)
                  | ! [X5] :
                      ( ~ r1_partfun1(X2,X5)
                      | ~ v1_partfun1(X5,X0)
                      | X4 != X5
                      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      | ~ v1_funct_1(X5) ) )
                & ( ? [X5] :
                      ( r1_partfun1(X2,X5)
                      & v1_partfun1(X5,X0)
                      & X4 = X5
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_1(X5) )
                  | ~ r2_hidden(X4,X3) ) )
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f82])).

fof(f82,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t166_funct_2.p',d7_partfun1)).

fof(f18116,plain,
    ( spl15_828
    | ~ spl15_72 ),
    inference(avatar_split_clause,[],[f6075,f550,f17542])).

fof(f550,plain,
    ( spl15_72
  <=> m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_72])])).

fof(f6075,plain,
    ( ! [X10,X9] :
        ( k3_xboole_0(X9,X10) = k1_relat_1(sK3)
        | r2_hidden(sK11(X9,X10,k1_relat_1(sK3)),X9)
        | m1_subset_1(sK11(X9,X10,k1_relat_1(sK3)),k1_relat_1(sK2)) )
    | ~ spl15_72 ),
    inference(resolution,[],[f551,f589])).

fof(f589,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(X7))
      | k3_xboole_0(X4,X5) = X6
      | r2_hidden(sK11(X4,X5,X6),X4)
      | m1_subset_1(sK11(X4,X5,X6),X7) ) ),
    inference(resolution,[],[f184,f180])).

fof(f184,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK11(X0,X1,X2),X0)
      | r2_hidden(sK11(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f116])).

fof(f551,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_relat_1(sK2)))
    | ~ spl15_72 ),
    inference(avatar_component_clause,[],[f550])).

fof(f10299,plain,
    ( spl15_686
    | ~ spl15_2
    | ~ spl15_28
    | ~ spl15_244
    | ~ spl15_534 ),
    inference(avatar_split_clause,[],[f10295,f7777,f1695,f330,f223,f10297])).

fof(f1695,plain,
    ( spl15_244
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k3_xboole_0(k1_relat_1(sK2),k1_relat_1(X1)))
        | ~ r1_partfun1(sK2,X1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | k1_funct_1(sK2,X0) = k1_funct_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_244])])).

fof(f7777,plain,
    ( spl15_534
  <=> r1_partfun1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_534])])).

fof(f10295,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k3_xboole_0(k1_relat_1(sK2),k1_relat_1(sK3)))
        | k1_funct_1(sK2,X1) = k1_funct_1(sK3,X1) )
    | ~ spl15_2
    | ~ spl15_28
    | ~ spl15_244
    | ~ spl15_534 ),
    inference(subsumption_resolution,[],[f1709,f7778])).

fof(f7778,plain,
    ( r1_partfun1(sK2,sK3)
    | ~ spl15_534 ),
    inference(avatar_component_clause,[],[f7777])).

fof(f1709,plain,
    ( ! [X1] :
        ( ~ r1_partfun1(sK2,sK3)
        | ~ r2_hidden(X1,k3_xboole_0(k1_relat_1(sK2),k1_relat_1(sK3)))
        | k1_funct_1(sK2,X1) = k1_funct_1(sK3,X1) )
    | ~ spl15_2
    | ~ spl15_28
    | ~ spl15_244 ),
    inference(subsumption_resolution,[],[f1708,f331])).

fof(f1708,plain,
    ( ! [X1] :
        ( ~ r1_partfun1(sK2,sK3)
        | ~ r2_hidden(X1,k3_xboole_0(k1_relat_1(sK2),k1_relat_1(sK3)))
        | ~ v1_relat_1(sK3)
        | k1_funct_1(sK2,X1) = k1_funct_1(sK3,X1) )
    | ~ spl15_2
    | ~ spl15_244 ),
    inference(resolution,[],[f1696,f224])).

fof(f1696,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X1)
        | ~ r1_partfun1(sK2,X1)
        | ~ r2_hidden(X0,k3_xboole_0(k1_relat_1(sK2),k1_relat_1(X1)))
        | ~ v1_relat_1(X1)
        | k1_funct_1(sK2,X0) = k1_funct_1(X1,X0) )
    | ~ spl15_244 ),
    inference(avatar_component_clause,[],[f1695])).

fof(f8388,plain,
    ( spl15_574
    | ~ spl15_20
    | ~ spl15_228 ),
    inference(avatar_split_clause,[],[f6356,f1614,f280,f8128])).

fof(f1614,plain,
    ( spl15_228
  <=> ! [X3,X5,X4] :
        ( ~ r2_hidden(X3,k5_partfun1(X4,X5,sK3))
        | ~ v1_funct_1(X3)
        | ~ v1_relat_1(X3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | r1_partfun1(sK3,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_228])])).

fof(f6356,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ r2_hidden(X1,k5_partfun1(sK0,sK1,sK3))
        | r1_partfun1(sK3,X1) )
    | ~ spl15_20
    | ~ spl15_228 ),
    inference(resolution,[],[f281,f1615])).

fof(f1615,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X3)
        | ~ v1_relat_1(X3)
        | ~ r2_hidden(X3,k5_partfun1(X4,X5,sK3))
        | r1_partfun1(sK3,X3) )
    | ~ spl15_228 ),
    inference(avatar_component_clause,[],[f1614])).

fof(f6458,plain,
    ( spl15_444
    | ~ spl15_0
    | ~ spl15_26
    | ~ spl15_278
    | ~ spl15_426
    | ~ spl15_440 ),
    inference(avatar_split_clause,[],[f6449,f6188,f5740,f2374,f318,f216,f6456])).

fof(f6188,plain,
    ( spl15_440
  <=> r1_partfun1(sK7(sK0,sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_440])])).

fof(f6449,plain,
    ( r1_partfun1(sK2,sK7(sK0,sK1,sK2))
    | ~ spl15_0
    | ~ spl15_26
    | ~ spl15_278
    | ~ spl15_426
    | ~ spl15_440 ),
    inference(subsumption_resolution,[],[f6448,f5741])).

fof(f6448,plain,
    ( r1_partfun1(sK2,sK7(sK0,sK1,sK2))
    | ~ v1_relat_1(sK7(sK0,sK1,sK2))
    | ~ spl15_0
    | ~ spl15_26
    | ~ spl15_278
    | ~ spl15_440 ),
    inference(subsumption_resolution,[],[f6447,f2375])).

fof(f6447,plain,
    ( r1_partfun1(sK2,sK7(sK0,sK1,sK2))
    | ~ v1_funct_1(sK7(sK0,sK1,sK2))
    | ~ v1_relat_1(sK7(sK0,sK1,sK2))
    | ~ spl15_0
    | ~ spl15_26
    | ~ spl15_440 ),
    inference(subsumption_resolution,[],[f6446,f319])).

fof(f6446,plain,
    ( r1_partfun1(sK2,sK7(sK0,sK1,sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK7(sK0,sK1,sK2))
    | ~ v1_relat_1(sK7(sK0,sK1,sK2))
    | ~ spl15_0
    | ~ spl15_440 ),
    inference(subsumption_resolution,[],[f6445,f217])).

fof(f6445,plain,
    ( r1_partfun1(sK2,sK7(sK0,sK1,sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK7(sK0,sK1,sK2))
    | ~ v1_relat_1(sK7(sK0,sK1,sK2))
    | ~ spl15_440 ),
    inference(resolution,[],[f6189,f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ r1_partfun1(X0,X1)
      | r1_partfun1(X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X1,X0)
      | ~ r1_partfun1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_partfun1(X1,X0)
      | ~ r1_partfun1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( r1_partfun1(X0,X1)
       => r1_partfun1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t166_funct_2.p',symmetry_r1_partfun1)).

fof(f6189,plain,
    ( r1_partfun1(sK7(sK0,sK1,sK2),sK2)
    | ~ spl15_440 ),
    inference(avatar_component_clause,[],[f6188])).

fof(f6319,plain,
    ( ~ spl15_102
    | ~ spl15_432 ),
    inference(avatar_contradiction_clause,[],[f6317])).

fof(f6317,plain,
    ( $false
    | ~ spl15_102
    | ~ spl15_432 ),
    inference(unit_resulting_resolution,[],[f747,f6046,f211])).

fof(f6046,plain,
    ( sP14(k1_relat_1(sK3))
    | ~ spl15_432 ),
    inference(avatar_component_clause,[],[f6045])).

fof(f6045,plain,
    ( spl15_432
  <=> sP14(k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_432])])).

fof(f6190,plain,
    ( spl15_440
    | ~ spl15_0
    | ~ spl15_18
    | ~ spl15_260
    | spl15_277
    | ~ spl15_426 ),
    inference(avatar_split_clause,[],[f6101,f5740,f2365,f1840,f273,f216,f6188])).

fof(f1840,plain,
    ( spl15_260
  <=> ! [X1,X0,X2] :
        ( o_0_0_xboole_0 = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ v1_funct_1(X1)
        | r1_partfun1(sK7(X2,X0,X1),X1)
        | ~ v1_relat_1(sK7(X2,X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_260])])).

fof(f6101,plain,
    ( r1_partfun1(sK7(sK0,sK1,sK2),sK2)
    | ~ spl15_0
    | ~ spl15_18
    | ~ spl15_260
    | ~ spl15_277
    | ~ spl15_426 ),
    inference(subsumption_resolution,[],[f6100,f2366])).

fof(f6100,plain,
    ( r1_partfun1(sK7(sK0,sK1,sK2),sK2)
    | o_0_0_xboole_0 = sK1
    | ~ spl15_0
    | ~ spl15_18
    | ~ spl15_260
    | ~ spl15_426 ),
    inference(subsumption_resolution,[],[f6099,f217])).

fof(f6099,plain,
    ( ~ v1_funct_1(sK2)
    | r1_partfun1(sK7(sK0,sK1,sK2),sK2)
    | o_0_0_xboole_0 = sK1
    | ~ spl15_18
    | ~ spl15_260
    | ~ spl15_426 ),
    inference(subsumption_resolution,[],[f6098,f274])).

fof(f6098,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | r1_partfun1(sK7(sK0,sK1,sK2),sK2)
    | o_0_0_xboole_0 = sK1
    | ~ spl15_260
    | ~ spl15_426 ),
    inference(resolution,[],[f5741,f1841])).

fof(f1841,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(sK7(X2,X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ v1_funct_1(X1)
        | r1_partfun1(sK7(X2,X0,X1),X1)
        | o_0_0_xboole_0 = X0 )
    | ~ spl15_260 ),
    inference(avatar_component_clause,[],[f1840])).

fof(f6047,plain,
    ( spl15_432
    | ~ spl15_40
    | ~ spl15_424 ),
    inference(avatar_split_clause,[],[f6006,f5299,f384,f6045])).

fof(f5299,plain,
    ( spl15_424
  <=> m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_424])])).

fof(f6006,plain,
    ( sP14(k1_relat_1(sK3))
    | ~ spl15_40
    | ~ spl15_424 ),
    inference(resolution,[],[f5300,f385])).

fof(f5300,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl15_424 ),
    inference(avatar_component_clause,[],[f5299])).

fof(f5742,plain,
    ( spl15_426
    | ~ spl15_420 ),
    inference(avatar_split_clause,[],[f5717,f4982,f5740])).

fof(f5717,plain,
    ( v1_relat_1(sK7(sK0,sK1,sK2))
    | ~ spl15_420 ),
    inference(resolution,[],[f4983,f155])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t166_funct_2.p',cc1_relset_1)).

fof(f5301,plain,
    ( spl15_424
    | ~ spl15_418 ),
    inference(avatar_split_clause,[],[f4998,f4665,f5299])).

fof(f4665,plain,
    ( spl15_418
  <=> r1_tarski(k1_relat_1(sK3),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_418])])).

fof(f4998,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl15_418 ),
    inference(resolution,[],[f4666,f148])).

fof(f4666,plain,
    ( r1_tarski(k1_relat_1(sK3),o_0_0_xboole_0)
    | ~ spl15_418 ),
    inference(avatar_component_clause,[],[f4665])).

fof(f4985,plain,
    ( o_0_0_xboole_0 != sK2
    | k1_relset_1(sK0,sK1,sK2) != k1_relat_1(sK2)
    | k1_relset_1(sK0,sK1,o_0_0_xboole_0) != o_0_0_xboole_0
    | k1_relat_1(sK2) = o_0_0_xboole_0 ),
    introduced(theory_axiom,[])).

fof(f4984,plain,
    ( spl15_420
    | ~ spl15_18
    | ~ spl15_208
    | spl15_277 ),
    inference(avatar_split_clause,[],[f4603,f2365,f1500,f273,f4982])).

fof(f1500,plain,
    ( spl15_208
  <=> ! [X1,X0] :
        ( m1_subset_1(sK7(X0,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | o_0_0_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_208])])).

fof(f4603,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl15_18
    | ~ spl15_208
    | ~ spl15_277 ),
    inference(subsumption_resolution,[],[f4602,f2366])).

fof(f4602,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | o_0_0_xboole_0 = sK1
    | ~ spl15_18
    | ~ spl15_208 ),
    inference(resolution,[],[f1501,f274])).

fof(f1501,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(sK7(X0,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | o_0_0_xboole_0 = X1 )
    | ~ spl15_208 ),
    inference(avatar_component_clause,[],[f1500])).

fof(f4667,plain,
    ( spl15_418
    | ~ spl15_70
    | ~ spl15_414 ),
    inference(avatar_split_clause,[],[f4636,f4371,f541,f4665])).

fof(f4371,plain,
    ( spl15_414
  <=> k1_relat_1(sK2) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_414])])).

fof(f4636,plain,
    ( r1_tarski(k1_relat_1(sK3),o_0_0_xboole_0)
    | ~ spl15_70
    | ~ spl15_414 ),
    inference(backward_demodulation,[],[f4372,f542])).

fof(f4372,plain,
    ( k1_relat_1(sK2) = o_0_0_xboole_0
    | ~ spl15_414 ),
    inference(avatar_component_clause,[],[f4371])).

fof(f4373,plain,
    ( spl15_414
    | ~ spl15_14
    | ~ spl15_400 ),
    inference(avatar_split_clause,[],[f3911,f3901,f261,f4371])).

fof(f3901,plain,
    ( spl15_400
  <=> v1_xboole_0(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_400])])).

fof(f3911,plain,
    ( k1_relat_1(sK2) = o_0_0_xboole_0
    | ~ spl15_14
    | ~ spl15_400 ),
    inference(resolution,[],[f3902,f262])).

fof(f3902,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | ~ spl15_400 ),
    inference(avatar_component_clause,[],[f3901])).

fof(f4026,plain,
    ( spl15_410
    | ~ spl15_14
    | ~ spl15_286 ),
    inference(avatar_split_clause,[],[f3926,f2534,f261,f4024])).

fof(f4024,plain,
    ( spl15_410
  <=> o_0_0_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_410])])).

fof(f2534,plain,
    ( spl15_286
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_286])])).

fof(f3926,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ spl15_14
    | ~ spl15_286 ),
    inference(resolution,[],[f2535,f262])).

fof(f2535,plain,
    ( v1_xboole_0(sK2)
    | ~ spl15_286 ),
    inference(avatar_component_clause,[],[f2534])).

fof(f3367,plain,
    ( spl15_318
    | ~ spl15_14
    | ~ spl15_74
    | ~ spl15_90
    | ~ spl15_96 ),
    inference(avatar_split_clause,[],[f3363,f698,f668,f554,f261,f3365])).

fof(f668,plain,
    ( spl15_90
  <=> ! [X1,X0,X2] :
        ( o_0_0_xboole_0 = X1
        | v1_funct_2(sK7(X0,X1,X2),X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_90])])).

fof(f698,plain,
    ( spl15_96
  <=> ! [X1,X0,X2] :
        ( o_0_0_xboole_0 = X1
        | m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_96])])).

fof(f3363,plain,
    ( ! [X2,X0,X1] :
        ( o_0_0_xboole_0 = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ v1_funct_1(X1)
        | v1_partfun1(sK7(X2,X0,X1),X2) )
    | ~ spl15_14
    | ~ spl15_74
    | ~ spl15_90
    | ~ spl15_96 ),
    inference(subsumption_resolution,[],[f676,f699])).

fof(f699,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X2)
        | m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | o_0_0_xboole_0 = X1 )
    | ~ spl15_96 ),
    inference(avatar_component_clause,[],[f698])).

fof(f676,plain,
    ( ! [X2,X0,X1] :
        ( o_0_0_xboole_0 = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ v1_funct_1(X1)
        | v1_partfun1(sK7(X2,X0,X1),X2)
        | ~ m1_subset_1(sK7(X2,X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
    | ~ spl15_14
    | ~ spl15_74
    | ~ spl15_90 ),
    inference(subsumption_resolution,[],[f675,f262])).

fof(f675,plain,
    ( ! [X2,X0,X1] :
        ( o_0_0_xboole_0 = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ v1_funct_1(X1)
        | v1_partfun1(sK7(X2,X0,X1),X2)
        | ~ m1_subset_1(sK7(X2,X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | v1_xboole_0(X0) )
    | ~ spl15_74
    | ~ spl15_90 ),
    inference(subsumption_resolution,[],[f674,f555])).

fof(f674,plain,
    ( ! [X2,X0,X1] :
        ( o_0_0_xboole_0 = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ v1_funct_1(X1)
        | v1_partfun1(sK7(X2,X0,X1),X2)
        | ~ v1_funct_1(sK7(X2,X0,X1))
        | ~ m1_subset_1(sK7(X2,X0,X1),k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | v1_xboole_0(X0) )
    | ~ spl15_90 ),
    inference(resolution,[],[f669,f139])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t166_funct_2.p',cc5_funct_2)).

fof(f669,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(sK7(X0,X1,X2),X0,X1)
        | o_0_0_xboole_0 = X1
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl15_90 ),
    inference(avatar_component_clause,[],[f668])).

fof(f2536,plain,
    ( spl15_286
    | ~ spl15_110
    | ~ spl15_282 ),
    inference(avatar_split_clause,[],[f2510,f2409,f805,f2534])).

fof(f805,plain,
    ( spl15_110
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,o_0_0_xboole_0)))
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_110])])).

fof(f2409,plain,
    ( spl15_282
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_282])])).

fof(f2510,plain,
    ( v1_xboole_0(sK2)
    | ~ spl15_110
    | ~ spl15_282 ),
    inference(resolution,[],[f2410,f806])).

fof(f806,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,o_0_0_xboole_0)))
        | v1_xboole_0(X0) )
    | ~ spl15_110 ),
    inference(avatar_component_clause,[],[f805])).

fof(f2410,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,o_0_0_xboole_0)))
    | ~ spl15_282 ),
    inference(avatar_component_clause,[],[f2409])).

fof(f2411,plain,
    ( spl15_282
    | ~ spl15_18
    | ~ spl15_276 ),
    inference(avatar_split_clause,[],[f2378,f2368,f273,f2409])).

fof(f2368,plain,
    ( spl15_276
  <=> o_0_0_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_276])])).

fof(f2378,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,o_0_0_xboole_0)))
    | ~ spl15_18
    | ~ spl15_276 ),
    inference(backward_demodulation,[],[f2369,f274])).

fof(f2369,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl15_276 ),
    inference(avatar_component_clause,[],[f2368])).

fof(f2376,plain,
    ( spl15_276
    | spl15_278
    | ~ spl15_18
    | ~ spl15_168 ),
    inference(avatar_split_clause,[],[f1191,f1173,f273,f2374,f2368])).

fof(f1173,plain,
    ( spl15_168
  <=> ! [X1,X0] :
        ( v1_funct_1(sK7(X0,X1,sK2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | o_0_0_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_168])])).

fof(f1191,plain,
    ( v1_funct_1(sK7(sK0,sK1,sK2))
    | o_0_0_xboole_0 = sK1
    | ~ spl15_18
    | ~ spl15_168 ),
    inference(resolution,[],[f1174,f274])).

fof(f1174,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_funct_1(sK7(X0,X1,sK2))
        | o_0_0_xboole_0 = X1 )
    | ~ spl15_168 ),
    inference(avatar_component_clause,[],[f1173])).

fof(f1850,plain,
    ( spl15_262
    | ~ spl15_172
    | ~ spl15_200 ),
    inference(avatar_split_clause,[],[f1843,f1483,f1188,f1848])).

fof(f1848,plain,
    ( spl15_262
  <=> k1_relset_1(sK0,sK1,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_262])])).

fof(f1188,plain,
    ( spl15_172
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_172])])).

fof(f1483,plain,
    ( spl15_200
  <=> k1_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_200])])).

fof(f1843,plain,
    ( k1_relset_1(sK0,sK1,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl15_172
    | ~ spl15_200 ),
    inference(forward_demodulation,[],[f1194,f1484])).

fof(f1484,plain,
    ( k1_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl15_200 ),
    inference(avatar_component_clause,[],[f1483])).

fof(f1194,plain,
    ( k1_relset_1(sK0,sK1,o_0_0_xboole_0) = k1_relat_1(o_0_0_xboole_0)
    | ~ spl15_172 ),
    inference(resolution,[],[f1189,f156])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t166_funct_2.p',redefinition_k1_relset_1)).

fof(f1189,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl15_172 ),
    inference(avatar_component_clause,[],[f1188])).

fof(f1842,plain,
    ( spl15_260
    | ~ spl15_74
    | ~ spl15_82 ),
    inference(avatar_split_clause,[],[f654,f634,f554,f1840])).

fof(f654,plain,
    ( ! [X2,X0,X1] :
        ( o_0_0_xboole_0 = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ v1_funct_1(X1)
        | r1_partfun1(sK7(X2,X0,X1),X1)
        | ~ v1_relat_1(sK7(X2,X0,X1)) )
    | ~ spl15_74
    | ~ spl15_82 ),
    inference(subsumption_resolution,[],[f653,f155])).

fof(f653,plain,
    ( ! [X2,X0,X1] :
        ( o_0_0_xboole_0 = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ v1_funct_1(X1)
        | r1_partfun1(sK7(X2,X0,X1),X1)
        | ~ v1_relat_1(sK7(X2,X0,X1))
        | ~ v1_relat_1(X1) )
    | ~ spl15_74
    | ~ spl15_82 ),
    inference(subsumption_resolution,[],[f652,f555])).

fof(f652,plain,
    ( ! [X2,X0,X1] :
        ( o_0_0_xboole_0 = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ v1_funct_1(X1)
        | r1_partfun1(sK7(X2,X0,X1),X1)
        | ~ v1_funct_1(sK7(X2,X0,X1))
        | ~ v1_relat_1(sK7(X2,X0,X1))
        | ~ v1_relat_1(X1) )
    | ~ spl15_82 ),
    inference(duplicate_literal_removal,[],[f651])).

fof(f651,plain,
    ( ! [X2,X0,X1] :
        ( o_0_0_xboole_0 = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ v1_funct_1(X1)
        | r1_partfun1(sK7(X2,X0,X1),X1)
        | ~ v1_funct_1(sK7(X2,X0,X1))
        | ~ v1_relat_1(sK7(X2,X0,X1))
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl15_82 ),
    inference(resolution,[],[f635,f146])).

fof(f1697,plain,
    ( spl15_244
    | ~ spl15_0
    | ~ spl15_26 ),
    inference(avatar_split_clause,[],[f777,f318,f216,f1695])).

fof(f777,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k3_xboole_0(k1_relat_1(sK2),k1_relat_1(X1)))
        | ~ r1_partfun1(sK2,X1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | k1_funct_1(sK2,X0) = k1_funct_1(X1,X0) )
    | ~ spl15_0
    | ~ spl15_26 ),
    inference(subsumption_resolution,[],[f775,f319])).

fof(f775,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k3_xboole_0(k1_relat_1(sK2),k1_relat_1(X1)))
        | ~ r1_partfun1(sK2,X1)
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | k1_funct_1(sK2,X0) = k1_funct_1(X1,X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl15_0 ),
    inference(resolution,[],[f132,f217])).

fof(f132,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X3,k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
      | ~ r1_partfun1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f100])).

fof(f100,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_partfun1(X0,X1)
              | ( k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
                & r2_hidden(sK5(X0,X1),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) )
            & ( ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) )
              | ~ r1_partfun1(X0,X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f98,f99])).

fof(f99,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) )
     => ( k1_funct_1(X0,sK5(X0,X1)) != k1_funct_1(X1,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f98,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_partfun1(X0,X1)
              | ? [X2] :
                  ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
                  & r2_hidden(X2,k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) )
            & ( ! [X3] :
                  ( k1_funct_1(X0,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) )
              | ~ r1_partfun1(X0,X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f97])).

fof(f97,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_partfun1(X0,X1)
              | ? [X2] :
                  ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
                  & r2_hidden(X2,k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) )
            & ( ! [X2] :
                  ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                  | ~ r2_hidden(X2,k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) )
              | ~ r1_partfun1(X0,X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_partfun1(X0,X1)
          <=> ! [X2] :
                ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                | ~ r2_hidden(X2,k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_partfun1(X0,X1)
          <=> ! [X2] :
                ( k1_funct_1(X0,X2) = k1_funct_1(X1,X2)
                | ~ r2_hidden(X2,k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( r1_partfun1(X0,X1)
          <=> ! [X2] :
                ( r2_hidden(X2,k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
               => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t166_funct_2.p',d6_partfun1)).

fof(f1616,plain,
    ( spl15_228
    | ~ spl15_2 ),
    inference(avatar_split_clause,[],[f709,f223,f1614])).

fof(f709,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_hidden(X3,k5_partfun1(X4,X5,sK3))
        | ~ v1_funct_1(X3)
        | ~ v1_relat_1(X3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | r1_partfun1(sK3,X3) )
    | ~ spl15_2 ),
    inference(resolution,[],[f166,f224])).

fof(f166,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r1_partfun1(X2,X3) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
          | ~ v1_funct_1(X3)
          | ~ v1_relat_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_partfun1(X2,X3)
          | ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
          | ~ v1_funct_1(X3)
          | ~ v1_relat_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( v1_funct_1(X3)
            & v1_relat_1(X3) )
         => ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
           => r1_partfun1(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t166_funct_2.p',t171_partfun1)).

fof(f1502,plain,
    ( spl15_208
    | ~ spl15_0
    | ~ spl15_96 ),
    inference(avatar_split_clause,[],[f705,f698,f216,f1500])).

fof(f705,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK7(X0,X1,sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | o_0_0_xboole_0 = X1 )
    | ~ spl15_0
    | ~ spl15_96 ),
    inference(resolution,[],[f699,f217])).

fof(f1485,plain,
    ( spl15_200
    | ~ spl15_14
    | ~ spl15_192 ),
    inference(avatar_split_clause,[],[f1353,f1304,f261,f1483])).

fof(f1304,plain,
    ( spl15_192
  <=> v1_xboole_0(k1_relat_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_192])])).

fof(f1353,plain,
    ( k1_relat_1(o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl15_14
    | ~ spl15_192 ),
    inference(resolution,[],[f1305,f262])).

fof(f1305,plain,
    ( v1_xboole_0(k1_relat_1(o_0_0_xboole_0))
    | ~ spl15_192 ),
    inference(avatar_component_clause,[],[f1304])).

fof(f1306,plain,
    ( spl15_192
    | ~ spl15_110
    | ~ spl15_188 ),
    inference(avatar_split_clause,[],[f1281,f1264,f805,f1304])).

fof(f1264,plain,
    ( spl15_188
  <=> ! [X0] : m1_subset_1(k1_relat_1(o_0_0_xboole_0),k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_188])])).

fof(f1281,plain,
    ( v1_xboole_0(k1_relat_1(o_0_0_xboole_0))
    | ~ spl15_110
    | ~ spl15_188 ),
    inference(resolution,[],[f1265,f806])).

fof(f1265,plain,
    ( ! [X0] : m1_subset_1(k1_relat_1(o_0_0_xboole_0),k1_zfmisc_1(X0))
    | ~ spl15_188 ),
    inference(avatar_component_clause,[],[f1264])).

fof(f1266,plain,
    ( spl15_188
    | ~ spl15_114 ),
    inference(avatar_split_clause,[],[f1254,f827,f1264])).

fof(f827,plain,
    ( spl15_114
  <=> ! [X10] : o_0_0_xboole_0 = sK6(k1_zfmisc_1(k2_zfmisc_1(X10,o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_114])])).

fof(f1254,plain,
    ( ! [X0] : m1_subset_1(k1_relat_1(o_0_0_xboole_0),k1_zfmisc_1(X0))
    | ~ spl15_114 ),
    inference(superposition,[],[f1233,f828])).

fof(f828,plain,
    ( ! [X10] : o_0_0_xboole_0 = sK6(k1_zfmisc_1(k2_zfmisc_1(X10,o_0_0_xboole_0)))
    | ~ spl15_114 ),
    inference(avatar_component_clause,[],[f827])).

fof(f1233,plain,(
    ! [X4,X5] : m1_subset_1(k1_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(X4,X5)))),k1_zfmisc_1(X4)) ),
    inference(backward_demodulation,[],[f432,f436])).

fof(f436,plain,(
    ! [X4,X5] : m1_subset_1(k1_relset_1(X4,X5,sK6(k1_zfmisc_1(k2_zfmisc_1(X4,X5)))),k1_zfmisc_1(X4)) ),
    inference(resolution,[],[f157,f135])).

fof(f135,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f102])).

fof(f102,plain,(
    ! [X0] : m1_subset_1(sK6(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f20,f101])).

fof(f101,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t166_funct_2.p',existence_m1_subset_1)).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t166_funct_2.p',dt_k1_relset_1)).

fof(f432,plain,(
    ! [X4,X5] : k1_relset_1(X4,X5,sK6(k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) = k1_relat_1(sK6(k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) ),
    inference(resolution,[],[f156,f135])).

fof(f1190,plain,
    ( spl15_172
    | ~ spl15_158 ),
    inference(avatar_split_clause,[],[f1101,f1090,f1188])).

fof(f1090,plain,
    ( spl15_158
  <=> r1_tarski(o_0_0_xboole_0,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_158])])).

fof(f1101,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl15_158 ),
    inference(resolution,[],[f1091,f148])).

fof(f1091,plain,
    ( r1_tarski(o_0_0_xboole_0,k2_zfmisc_1(sK0,sK1))
    | ~ spl15_158 ),
    inference(avatar_component_clause,[],[f1090])).

fof(f1175,plain,
    ( spl15_168
    | ~ spl15_0
    | ~ spl15_74 ),
    inference(avatar_split_clause,[],[f560,f554,f216,f1173])).

fof(f560,plain,
    ( ! [X0,X1] :
        ( v1_funct_1(sK7(X0,X1,sK2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | o_0_0_xboole_0 = X1 )
    | ~ spl15_0
    | ~ spl15_74 ),
    inference(resolution,[],[f555,f217])).

fof(f1092,plain,
    ( spl15_158
    | ~ spl15_32
    | ~ spl15_148 ),
    inference(avatar_split_clause,[],[f1081,f1053,f347,f1090])).

fof(f347,plain,
    ( spl15_32
  <=> ! [X1] : k3_xboole_0(o_0_0_xboole_0,X1) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_32])])).

fof(f1053,plain,
    ( spl15_148
  <=> ! [X2] : r1_tarski(k3_xboole_0(X2,sK2),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_148])])).

fof(f1081,plain,
    ( r1_tarski(o_0_0_xboole_0,k2_zfmisc_1(sK0,sK1))
    | ~ spl15_32
    | ~ spl15_148 ),
    inference(superposition,[],[f1054,f348])).

fof(f348,plain,
    ( ! [X1] : k3_xboole_0(o_0_0_xboole_0,X1) = o_0_0_xboole_0
    | ~ spl15_32 ),
    inference(avatar_component_clause,[],[f347])).

fof(f1054,plain,
    ( ! [X2] : r1_tarski(k3_xboole_0(X2,sK2),k2_zfmisc_1(sK0,sK1))
    | ~ spl15_148 ),
    inference(avatar_component_clause,[],[f1053])).

fof(f1055,plain,
    ( spl15_148
    | ~ spl15_18
    | ~ spl15_124 ),
    inference(avatar_split_clause,[],[f907,f860,f273,f1053])).

fof(f860,plain,
    ( spl15_124
  <=> ! [X4] : k3_xboole_0(X4,sK2) = k9_subset_1(k2_zfmisc_1(sK0,sK1),X4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_124])])).

fof(f907,plain,
    ( ! [X2] : r1_tarski(k3_xboole_0(X2,sK2),k2_zfmisc_1(sK0,sK1))
    | ~ spl15_18
    | ~ spl15_124 ),
    inference(subsumption_resolution,[],[f905,f274])).

fof(f905,plain,
    ( ! [X2] :
        ( r1_tarski(k3_xboole_0(X2,sK2),k2_zfmisc_1(sK0,sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
    | ~ spl15_124 ),
    inference(superposition,[],[f389,f861])).

fof(f861,plain,
    ( ! [X4] : k3_xboole_0(X4,sK2) = k9_subset_1(k2_zfmisc_1(sK0,sK1),X4,sK2)
    | ~ spl15_124 ),
    inference(avatar_component_clause,[],[f860])).

fof(f389,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_subset_1(X1,X2,X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f152,f147])).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t166_funct_2.p',dt_k9_subset_1)).

fof(f862,plain,
    ( spl15_124
    | ~ spl15_18 ),
    inference(avatar_split_clause,[],[f408,f273,f860])).

fof(f408,plain,
    ( ! [X4] : k3_xboole_0(X4,sK2) = k9_subset_1(k2_zfmisc_1(sK0,sK1),X4,sK2)
    | ~ spl15_18 ),
    inference(resolution,[],[f153,f274])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t166_funct_2.p',redefinition_k9_subset_1)).

fof(f854,plain,
    ( spl15_120
    | ~ spl15_36 ),
    inference(avatar_split_clause,[],[f376,f365,f852])).

fof(f376,plain,
    ( m1_subset_1(k5_partfun1(sK0,sK1,sK2),k1_zfmisc_1(k5_partfun1(sK0,sK1,sK3)))
    | ~ spl15_36 ),
    inference(resolution,[],[f366,f148])).

fof(f829,plain,
    ( spl15_114
    | ~ spl15_14
    | ~ spl15_112 ),
    inference(avatar_split_clause,[],[f824,f815,f261,f827])).

fof(f815,plain,
    ( spl15_112
  <=> ! [X3] : v1_xboole_0(sK6(k1_zfmisc_1(k2_zfmisc_1(X3,o_0_0_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_112])])).

fof(f824,plain,
    ( ! [X10] : o_0_0_xboole_0 = sK6(k1_zfmisc_1(k2_zfmisc_1(X10,o_0_0_xboole_0)))
    | ~ spl15_14
    | ~ spl15_112 ),
    inference(resolution,[],[f816,f262])).

fof(f816,plain,
    ( ! [X3] : v1_xboole_0(sK6(k1_zfmisc_1(k2_zfmisc_1(X3,o_0_0_xboole_0))))
    | ~ spl15_112 ),
    inference(avatar_component_clause,[],[f815])).

fof(f817,plain,
    ( spl15_112
    | ~ spl15_110 ),
    inference(avatar_split_clause,[],[f811,f805,f815])).

fof(f811,plain,
    ( ! [X3] : v1_xboole_0(sK6(k1_zfmisc_1(k2_zfmisc_1(X3,o_0_0_xboole_0))))
    | ~ spl15_110 ),
    inference(resolution,[],[f806,f135])).

fof(f807,plain,
    ( spl15_110
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f377,f230,f805])).

fof(f230,plain,
    ( spl15_4
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_4])])).

fof(f377,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,o_0_0_xboole_0)))
        | v1_xboole_0(X0) )
    | ~ spl15_4 ),
    inference(resolution,[],[f140,f231])).

fof(f231,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl15_4 ),
    inference(avatar_component_clause,[],[f230])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t166_funct_2.p',cc4_relset_1)).

fof(f748,plain,
    ( spl15_102
    | ~ spl15_0
    | ~ spl15_2
    | ~ spl15_26
    | ~ spl15_28
    | ~ spl15_70
    | spl15_101 ),
    inference(avatar_split_clause,[],[f741,f720,f541,f330,f318,f223,f216,f746])).

fof(f741,plain,
    ( r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3))
    | ~ spl15_0
    | ~ spl15_2
    | ~ spl15_26
    | ~ spl15_28
    | ~ spl15_70
    | ~ spl15_101 ),
    inference(subsumption_resolution,[],[f740,f331])).

fof(f740,plain,
    ( r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl15_0
    | ~ spl15_2
    | ~ spl15_26
    | ~ spl15_70
    | ~ spl15_101 ),
    inference(subsumption_resolution,[],[f739,f224])).

fof(f739,plain,
    ( r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl15_0
    | ~ spl15_26
    | ~ spl15_70
    | ~ spl15_101 ),
    inference(subsumption_resolution,[],[f738,f319])).

fof(f738,plain,
    ( r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl15_0
    | ~ spl15_70
    | ~ spl15_101 ),
    inference(subsumption_resolution,[],[f737,f217])).

fof(f737,plain,
    ( r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl15_70
    | ~ spl15_101 ),
    inference(subsumption_resolution,[],[f735,f721])).

fof(f735,plain,
    ( r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3))
    | r1_tarski(sK3,sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl15_70 ),
    inference(resolution,[],[f130,f542])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | r1_tarski(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f722,plain,
    ( ~ spl15_101
    | spl15_7
    | ~ spl15_98 ),
    inference(avatar_split_clause,[],[f710,f702,f237,f720])).

fof(f237,plain,
    ( spl15_7
  <=> ~ r1_relset_1(sK0,sK1,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_7])])).

fof(f702,plain,
    ( spl15_98
  <=> ! [X6] :
        ( ~ r1_tarski(sK3,X6)
        | r1_relset_1(sK0,sK1,sK3,X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_98])])).

fof(f710,plain,
    ( ~ r1_tarski(sK3,sK2)
    | ~ spl15_7
    | ~ spl15_98 ),
    inference(resolution,[],[f703,f238])).

fof(f238,plain,
    ( ~ r1_relset_1(sK0,sK1,sK3,sK2)
    | ~ spl15_7 ),
    inference(avatar_component_clause,[],[f237])).

fof(f703,plain,
    ( ! [X6] :
        ( r1_relset_1(sK0,sK1,sK3,X6)
        | ~ r1_tarski(sK3,X6) )
    | ~ spl15_98 ),
    inference(avatar_component_clause,[],[f702])).

fof(f704,plain,
    ( spl15_98
    | ~ spl15_20 ),
    inference(avatar_split_clause,[],[f481,f280,f702])).

fof(f481,plain,
    ( ! [X6] :
        ( ~ r1_tarski(sK3,X6)
        | r1_relset_1(sK0,sK1,sK3,X6) )
    | ~ spl15_20 ),
    inference(resolution,[],[f190,f281])).

fof(f190,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(X2,X3)
      | r1_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f117])).

fof(f117,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r1_relset_1(X0,X1,X2,X3)
          | ~ r1_tarski(X2,X3) )
        & ( r1_tarski(X2,X3)
          | ~ r1_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_relset_1(X0,X1,X2,X3)
      <=> r1_tarski(X2,X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_relset_1(X0,X1,X2,X3)
      <=> r1_tarski(X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t166_funct_2.p',redefinition_r1_relset_1)).

fof(f700,plain,
    ( spl15_96
    | ~ spl15_8 ),
    inference(avatar_split_clause,[],[f689,f247,f698])).

fof(f247,plain,
    ( spl15_8
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_8])])).

fof(f689,plain,
    ( ! [X2,X0,X1] :
        ( o_0_0_xboole_0 = X1
        | m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl15_8 ),
    inference(forward_demodulation,[],[f162,f248])).

fof(f248,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl15_8 ),
    inference(avatar_component_clause,[],[f247])).

fof(f162,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f105,plain,(
    ! [X0,X1,X2] :
      ( ( r1_partfun1(X2,sK7(X0,X1,X2))
        & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK7(X0,X1,X2),X0,X1)
        & v1_funct_1(sK7(X0,X1,X2)) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f77,f104])).

fof(f104,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( r1_partfun1(X2,sK7(X0,X1,X2))
        & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK7(X0,X1,X2),X0,X1)
        & v1_funct_1(sK7(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ~ ( ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X3,X0,X1)
                & v1_funct_1(X3) )
             => ~ r1_partfun1(X2,X3) )
          & ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t166_funct_2.p',t148_funct_2)).

fof(f670,plain,
    ( spl15_90
    | ~ spl15_8 ),
    inference(avatar_split_clause,[],[f659,f247,f668])).

fof(f659,plain,
    ( ! [X2,X0,X1] :
        ( o_0_0_xboole_0 = X1
        | v1_funct_2(sK7(X0,X1,X2),X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl15_8 ),
    inference(forward_demodulation,[],[f160,f248])).

fof(f160,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(sK7(X0,X1,X2),X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f636,plain,
    ( spl15_82
    | ~ spl15_8 ),
    inference(avatar_split_clause,[],[f578,f247,f634])).

fof(f578,plain,
    ( ! [X2,X0,X1] :
        ( o_0_0_xboole_0 = X1
        | r1_partfun1(X2,sK7(X0,X1,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl15_8 ),
    inference(forward_demodulation,[],[f164,f248])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( r1_partfun1(X2,sK7(X0,X1,X2))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f556,plain,
    ( spl15_74
    | ~ spl15_8 ),
    inference(avatar_split_clause,[],[f545,f247,f554])).

fof(f545,plain,
    ( ! [X2,X0,X1] :
        ( o_0_0_xboole_0 = X1
        | v1_funct_1(sK7(X0,X1,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl15_8 ),
    inference(forward_demodulation,[],[f158,f248])).

fof(f158,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(sK7(X0,X1,X2))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f552,plain,
    ( spl15_72
    | ~ spl15_70 ),
    inference(avatar_split_clause,[],[f544,f541,f550])).

fof(f544,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k1_relat_1(sK2)))
    | ~ spl15_70 ),
    inference(resolution,[],[f542,f148])).

fof(f543,plain,
    ( spl15_70
    | ~ spl15_20
    | ~ spl15_54 ),
    inference(avatar_split_clause,[],[f529,f464,f280,f541])).

fof(f464,plain,
    ( spl15_54
  <=> r1_tarski(k1_relset_1(sK0,sK1,sK3),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_54])])).

fof(f529,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK2))
    | ~ spl15_20
    | ~ spl15_54 ),
    inference(backward_demodulation,[],[f431,f465])).

fof(f465,plain,
    ( r1_tarski(k1_relset_1(sK0,sK1,sK3),k1_relat_1(sK2))
    | ~ spl15_54 ),
    inference(avatar_component_clause,[],[f464])).

fof(f431,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl15_20 ),
    inference(resolution,[],[f156,f281])).

fof(f466,plain,
    ( spl15_54
    | ~ spl15_18
    | ~ spl15_34 ),
    inference(avatar_split_clause,[],[f452,f357,f273,f464])).

fof(f357,plain,
    ( spl15_34
  <=> r1_tarski(k1_relset_1(sK0,sK1,sK3),k1_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_34])])).

fof(f452,plain,
    ( r1_tarski(k1_relset_1(sK0,sK1,sK3),k1_relat_1(sK2))
    | ~ spl15_18
    | ~ spl15_34 ),
    inference(backward_demodulation,[],[f430,f358])).

fof(f358,plain,
    ( r1_tarski(k1_relset_1(sK0,sK1,sK3),k1_relset_1(sK0,sK1,sK2))
    | ~ spl15_34 ),
    inference(avatar_component_clause,[],[f357])).

fof(f430,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl15_18 ),
    inference(resolution,[],[f156,f274])).

fof(f459,plain,
    ( spl15_52
    | ~ spl15_18 ),
    inference(avatar_split_clause,[],[f430,f273,f457])).

fof(f457,plain,
    ( spl15_52
  <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_52])])).

fof(f386,plain,
    ( spl15_40
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f351,f230,f384])).

fof(f351,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | sP14(X0) )
    | ~ spl15_4 ),
    inference(resolution,[],[f210,f231])).

fof(f367,plain,(
    spl15_36 ),
    inference(avatar_split_clause,[],[f123,f365])).

fof(f123,plain,(
    r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3)) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,
    ( ~ r1_relset_1(sK0,sK1,sK3,sK2)
    & r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,sK3))
    & r1_tarski(k1_relset_1(sK0,sK1,sK3),k1_relset_1(sK0,sK1,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f49,f90,f89])).

fof(f89,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r1_relset_1(X0,X1,X3,X2)
            & r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
            & r1_tarski(k1_relset_1(X0,X1,X3),k1_relset_1(X0,X1,X2))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r1_relset_1(sK0,sK1,X3,sK2)
          & r1_tarski(k5_partfun1(sK0,sK1,sK2),k5_partfun1(sK0,sK1,X3))
          & r1_tarski(k1_relset_1(sK0,sK1,X3),k1_relset_1(sK0,sK1,sK2))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_relset_1(X0,X1,X3,X2)
          & r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
          & r1_tarski(k1_relset_1(X0,X1,X3),k1_relset_1(X0,X1,X2))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
     => ( ~ r1_relset_1(X0,X1,sK3,X2)
        & r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,sK3))
        & r1_tarski(k1_relset_1(X0,X1,sK3),k1_relset_1(X0,X1,X2))
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_relset_1(X0,X1,X3,X2)
          & r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
          & r1_tarski(k1_relset_1(X0,X1,X3),k1_relset_1(X0,X1,X2))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_relset_1(X0,X1,X3,X2)
          & r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
          & r1_tarski(k1_relset_1(X0,X1,X3),k1_relset_1(X0,X1,X2))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X3) )
           => ( ( r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
                & r1_tarski(k1_relset_1(X0,X1,X3),k1_relset_1(X0,X1,X2)) )
             => r1_relset_1(X0,X1,X3,X2) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( r1_tarski(k5_partfun1(X0,X1,X2),k5_partfun1(X0,X1,X3))
              & r1_tarski(k1_relset_1(X0,X1,X3),k1_relset_1(X0,X1,X2)) )
           => r1_relset_1(X0,X1,X3,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t166_funct_2.p',t166_funct_2)).

fof(f360,plain,
    ( spl15_32
    | ~ spl15_16 ),
    inference(avatar_split_clause,[],[f289,f265,f347])).

fof(f265,plain,
    ( spl15_16
  <=> ! [X0] : k3_xboole_0(X0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_16])])).

fof(f289,plain,
    ( ! [X1] : k3_xboole_0(o_0_0_xboole_0,X1) = o_0_0_xboole_0
    | ~ spl15_16 ),
    inference(superposition,[],[f266,f137])).

fof(f137,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t166_funct_2.p',commutativity_k3_xboole_0)).

fof(f266,plain,
    ( ! [X0] : k3_xboole_0(X0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl15_16 ),
    inference(avatar_component_clause,[],[f265])).

fof(f359,plain,(
    spl15_34 ),
    inference(avatar_split_clause,[],[f122,f357])).

fof(f122,plain,(
    r1_tarski(k1_relset_1(sK0,sK1,sK3),k1_relset_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f91])).

fof(f332,plain,
    ( spl15_28
    | ~ spl15_20 ),
    inference(avatar_split_clause,[],[f313,f280,f330])).

fof(f313,plain,
    ( v1_relat_1(sK3)
    | ~ spl15_20 ),
    inference(resolution,[],[f155,f281])).

fof(f320,plain,
    ( spl15_26
    | ~ spl15_18 ),
    inference(avatar_split_clause,[],[f312,f273,f318])).

fof(f312,plain,
    ( v1_relat_1(sK2)
    | ~ spl15_18 ),
    inference(resolution,[],[f155,f274])).

fof(f282,plain,(
    spl15_20 ),
    inference(avatar_split_clause,[],[f121,f280])).

fof(f121,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f91])).

fof(f275,plain,(
    spl15_18 ),
    inference(avatar_split_clause,[],[f119,f273])).

fof(f119,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f91])).

fof(f267,plain,
    ( spl15_16
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f242,f230,f265])).

fof(f242,plain,
    ( ! [X0] : k3_xboole_0(X0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl15_4 ),
    inference(backward_demodulation,[],[f240,f126])).

fof(f126,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/funct_2__t166_funct_2.p',t2_boole)).

fof(f240,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl15_4 ),
    inference(resolution,[],[f127,f231])).

fof(f127,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t166_funct_2.p',t6_boole)).

fof(f263,plain,
    ( spl15_14
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f241,f230,f261])).

fof(f241,plain,
    ( ! [X0] :
        ( o_0_0_xboole_0 = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl15_4 ),
    inference(backward_demodulation,[],[f240,f127])).

fof(f249,plain,
    ( spl15_8
    | ~ spl15_4 ),
    inference(avatar_split_clause,[],[f240,f230,f247])).

fof(f239,plain,(
    ~ spl15_7 ),
    inference(avatar_split_clause,[],[f124,f237])).

fof(f124,plain,(
    ~ r1_relset_1(sK0,sK1,sK3,sK2) ),
    inference(cnf_transformation,[],[f91])).

fof(f232,plain,(
    spl15_4 ),
    inference(avatar_split_clause,[],[f125,f230])).

fof(f125,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t166_funct_2.p',dt_o_0_0_xboole_0)).

fof(f225,plain,(
    spl15_2 ),
    inference(avatar_split_clause,[],[f120,f223])).

fof(f120,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f91])).

fof(f218,plain,(
    spl15_0 ),
    inference(avatar_split_clause,[],[f118,f216])).

fof(f118,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f91])).
%------------------------------------------------------------------------------
