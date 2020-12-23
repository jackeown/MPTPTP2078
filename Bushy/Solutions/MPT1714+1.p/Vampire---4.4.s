%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t23_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:12 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  278 ( 676 expanded)
%              Number of leaves         :   75 ( 293 expanded)
%              Depth                    :    9
%              Number of atoms          :  780 (2450 expanded)
%              Number of equality atoms :    9 (  21 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f559,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f110,f117,f124,f131,f138,f145,f152,f159,f166,f175,f182,f193,f208,f221,f230,f237,f249,f256,f263,f278,f285,f292,f299,f310,f319,f326,f336,f343,f350,f358,f367,f376,f385,f395,f397,f399,f401,f403,f407,f410,f421,f430,f439,f469,f478,f488,f497,f504,f523,f530,f548,f552,f554,f556,f558])).

fof(f558,plain,
    ( ~ spl8_24
    | spl8_27
    | ~ spl8_42
    | ~ spl8_46 ),
    inference(avatar_contradiction_clause,[],[f557])).

fof(f557,plain,
    ( $false
    | ~ spl8_24
    | ~ spl8_27
    | ~ spl8_42
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f198,f388])).

fof(f388,plain,
    ( ~ r1_tsep_1(sK1,sK3)
    | ~ spl8_27
    | ~ spl8_42
    | ~ spl8_46 ),
    inference(unit_resulting_resolution,[],[f277,f291,f207,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t23_tmap_1.p',symmetry_r1_tsep_1)).

fof(f207,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl8_27
  <=> ~ r1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f291,plain,
    ( l1_struct_0(sK3)
    | ~ spl8_46 ),
    inference(avatar_component_clause,[],[f290])).

fof(f290,plain,
    ( spl8_46
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f277,plain,
    ( l1_struct_0(sK1)
    | ~ spl8_42 ),
    inference(avatar_component_clause,[],[f276])).

fof(f276,plain,
    ( spl8_42
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f198,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl8_24
  <=> r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f556,plain,
    ( ~ spl8_86
    | spl8_89 ),
    inference(avatar_contradiction_clause,[],[f555])).

fof(f555,plain,
    ( $false
    | ~ spl8_86
    | ~ spl8_89 ),
    inference(subsumption_resolution,[],[f519,f541])).

fof(f541,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ spl8_89 ),
    inference(resolution,[],[f529,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t23_tmap_1.p',symmetry_r1_xboole_0)).

fof(f529,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl8_89 ),
    inference(avatar_component_clause,[],[f528])).

fof(f528,plain,
    ( spl8_89
  <=> ~ r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_89])])).

fof(f519,plain,
    ( r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ spl8_86 ),
    inference(avatar_component_clause,[],[f518])).

fof(f518,plain,
    ( spl8_86
  <=> r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_86])])).

fof(f554,plain,
    ( ~ spl8_16
    | ~ spl8_38
    | spl8_91 ),
    inference(avatar_contradiction_clause,[],[f553])).

fof(f553,plain,
    ( $false
    | ~ spl8_16
    | ~ spl8_38
    | ~ spl8_91 ),
    inference(subsumption_resolution,[],[f550,f445])).

fof(f445,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl8_16
    | ~ spl8_38 ),
    inference(unit_resulting_resolution,[],[f255,f165,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t23_tmap_1.p',t1_tsep_1)).

fof(f165,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl8_16
  <=> m1_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f255,plain,
    ( l1_pre_topc(sK2)
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f254])).

fof(f254,plain,
    ( spl8_38
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f550,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl8_91 ),
    inference(resolution,[],[f547,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t23_tmap_1.p',t3_subset)).

fof(f547,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl8_91 ),
    inference(avatar_component_clause,[],[f546])).

fof(f546,plain,
    ( spl8_91
  <=> ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_91])])).

fof(f552,plain,
    ( ~ spl8_16
    | ~ spl8_38
    | spl8_91 ),
    inference(avatar_contradiction_clause,[],[f551])).

fof(f551,plain,
    ( $false
    | ~ spl8_16
    | ~ spl8_38
    | ~ spl8_91 ),
    inference(subsumption_resolution,[],[f549,f445])).

fof(f549,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl8_91 ),
    inference(unit_resulting_resolution,[],[f547,f95])).

fof(f548,plain,
    ( ~ spl8_91
    | ~ spl8_82
    | spl8_87 ),
    inference(avatar_split_clause,[],[f532,f521,f495,f546])).

fof(f495,plain,
    ( spl8_82
  <=> r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_82])])).

fof(f521,plain,
    ( spl8_87
  <=> ~ r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_87])])).

fof(f532,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl8_82
    | ~ spl8_87 ),
    inference(unit_resulting_resolution,[],[f496,f522,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t23_tmap_1.p',t63_xboole_1)).

fof(f522,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ spl8_87 ),
    inference(avatar_component_clause,[],[f521])).

fof(f496,plain,
    ( r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl8_82 ),
    inference(avatar_component_clause,[],[f495])).

fof(f530,plain,
    ( ~ spl8_89
    | spl8_27
    | ~ spl8_42
    | ~ spl8_46 ),
    inference(avatar_split_clause,[],[f508,f290,f276,f206,f528])).

fof(f508,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ spl8_27
    | ~ spl8_42
    | ~ spl8_46 ),
    inference(unit_resulting_resolution,[],[f291,f277,f207,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X0,X1)
      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t23_tmap_1.p',d3_tsep_1)).

fof(f523,plain,
    ( ~ spl8_87
    | spl8_25
    | ~ spl8_42
    | ~ spl8_46 ),
    inference(avatar_split_clause,[],[f507,f290,f276,f200,f521])).

fof(f200,plain,
    ( spl8_25
  <=> ~ r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f507,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ spl8_25
    | ~ spl8_42
    | ~ spl8_46 ),
    inference(unit_resulting_resolution,[],[f277,f291,f201,f81])).

fof(f201,plain,
    ( ~ r1_tsep_1(sK1,sK3)
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f200])).

fof(f504,plain,
    ( spl8_84
    | ~ spl8_30
    | ~ spl8_44
    | ~ spl8_46 ),
    inference(avatar_split_clause,[],[f481,f290,f283,f219,f502])).

fof(f502,plain,
    ( spl8_84
  <=> r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_84])])).

fof(f219,plain,
    ( spl8_30
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f283,plain,
    ( spl8_44
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).

fof(f481,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK2))
    | ~ spl8_30
    | ~ spl8_44
    | ~ spl8_46 ),
    inference(unit_resulting_resolution,[],[f291,f284,f220,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f220,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f219])).

fof(f284,plain,
    ( l1_struct_0(sK2)
    | ~ spl8_44 ),
    inference(avatar_component_clause,[],[f283])).

fof(f497,plain,
    ( spl8_82
    | ~ spl8_28
    | ~ spl8_44
    | ~ spl8_46 ),
    inference(avatar_split_clause,[],[f480,f290,f283,f213,f495])).

fof(f213,plain,
    ( spl8_28
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f480,plain,
    ( r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl8_28
    | ~ spl8_44
    | ~ spl8_46 ),
    inference(unit_resulting_resolution,[],[f284,f291,f214,f80])).

fof(f214,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f213])).

fof(f488,plain,
    ( spl8_80
    | ~ spl8_76 ),
    inference(avatar_split_clause,[],[f471,f467,f486])).

fof(f486,plain,
    ( spl8_80
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_80])])).

fof(f467,plain,
    ( spl8_76
  <=> o_0_0_xboole_0 = sK5(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_76])])).

fof(f471,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_76 ),
    inference(superposition,[],[f89,f468])).

fof(f468,plain,
    ( o_0_0_xboole_0 = sK5(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_76 ),
    inference(avatar_component_clause,[],[f467])).

fof(f89,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f16,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t23_tmap_1.p',existence_m1_subset_1)).

fof(f478,plain,
    ( spl8_78
    | ~ spl8_76 ),
    inference(avatar_split_clause,[],[f470,f467,f476])).

fof(f476,plain,
    ( spl8_78
  <=> r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_78])])).

fof(f470,plain,
    ( r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl8_76 ),
    inference(superposition,[],[f266,f468])).

fof(f266,plain,(
    ! [X0] : r1_tarski(sK5(k1_zfmisc_1(X0)),X0) ),
    inference(unit_resulting_resolution,[],[f89,f95])).

fof(f469,plain,
    ( spl8_76
    | ~ spl8_4
    | ~ spl8_74 ),
    inference(avatar_split_clause,[],[f454,f437,f122,f467])).

fof(f122,plain,
    ( spl8_4
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f437,plain,
    ( spl8_74
  <=> v1_xboole_0(sK5(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_74])])).

fof(f454,plain,
    ( o_0_0_xboole_0 = sK5(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl8_4
    | ~ spl8_74 ),
    inference(unit_resulting_resolution,[],[f438,f185])).

fof(f185,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl8_4 ),
    inference(backward_demodulation,[],[f183,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t23_tmap_1.p',t6_boole)).

fof(f183,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f123,f82])).

fof(f123,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f122])).

fof(f438,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl8_74 ),
    inference(avatar_component_clause,[],[f437])).

fof(f439,plain,
    ( spl8_74
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f432,f122,f437])).

fof(f432,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f89,f369,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t23_tmap_1.p',t2_subset)).

fof(f369,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK5(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f123,f89,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t23_tmap_1.p',t5_subset)).

fof(f430,plain,
    ( spl8_72
    | ~ spl8_70 ),
    inference(avatar_split_clause,[],[f423,f419,f428])).

fof(f428,plain,
    ( spl8_72
  <=> l1_struct_0(sK4(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_72])])).

fof(f419,plain,
    ( spl8_70
  <=> l1_pre_topc(sK4(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_70])])).

fof(f423,plain,
    ( l1_struct_0(sK4(sK3))
    | ~ spl8_70 ),
    inference(unit_resulting_resolution,[],[f420,f83])).

fof(f83,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t23_tmap_1.p',dt_l1_pre_topc)).

fof(f420,plain,
    ( l1_pre_topc(sK4(sK3))
    | ~ spl8_70 ),
    inference(avatar_component_clause,[],[f419])).

fof(f421,plain,
    ( spl8_70
    | ~ spl8_40
    | ~ spl8_60 ),
    inference(avatar_split_clause,[],[f386,f348,f261,f419])).

fof(f261,plain,
    ( spl8_40
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f348,plain,
    ( spl8_60
  <=> m1_pre_topc(sK4(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).

fof(f386,plain,
    ( l1_pre_topc(sK4(sK3))
    | ~ spl8_40
    | ~ spl8_60 ),
    inference(unit_resulting_resolution,[],[f262,f349,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t23_tmap_1.p',dt_m1_pre_topc)).

fof(f349,plain,
    ( m1_pre_topc(sK4(sK3),sK3)
    | ~ spl8_60 ),
    inference(avatar_component_clause,[],[f348])).

fof(f262,plain,
    ( l1_pre_topc(sK3)
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f261])).

fof(f410,plain,
    ( spl8_29
    | ~ spl8_30
    | ~ spl8_44
    | ~ spl8_46 ),
    inference(avatar_contradiction_clause,[],[f409])).

fof(f409,plain,
    ( $false
    | ~ spl8_29
    | ~ spl8_30
    | ~ spl8_44
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f408,f220])).

fof(f408,plain,
    ( ~ r1_tsep_1(sK3,sK2)
    | ~ spl8_29
    | ~ spl8_44
    | ~ spl8_46 ),
    inference(unit_resulting_resolution,[],[f291,f284,f211,f94])).

fof(f211,plain,
    ( ~ r1_tsep_1(sK2,sK3)
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl8_29
  <=> ~ r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f407,plain,
    ( ~ spl8_28
    | spl8_31
    | ~ spl8_44
    | ~ spl8_46 ),
    inference(avatar_contradiction_clause,[],[f406])).

fof(f406,plain,
    ( $false
    | ~ spl8_28
    | ~ spl8_31
    | ~ spl8_44
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f405,f284])).

fof(f405,plain,
    ( ~ l1_struct_0(sK2)
    | ~ spl8_28
    | ~ spl8_31
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f404,f291])).

fof(f404,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ spl8_28
    | ~ spl8_31 ),
    inference(subsumption_resolution,[],[f394,f217])).

fof(f217,plain,
    ( ~ r1_tsep_1(sK3,sK2)
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl8_31
  <=> ~ r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f394,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | ~ spl8_28 ),
    inference(resolution,[],[f94,f214])).

fof(f403,plain,
    ( ~ spl8_28
    | spl8_31
    | ~ spl8_44
    | ~ spl8_46 ),
    inference(avatar_contradiction_clause,[],[f402])).

fof(f402,plain,
    ( $false
    | ~ spl8_28
    | ~ spl8_31
    | ~ spl8_44
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f389,f214])).

fof(f389,plain,
    ( ~ r1_tsep_1(sK2,sK3)
    | ~ spl8_31
    | ~ spl8_44
    | ~ spl8_46 ),
    inference(unit_resulting_resolution,[],[f284,f291,f217,f94])).

fof(f401,plain,
    ( ~ spl8_28
    | spl8_31
    | ~ spl8_44
    | ~ spl8_46 ),
    inference(avatar_contradiction_clause,[],[f400])).

fof(f400,plain,
    ( $false
    | ~ spl8_28
    | ~ spl8_31
    | ~ spl8_44
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f390,f217])).

fof(f390,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl8_28
    | ~ spl8_44
    | ~ spl8_46 ),
    inference(unit_resulting_resolution,[],[f284,f291,f214,f94])).

fof(f399,plain,
    ( ~ spl8_28
    | spl8_31
    | ~ spl8_44
    | ~ spl8_46 ),
    inference(avatar_contradiction_clause,[],[f398])).

fof(f398,plain,
    ( $false
    | ~ spl8_28
    | ~ spl8_31
    | ~ spl8_44
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f391,f291])).

fof(f391,plain,
    ( ~ l1_struct_0(sK3)
    | ~ spl8_28
    | ~ spl8_31
    | ~ spl8_44 ),
    inference(unit_resulting_resolution,[],[f284,f217,f214,f94])).

fof(f397,plain,
    ( ~ spl8_28
    | spl8_31
    | ~ spl8_44
    | ~ spl8_46 ),
    inference(avatar_contradiction_clause,[],[f396])).

fof(f396,plain,
    ( $false
    | ~ spl8_28
    | ~ spl8_31
    | ~ spl8_44
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f392,f284])).

fof(f392,plain,
    ( ~ l1_struct_0(sK2)
    | ~ spl8_28
    | ~ spl8_31
    | ~ spl8_46 ),
    inference(unit_resulting_resolution,[],[f291,f217,f214,f94])).

fof(f395,plain,
    ( ~ spl8_28
    | spl8_31
    | ~ spl8_44
    | ~ spl8_46 ),
    inference(avatar_contradiction_clause,[],[f393])).

fof(f393,plain,
    ( $false
    | ~ spl8_28
    | ~ spl8_31
    | ~ spl8_44
    | ~ spl8_46 ),
    inference(unit_resulting_resolution,[],[f284,f291,f217,f214,f94])).

fof(f385,plain,
    ( spl8_68
    | ~ spl8_66 ),
    inference(avatar_split_clause,[],[f378,f374,f383])).

fof(f383,plain,
    ( spl8_68
  <=> l1_struct_0(sK4(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_68])])).

fof(f374,plain,
    ( spl8_66
  <=> l1_pre_topc(sK4(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_66])])).

fof(f378,plain,
    ( l1_struct_0(sK4(sK2))
    | ~ spl8_66 ),
    inference(unit_resulting_resolution,[],[f375,f83])).

fof(f375,plain,
    ( l1_pre_topc(sK4(sK2))
    | ~ spl8_66 ),
    inference(avatar_component_clause,[],[f374])).

fof(f376,plain,
    ( spl8_66
    | ~ spl8_38
    | ~ spl8_58 ),
    inference(avatar_split_clause,[],[f368,f341,f254,f374])).

fof(f341,plain,
    ( spl8_58
  <=> m1_pre_topc(sK4(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_58])])).

fof(f368,plain,
    ( l1_pre_topc(sK4(sK2))
    | ~ spl8_38
    | ~ spl8_58 ),
    inference(unit_resulting_resolution,[],[f255,f342,f84])).

fof(f342,plain,
    ( m1_pre_topc(sK4(sK2),sK2)
    | ~ spl8_58 ),
    inference(avatar_component_clause,[],[f341])).

fof(f367,plain,
    ( spl8_64
    | ~ spl8_62 ),
    inference(avatar_split_clause,[],[f360,f356,f365])).

fof(f365,plain,
    ( spl8_64
  <=> l1_struct_0(sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_64])])).

fof(f356,plain,
    ( spl8_62
  <=> l1_pre_topc(sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).

fof(f360,plain,
    ( l1_struct_0(sK4(sK1))
    | ~ spl8_62 ),
    inference(unit_resulting_resolution,[],[f357,f83])).

fof(f357,plain,
    ( l1_pre_topc(sK4(sK1))
    | ~ spl8_62 ),
    inference(avatar_component_clause,[],[f356])).

fof(f358,plain,
    ( spl8_62
    | ~ spl8_36
    | ~ spl8_56 ),
    inference(avatar_split_clause,[],[f351,f334,f247,f356])).

fof(f247,plain,
    ( spl8_36
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f334,plain,
    ( spl8_56
  <=> m1_pre_topc(sK4(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).

fof(f351,plain,
    ( l1_pre_topc(sK4(sK1))
    | ~ spl8_36
    | ~ spl8_56 ),
    inference(unit_resulting_resolution,[],[f248,f335,f84])).

fof(f335,plain,
    ( m1_pre_topc(sK4(sK1),sK1)
    | ~ spl8_56 ),
    inference(avatar_component_clause,[],[f334])).

fof(f248,plain,
    ( l1_pre_topc(sK1)
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f247])).

fof(f350,plain,
    ( spl8_60
    | ~ spl8_40 ),
    inference(avatar_split_clause,[],[f270,f261,f348])).

fof(f270,plain,
    ( m1_pre_topc(sK4(sK3),sK3)
    | ~ spl8_40 ),
    inference(unit_resulting_resolution,[],[f262,f86])).

fof(f86,plain,(
    ! [X0] :
      ( m1_pre_topc(sK4(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( m1_pre_topc(sK4(X0),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X1] : m1_pre_topc(X1,X0)
     => m1_pre_topc(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] : m1_pre_topc(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t23_tmap_1.p',existence_m1_pre_topc)).

fof(f343,plain,
    ( spl8_58
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f268,f254,f341])).

fof(f268,plain,
    ( m1_pre_topc(sK4(sK2),sK2)
    | ~ spl8_38 ),
    inference(unit_resulting_resolution,[],[f255,f86])).

fof(f336,plain,
    ( spl8_56
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f264,f247,f334])).

fof(f264,plain,
    ( m1_pre_topc(sK4(sK1),sK1)
    | ~ spl8_36 ),
    inference(unit_resulting_resolution,[],[f248,f86])).

fof(f326,plain,
    ( spl8_54
    | ~ spl8_50 ),
    inference(avatar_split_clause,[],[f312,f308,f324])).

fof(f324,plain,
    ( spl8_54
  <=> l1_struct_0(sK4(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).

fof(f308,plain,
    ( spl8_50
  <=> l1_pre_topc(sK4(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f312,plain,
    ( l1_struct_0(sK4(sK7))
    | ~ spl8_50 ),
    inference(unit_resulting_resolution,[],[f309,f83])).

fof(f309,plain,
    ( l1_pre_topc(sK4(sK7))
    | ~ spl8_50 ),
    inference(avatar_component_clause,[],[f308])).

fof(f319,plain,
    ( spl8_52
    | ~ spl8_48 ),
    inference(avatar_split_clause,[],[f301,f297,f317])).

fof(f317,plain,
    ( spl8_52
  <=> l1_struct_0(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f297,plain,
    ( spl8_48
  <=> l1_pre_topc(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).

fof(f301,plain,
    ( l1_struct_0(sK4(sK0))
    | ~ spl8_48 ),
    inference(unit_resulting_resolution,[],[f298,f83])).

fof(f298,plain,
    ( l1_pre_topc(sK4(sK0))
    | ~ spl8_48 ),
    inference(avatar_component_clause,[],[f297])).

fof(f310,plain,
    ( spl8_50
    | ~ spl8_8
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f242,f235,f136,f308])).

fof(f136,plain,
    ( spl8_8
  <=> l1_pre_topc(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f235,plain,
    ( spl8_34
  <=> m1_pre_topc(sK4(sK7),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f242,plain,
    ( l1_pre_topc(sK4(sK7))
    | ~ spl8_8
    | ~ spl8_34 ),
    inference(unit_resulting_resolution,[],[f137,f236,f84])).

fof(f236,plain,
    ( m1_pre_topc(sK4(sK7),sK7)
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f235])).

fof(f137,plain,
    ( l1_pre_topc(sK7)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f136])).

fof(f299,plain,
    ( spl8_48
    | ~ spl8_2
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f241,f228,f115,f297])).

fof(f115,plain,
    ( spl8_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f228,plain,
    ( spl8_32
  <=> m1_pre_topc(sK4(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f241,plain,
    ( l1_pre_topc(sK4(sK0))
    | ~ spl8_2
    | ~ spl8_32 ),
    inference(unit_resulting_resolution,[],[f116,f229,f84])).

fof(f229,plain,
    ( m1_pre_topc(sK4(sK0),sK0)
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f228])).

fof(f116,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f115])).

fof(f292,plain,
    ( spl8_46
    | ~ spl8_40 ),
    inference(avatar_split_clause,[],[f271,f261,f290])).

fof(f271,plain,
    ( l1_struct_0(sK3)
    | ~ spl8_40 ),
    inference(unit_resulting_resolution,[],[f262,f83])).

fof(f285,plain,
    ( spl8_44
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f269,f254,f283])).

fof(f269,plain,
    ( l1_struct_0(sK2)
    | ~ spl8_38 ),
    inference(unit_resulting_resolution,[],[f255,f83])).

fof(f278,plain,
    ( spl8_42
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f265,f247,f276])).

fof(f265,plain,
    ( l1_struct_0(sK1)
    | ~ spl8_36 ),
    inference(unit_resulting_resolution,[],[f248,f83])).

fof(f263,plain,
    ( spl8_40
    | ~ spl8_2
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f240,f157,f115,f261])).

fof(f157,plain,
    ( spl8_14
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f240,plain,
    ( l1_pre_topc(sK3)
    | ~ spl8_2
    | ~ spl8_14 ),
    inference(unit_resulting_resolution,[],[f116,f158,f84])).

fof(f158,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f157])).

fof(f256,plain,
    ( spl8_38
    | ~ spl8_2
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f239,f150,f115,f254])).

fof(f150,plain,
    ( spl8_12
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f239,plain,
    ( l1_pre_topc(sK2)
    | ~ spl8_2
    | ~ spl8_12 ),
    inference(unit_resulting_resolution,[],[f116,f151,f84])).

fof(f151,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f150])).

fof(f249,plain,
    ( spl8_36
    | ~ spl8_2
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f238,f143,f115,f247])).

fof(f143,plain,
    ( spl8_10
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f238,plain,
    ( l1_pre_topc(sK1)
    | ~ spl8_2
    | ~ spl8_10 ),
    inference(unit_resulting_resolution,[],[f116,f144,f84])).

fof(f144,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f143])).

fof(f237,plain,
    ( spl8_34
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f223,f136,f235])).

fof(f223,plain,
    ( m1_pre_topc(sK4(sK7),sK7)
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f137,f86])).

fof(f230,plain,
    ( spl8_32
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f222,f115,f228])).

fof(f222,plain,
    ( m1_pre_topc(sK4(sK0),sK0)
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f116,f86])).

fof(f221,plain,
    ( spl8_28
    | spl8_30 ),
    inference(avatar_split_clause,[],[f78,f219,f213])).

fof(f78,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,
    ( ( r1_tsep_1(sK3,sK2)
      | r1_tsep_1(sK2,sK3) )
    & ( ~ r1_tsep_1(sK3,sK1)
      | ~ r1_tsep_1(sK1,sK3) )
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK3,sK0)
    & m1_pre_topc(sK2,sK0)
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f58,f57,f56,f55])).

fof(f55,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X2,X3) )
                    & ( ~ r1_tsep_1(X3,X1)
                      | ~ r1_tsep_1(X1,X3) )
                    & m1_pre_topc(X1,X2)
                    & m1_pre_topc(X3,X0) )
                & m1_pre_topc(X2,X0) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,sK0) )
              & m1_pre_topc(X2,sK0) )
          & m1_pre_topc(X1,sK0) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( r1_tsep_1(X3,X2)
                  | r1_tsep_1(X2,X3) )
                & ( ~ r1_tsep_1(X3,sK1)
                  | ~ r1_tsep_1(sK1,X3) )
                & m1_pre_topc(sK1,X2)
                & m1_pre_topc(X3,X0) )
            & m1_pre_topc(X2,X0) )
        & m1_pre_topc(sK1,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( r1_tsep_1(X3,X2)
                | r1_tsep_1(X2,X3) )
              & ( ~ r1_tsep_1(X3,X1)
                | ~ r1_tsep_1(X1,X3) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X3,X0) )
          & m1_pre_topc(X2,X0) )
     => ( ? [X3] :
            ( ( r1_tsep_1(X3,sK2)
              | r1_tsep_1(sK2,X3) )
            & ( ~ r1_tsep_1(X3,X1)
              | ~ r1_tsep_1(X1,X3) )
            & m1_pre_topc(X1,sK2)
            & m1_pre_topc(X3,X0) )
        & m1_pre_topc(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( r1_tsep_1(X3,X2)
            | r1_tsep_1(X2,X3) )
          & ( ~ r1_tsep_1(X3,X1)
            | ~ r1_tsep_1(X1,X3) )
          & m1_pre_topc(X1,X2)
          & m1_pre_topc(X3,X0) )
     => ( ( r1_tsep_1(sK3,X2)
          | r1_tsep_1(X2,sK3) )
        & ( ~ r1_tsep_1(sK3,X1)
          | ~ r1_tsep_1(X1,sK3) )
        & m1_pre_topc(X1,X2)
        & m1_pre_topc(sK3,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ! [X3] :
                    ( m1_pre_topc(X3,X0)
                   => ( m1_pre_topc(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( m1_pre_topc(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t23_tmap_1.p',t23_tmap_1)).

fof(f208,plain,
    ( ~ spl8_25
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f77,f206,f200])).

fof(f77,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | ~ r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f193,plain,
    ( spl8_22
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f183,f122,f191])).

fof(f191,plain,
    ( spl8_22
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f182,plain,
    ( spl8_20
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f168,f136,f180])).

fof(f180,plain,
    ( spl8_20
  <=> l1_struct_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f168,plain,
    ( l1_struct_0(sK7)
    | ~ spl8_8 ),
    inference(unit_resulting_resolution,[],[f137,f83])).

fof(f175,plain,
    ( spl8_18
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f167,f115,f173])).

fof(f173,plain,
    ( spl8_18
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f167,plain,
    ( l1_struct_0(sK0)
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f116,f83])).

fof(f166,plain,(
    spl8_16 ),
    inference(avatar_split_clause,[],[f76,f164])).

fof(f76,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f159,plain,(
    spl8_14 ),
    inference(avatar_split_clause,[],[f75,f157])).

fof(f75,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f152,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f74,f150])).

fof(f74,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f145,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f73,f143])).

fof(f73,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f138,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f103,f136])).

fof(f103,plain,(
    l1_pre_topc(sK7) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    l1_pre_topc(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f13,f69])).

fof(f69,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK7) ),
    introduced(choice_axiom,[])).

fof(f13,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t23_tmap_1.p',existence_l1_pre_topc)).

fof(f131,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f102,f129])).

fof(f129,plain,
    ( spl8_6
  <=> l1_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f102,plain,(
    l1_struct_0(sK6) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    l1_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f14,f67])).

fof(f67,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK6) ),
    introduced(choice_axiom,[])).

fof(f14,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t23_tmap_1.p',existence_l1_struct_0)).

fof(f124,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f79,f122])).

fof(f79,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t23_tmap_1.p',dt_o_0_0_xboole_0)).

fof(f117,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f72,f115])).

fof(f72,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f110,plain,(
    spl8_0 ),
    inference(avatar_split_clause,[],[f71,f108])).

fof(f108,plain,
    ( spl8_0
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f71,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f59])).
%------------------------------------------------------------------------------
