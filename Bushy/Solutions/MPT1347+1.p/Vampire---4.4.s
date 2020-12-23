%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_2__t72_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:43 EDT 2019

% Result     : Theorem 1.23s
% Output     : Refutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :  499 (1309 expanded)
%              Number of leaves         :   93 ( 581 expanded)
%              Depth                    :   15
%              Number of atoms          : 2538 (8229 expanded)
%              Number of equality atoms :  250 (1041 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10336,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f205,f219,f226,f255,f268,f287,f298,f308,f322,f344,f437,f459,f492,f515,f532,f542,f549,f647,f659,f672,f685,f691,f706,f709,f723,f731,f739,f746,f762,f778,f786,f804,f811,f825,f836,f865,f871,f881,f886,f893,f897,f1043,f1243,f1250,f1261,f1294,f1379,f1401,f1560,f1991,f2076,f2077,f2159,f2174,f2181,f2205,f2215,f2223,f2233,f2264,f3985,f4029,f4040,f4051,f7435,f10215,f10276,f10335])).

fof(f10335,plain,
    ( ~ spl9_250
    | ~ spl9_258
    | spl9_261
    | ~ spl9_1004
    | ~ spl9_1006 ),
    inference(avatar_contradiction_clause,[],[f10334])).

fof(f10334,plain,
    ( $false
    | ~ spl9_250
    | ~ spl9_258
    | ~ spl9_261
    | ~ spl9_1004
    | ~ spl9_1006 ),
    inference(subsumption_resolution,[],[f10333,f2232])).

fof(f2232,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | ~ spl9_261 ),
    inference(avatar_component_clause,[],[f2231])).

fof(f2231,plain,
    ( spl9_261
  <=> ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_261])])).

fof(f10333,plain,
    ( v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | ~ spl9_250
    | ~ spl9_258
    | ~ spl9_1004
    | ~ spl9_1006 ),
    inference(forward_demodulation,[],[f10332,f2218])).

fof(f2218,plain,
    ( ! [X0] : k10_relat_1(sK2,X0) = k10_relat_1(sK2,k9_relat_1(sK2,k10_relat_1(sK2,X0)))
    | ~ spl9_258 ),
    inference(avatar_component_clause,[],[f2217])).

fof(f2217,plain,
    ( spl9_258
  <=> ! [X0] : k10_relat_1(sK2,X0) = k10_relat_1(sK2,k9_relat_1(sK2,k10_relat_1(sK2,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_258])])).

fof(f10332,plain,
    ( v4_pre_topc(k10_relat_1(sK2,k9_relat_1(sK2,k10_relat_1(sK2,sK4(sK0,sK1,sK2)))),sK0)
    | ~ spl9_250
    | ~ spl9_1004
    | ~ spl9_1006 ),
    inference(subsumption_resolution,[],[f10321,f2180])).

fof(f2180,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | ~ spl9_250 ),
    inference(avatar_component_clause,[],[f2179])).

fof(f2179,plain,
    ( spl9_250
  <=> v4_pre_topc(sK4(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_250])])).

fof(f10321,plain,
    ( ~ v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | v4_pre_topc(k10_relat_1(sK2,k9_relat_1(sK2,k10_relat_1(sK2,sK4(sK0,sK1,sK2)))),sK0)
    | ~ spl9_1004
    | ~ spl9_1006 ),
    inference(superposition,[],[f10189,f10202])).

fof(f10202,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK4(sK0,sK1,sK2))) = sK4(sK0,sK1,sK2)
    | ~ spl9_1006 ),
    inference(avatar_component_clause,[],[f10201])).

fof(f10201,plain,
    ( spl9_1006
  <=> k9_relat_1(sK2,k10_relat_1(sK2,sK4(sK0,sK1,sK2))) = sK4(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1006])])).

fof(f10189,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(k9_relat_1(sK2,X0),sK1)
        | v4_pre_topc(k10_relat_1(sK2,k9_relat_1(sK2,X0)),sK0) )
    | ~ spl9_1004 ),
    inference(avatar_component_clause,[],[f10188])).

fof(f10188,plain,
    ( spl9_1004
  <=> ! [X0] :
        ( ~ v4_pre_topc(k9_relat_1(sK2,X0),sK1)
        | v4_pre_topc(k10_relat_1(sK2,k9_relat_1(sK2,X0)),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1004])])).

fof(f10276,plain,
    ( spl9_1006
    | ~ spl9_126
    | ~ spl9_256 ),
    inference(avatar_split_clause,[],[f8226,f2203,f869,f10201])).

fof(f869,plain,
    ( spl9_126
  <=> ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK1))
        | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_126])])).

fof(f2203,plain,
    ( spl9_256
  <=> r1_tarski(sK4(sK0,sK1,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_256])])).

fof(f8226,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK4(sK0,sK1,sK2))) = sK4(sK0,sK1,sK2)
    | ~ spl9_126
    | ~ spl9_256 ),
    inference(resolution,[],[f2204,f870])).

fof(f870,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK1))
        | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 )
    | ~ spl9_126 ),
    inference(avatar_component_clause,[],[f869])).

fof(f2204,plain,
    ( r1_tarski(sK4(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl9_256 ),
    inference(avatar_component_clause,[],[f2203])).

fof(f10215,plain,
    ( spl9_1004
    | ~ spl9_130
    | ~ spl9_242
    | ~ spl9_246 ),
    inference(avatar_split_clause,[],[f9559,f2157,f2067,f879,f10188])).

fof(f879,plain,
    ( spl9_130
  <=> ! [X4] : m1_subset_1(k10_relat_1(sK2,X4),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_130])])).

fof(f2067,plain,
    ( spl9_242
  <=> ! [X0] : k9_relat_1(sK2,X0) = k9_relat_1(sK2,k10_relat_1(sK2,k9_relat_1(sK2,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_242])])).

fof(f2157,plain,
    ( spl9_246
  <=> ! [X4] :
        ( ~ v4_pre_topc(k9_relat_1(sK2,X4),sK1)
        | v4_pre_topc(X4,sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_246])])).

fof(f9559,plain,
    ( ! [X3] :
        ( ~ v4_pre_topc(k9_relat_1(sK2,X3),sK1)
        | v4_pre_topc(k10_relat_1(sK2,k9_relat_1(sK2,X3)),sK0) )
    | ~ spl9_130
    | ~ spl9_242
    | ~ spl9_246 ),
    inference(subsumption_resolution,[],[f9552,f880])).

fof(f880,plain,
    ( ! [X4] : m1_subset_1(k10_relat_1(sK2,X4),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_130 ),
    inference(avatar_component_clause,[],[f879])).

fof(f9552,plain,
    ( ! [X3] :
        ( ~ v4_pre_topc(k9_relat_1(sK2,X3),sK1)
        | v4_pre_topc(k10_relat_1(sK2,k9_relat_1(sK2,X3)),sK0)
        | ~ m1_subset_1(k10_relat_1(sK2,k9_relat_1(sK2,X3)),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl9_242
    | ~ spl9_246 ),
    inference(superposition,[],[f2158,f2068])).

fof(f2068,plain,
    ( ! [X0] : k9_relat_1(sK2,X0) = k9_relat_1(sK2,k10_relat_1(sK2,k9_relat_1(sK2,X0)))
    | ~ spl9_242 ),
    inference(avatar_component_clause,[],[f2067])).

fof(f2158,plain,
    ( ! [X4] :
        ( ~ v4_pre_topc(k9_relat_1(sK2,X4),sK1)
        | v4_pre_topc(X4,sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl9_246 ),
    inference(avatar_component_clause,[],[f2157])).

fof(f7435,plain,
    ( ~ spl9_0
    | ~ spl9_4
    | ~ spl9_14
    | spl9_17
    | ~ spl9_22
    | ~ spl9_24
    | ~ spl9_26
    | ~ spl9_32
    | ~ spl9_56
    | ~ spl9_60
    | ~ spl9_98
    | ~ spl9_102
    | ~ spl9_174 ),
    inference(avatar_contradiction_clause,[],[f7434])).

fof(f7434,plain,
    ( $false
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_22
    | ~ spl9_24
    | ~ spl9_26
    | ~ spl9_32
    | ~ spl9_56
    | ~ spl9_60
    | ~ spl9_98
    | ~ spl9_102
    | ~ spl9_174 ),
    inference(subsumption_resolution,[],[f7409,f514])).

fof(f514,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl9_56 ),
    inference(avatar_component_clause,[],[f513])).

fof(f513,plain,
    ( spl9_56
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_56])])).

fof(f7409,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_22
    | ~ spl9_24
    | ~ spl9_26
    | ~ spl9_32
    | ~ spl9_60
    | ~ spl9_98
    | ~ spl9_102
    | ~ spl9_174 ),
    inference(subsumption_resolution,[],[f7408,f761])).

fof(f761,plain,
    ( v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ spl9_102 ),
    inference(avatar_component_clause,[],[f760])).

fof(f760,plain,
    ( spl9_102
  <=> v5_pre_topc(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_102])])).

fof(f7408,plain,
    ( ~ v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_22
    | ~ spl9_24
    | ~ spl9_26
    | ~ spl9_32
    | ~ spl9_60
    | ~ spl9_98
    | ~ spl9_174 ),
    inference(forward_demodulation,[],[f7407,f738])).

fof(f738,plain,
    ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ spl9_98 ),
    inference(avatar_component_clause,[],[f737])).

fof(f737,plain,
    ( spl9_98
  <=> k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_98])])).

fof(f7407,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_22
    | ~ spl9_24
    | ~ spl9_26
    | ~ spl9_32
    | ~ spl9_60
    | ~ spl9_174 ),
    inference(subsumption_resolution,[],[f7406,f343])).

fof(f343,plain,
    ( u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl9_32 ),
    inference(avatar_component_clause,[],[f342])).

fof(f342,plain,
    ( spl9_32
  <=> u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f7406,plain,
    ( u1_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_22
    | ~ spl9_24
    | ~ spl9_26
    | ~ spl9_60
    | ~ spl9_174 ),
    inference(forward_demodulation,[],[f7405,f297])).

fof(f297,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f296])).

fof(f296,plain,
    ( spl9_24
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f7405,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_22
    | ~ spl9_26
    | ~ spl9_60
    | ~ spl9_174 ),
    inference(subsumption_resolution,[],[f7404,f307])).

fof(f307,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f306])).

fof(f306,plain,
    ( spl9_26
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f7404,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_22
    | ~ spl9_60
    | ~ spl9_174 ),
    inference(forward_demodulation,[],[f7403,f531])).

fof(f531,plain,
    ( u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl9_60 ),
    inference(avatar_component_clause,[],[f530])).

fof(f530,plain,
    ( spl9_60
  <=> u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_60])])).

fof(f7403,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_22
    | ~ spl9_174 ),
    inference(subsumption_resolution,[],[f7402,f204])).

fof(f204,plain,
    ( l1_pre_topc(sK0)
    | ~ spl9_0 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl9_0
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_0])])).

fof(f7402,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_4
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_22
    | ~ spl9_174 ),
    inference(subsumption_resolution,[],[f7401,f218])).

fof(f218,plain,
    ( l1_pre_topc(sK1)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl9_4
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f7401,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_22
    | ~ spl9_174 ),
    inference(subsumption_resolution,[],[f7400,f286])).

fof(f286,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f285])).

fof(f285,plain,
    ( spl9_22
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f7400,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_14
    | ~ spl9_17
    | ~ spl9_174 ),
    inference(subsumption_resolution,[],[f6091,f258])).

fof(f258,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f257])).

fof(f257,plain,
    ( spl9_17
  <=> ~ v3_tops_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f6091,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | v3_tops_2(sK2,sK0,sK1)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_14
    | ~ spl9_174 ),
    inference(resolution,[],[f254,f1293])).

fof(f1293,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v5_pre_topc(sK2,X0,X1)
        | v3_tops_2(sK2,X0,X1)
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
        | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) != k2_struct_0(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2),X1,X0)
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl9_174 ),
    inference(avatar_component_clause,[],[f1292])).

fof(f1292,plain,
    ( spl9_174
  <=> ! [X1,X0] :
        ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2),X1,X0)
        | ~ v5_pre_topc(sK2,X0,X1)
        | v3_tops_2(sK2,X0,X1)
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
        | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) != k2_struct_0(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_174])])).

fof(f254,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl9_14
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f4051,plain,
    ( ~ spl9_0
    | ~ spl9_4
    | ~ spl9_100
    | spl9_103
    | ~ spl9_122
    | ~ spl9_150
    | spl9_435 ),
    inference(avatar_contradiction_clause,[],[f4050])).

fof(f4050,plain,
    ( $false
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_100
    | ~ spl9_103
    | ~ spl9_122
    | ~ spl9_150
    | ~ spl9_435 ),
    inference(subsumption_resolution,[],[f4049,f218])).

fof(f4049,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl9_0
    | ~ spl9_100
    | ~ spl9_103
    | ~ spl9_122
    | ~ spl9_150
    | ~ spl9_435 ),
    inference(subsumption_resolution,[],[f4048,f204])).

fof(f4048,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ spl9_100
    | ~ spl9_103
    | ~ spl9_122
    | ~ spl9_150
    | ~ spl9_435 ),
    inference(subsumption_resolution,[],[f4047,f745])).

fof(f745,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl9_100 ),
    inference(avatar_component_clause,[],[f744])).

fof(f744,plain,
    ( spl9_100
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_100])])).

fof(f4047,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ spl9_103
    | ~ spl9_122
    | ~ spl9_150
    | ~ spl9_435 ),
    inference(subsumption_resolution,[],[f4046,f835])).

fof(f835,plain,
    ( v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl9_122 ),
    inference(avatar_component_clause,[],[f834])).

fof(f834,plain,
    ( spl9_122
  <=> v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_122])])).

fof(f4046,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ spl9_103
    | ~ spl9_150
    | ~ spl9_435 ),
    inference(subsumption_resolution,[],[f4045,f1042])).

fof(f1042,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl9_150 ),
    inference(avatar_component_clause,[],[f1041])).

fof(f1041,plain,
    ( spl9_150
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_150])])).

fof(f4045,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ spl9_103
    | ~ spl9_435 ),
    inference(subsumption_resolution,[],[f4042,f758])).

fof(f758,plain,
    ( ~ v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ spl9_103 ),
    inference(avatar_component_clause,[],[f757])).

fof(f757,plain,
    ( spl9_103
  <=> ~ v5_pre_topc(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_103])])).

fof(f4042,plain,
    ( v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ spl9_435 ),
    inference(resolution,[],[f4039,f146])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f109])).

fof(f109,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0)
                    & v4_pre_topc(sK4(X0,X1,X2),X1)
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f107,f108])).

fof(f108,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0)
        & v4_pre_topc(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f107,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f106])).

fof(f106,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      | ~ v4_pre_topc(X3,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( v4_pre_topc(X3,X1)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',d12_pre_topc)).

fof(f4039,plain,
    ( ~ m1_subset_1(sK4(sK1,sK0,k2_funct_1(sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_435 ),
    inference(avatar_component_clause,[],[f4038])).

fof(f4038,plain,
    ( spl9_435
  <=> ~ m1_subset_1(sK4(sK1,sK0,k2_funct_1(sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_435])])).

fof(f4040,plain,
    ( ~ spl9_435
    | ~ spl9_248
    | spl9_431
    | ~ spl9_432 ),
    inference(avatar_split_clause,[],[f4032,f4027,f3983,f2172,f4038])).

fof(f2172,plain,
    ( spl9_248
  <=> ! [X4] :
        ( v4_pre_topc(k9_relat_1(sK2,X4),sK1)
        | ~ v4_pre_topc(X4,sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_248])])).

fof(f3983,plain,
    ( spl9_431
  <=> ~ v4_pre_topc(k9_relat_1(sK2,sK4(sK1,sK0,k2_funct_1(sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_431])])).

fof(f4027,plain,
    ( spl9_432
  <=> v4_pre_topc(sK4(sK1,sK0,k2_funct_1(sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_432])])).

fof(f4032,plain,
    ( ~ m1_subset_1(sK4(sK1,sK0,k2_funct_1(sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_248
    | ~ spl9_431
    | ~ spl9_432 ),
    inference(subsumption_resolution,[],[f4030,f3984])).

fof(f3984,plain,
    ( ~ v4_pre_topc(k9_relat_1(sK2,sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | ~ spl9_431 ),
    inference(avatar_component_clause,[],[f3983])).

fof(f4030,plain,
    ( v4_pre_topc(k9_relat_1(sK2,sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | ~ m1_subset_1(sK4(sK1,sK0,k2_funct_1(sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_248
    | ~ spl9_432 ),
    inference(resolution,[],[f4028,f2173])).

fof(f2173,plain,
    ( ! [X4] :
        ( ~ v4_pre_topc(X4,sK0)
        | v4_pre_topc(k9_relat_1(sK2,X4),sK1)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl9_248 ),
    inference(avatar_component_clause,[],[f2172])).

fof(f4028,plain,
    ( v4_pre_topc(sK4(sK1,sK0,k2_funct_1(sK2)),sK0)
    | ~ spl9_432 ),
    inference(avatar_component_clause,[],[f4027])).

fof(f4029,plain,
    ( spl9_432
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_100
    | spl9_103
    | ~ spl9_122
    | ~ spl9_150 ),
    inference(avatar_split_clause,[],[f4022,f1041,f834,f757,f744,f217,f203,f4027])).

fof(f4022,plain,
    ( v4_pre_topc(sK4(sK1,sK0,k2_funct_1(sK2)),sK0)
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_100
    | ~ spl9_103
    | ~ spl9_122
    | ~ spl9_150 ),
    inference(subsumption_resolution,[],[f3557,f758])).

fof(f3557,plain,
    ( v4_pre_topc(sK4(sK1,sK0,k2_funct_1(sK2)),sK0)
    | v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_100
    | ~ spl9_122
    | ~ spl9_150 ),
    inference(subsumption_resolution,[],[f3556,f218])).

fof(f3556,plain,
    ( v4_pre_topc(sK4(sK1,sK0,k2_funct_1(sK2)),sK0)
    | v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ spl9_0
    | ~ spl9_100
    | ~ spl9_122
    | ~ spl9_150 ),
    inference(subsumption_resolution,[],[f3555,f204])).

fof(f3555,plain,
    ( v4_pre_topc(sK4(sK1,sK0,k2_funct_1(sK2)),sK0)
    | v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ spl9_100
    | ~ spl9_122
    | ~ spl9_150 ),
    inference(subsumption_resolution,[],[f3554,f745])).

fof(f3554,plain,
    ( v4_pre_topc(sK4(sK1,sK0,k2_funct_1(sK2)),sK0)
    | v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ spl9_122
    | ~ spl9_150 ),
    inference(subsumption_resolution,[],[f1871,f1042])).

fof(f1871,plain,
    ( v4_pre_topc(sK4(sK1,sK0,k2_funct_1(sK2)),sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ spl9_122 ),
    inference(resolution,[],[f835,f147])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v4_pre_topc(sK4(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f109])).

fof(f3985,plain,
    ( ~ spl9_431
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_100
    | spl9_103
    | ~ spl9_122
    | ~ spl9_150
    | ~ spl9_244 ),
    inference(avatar_split_clause,[],[f3978,f2072,f1041,f834,f757,f744,f217,f203,f3983])).

fof(f2072,plain,
    ( spl9_244
  <=> ! [X2] : k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2),X2) = k9_relat_1(sK2,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_244])])).

fof(f3978,plain,
    ( ~ v4_pre_topc(k9_relat_1(sK2,sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_100
    | ~ spl9_103
    | ~ spl9_122
    | ~ spl9_150
    | ~ spl9_244 ),
    inference(subsumption_resolution,[],[f3977,f218])).

fof(f3977,plain,
    ( ~ v4_pre_topc(k9_relat_1(sK2,sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl9_0
    | ~ spl9_100
    | ~ spl9_103
    | ~ spl9_122
    | ~ spl9_150
    | ~ spl9_244 ),
    inference(subsumption_resolution,[],[f3976,f204])).

fof(f3976,plain,
    ( ~ v4_pre_topc(k9_relat_1(sK2,sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ spl9_100
    | ~ spl9_103
    | ~ spl9_122
    | ~ spl9_150
    | ~ spl9_244 ),
    inference(subsumption_resolution,[],[f3975,f745])).

fof(f3975,plain,
    ( ~ v4_pre_topc(k9_relat_1(sK2,sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ spl9_103
    | ~ spl9_122
    | ~ spl9_150
    | ~ spl9_244 ),
    inference(subsumption_resolution,[],[f3974,f835])).

fof(f3974,plain,
    ( ~ v4_pre_topc(k9_relat_1(sK2,sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ spl9_103
    | ~ spl9_150
    | ~ spl9_244 ),
    inference(subsumption_resolution,[],[f3973,f1042])).

fof(f3973,plain,
    ( ~ v4_pre_topc(k9_relat_1(sK2,sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ spl9_103
    | ~ spl9_244 ),
    inference(subsumption_resolution,[],[f3972,f758])).

fof(f3972,plain,
    ( ~ v4_pre_topc(k9_relat_1(sK2,sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ spl9_244 ),
    inference(superposition,[],[f148,f2073])).

fof(f2073,plain,
    ( ! [X2] : k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2),X2) = k9_relat_1(sK2,X2)
    | ~ spl9_244 ),
    inference(avatar_component_clause,[],[f2072])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0)
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f109])).

fof(f2264,plain,
    ( spl9_258
    | ~ spl9_132
    | ~ spl9_210 ),
    inference(avatar_split_clause,[],[f2044,f1558,f884,f2217])).

fof(f884,plain,
    ( spl9_132
  <=> ! [X0] : r1_tarski(k10_relat_1(sK2,X0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_132])])).

fof(f1558,plain,
    ( spl9_210
  <=> ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_210])])).

fof(f2044,plain,
    ( ! [X0] : k10_relat_1(sK2,X0) = k10_relat_1(sK2,k9_relat_1(sK2,k10_relat_1(sK2,X0)))
    | ~ spl9_132
    | ~ spl9_210 ),
    inference(resolution,[],[f1559,f885])).

fof(f885,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK2,X0),u1_struct_0(sK0))
    | ~ spl9_132 ),
    inference(avatar_component_clause,[],[f884])).

fof(f1559,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 )
    | ~ spl9_210 ),
    inference(avatar_component_clause,[],[f1558])).

fof(f2233,plain,
    ( ~ spl9_261
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_22
    | spl9_57
    | ~ spl9_114 ),
    inference(avatar_split_clause,[],[f2226,f802,f510,f285,f253,f224,f217,f203,f2231])).

fof(f224,plain,
    ( spl9_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f510,plain,
    ( spl9_57
  <=> ~ v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_57])])).

fof(f802,plain,
    ( spl9_114
  <=> ! [X4] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4) = k10_relat_1(sK2,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_114])])).

fof(f2226,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_22
    | ~ spl9_57
    | ~ spl9_114 ),
    inference(subsumption_resolution,[],[f2137,f511])).

fof(f511,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ spl9_57 ),
    inference(avatar_component_clause,[],[f510])).

fof(f2137,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_22
    | ~ spl9_114 ),
    inference(subsumption_resolution,[],[f2136,f204])).

fof(f2136,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_22
    | ~ spl9_114 ),
    inference(subsumption_resolution,[],[f2135,f218])).

fof(f2135,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_22
    | ~ spl9_114 ),
    inference(subsumption_resolution,[],[f2134,f225])).

fof(f225,plain,
    ( v1_funct_1(sK2)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f224])).

fof(f2134,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_14
    | ~ spl9_22
    | ~ spl9_114 ),
    inference(subsumption_resolution,[],[f2133,f254])).

fof(f2133,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_22
    | ~ spl9_114 ),
    inference(subsumption_resolution,[],[f1965,f286])).

fof(f1965,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_114 ),
    inference(superposition,[],[f148,f803])).

fof(f803,plain,
    ( ! [X4] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4) = k10_relat_1(sK2,X4)
    | ~ spl9_114 ),
    inference(avatar_component_clause,[],[f802])).

fof(f2223,plain,
    ( spl9_242
    | ~ spl9_126
    | ~ spl9_136 ),
    inference(avatar_split_clause,[],[f1972,f895,f869,f2067])).

fof(f895,plain,
    ( spl9_136
  <=> ! [X0] : r1_tarski(k9_relat_1(sK2,X0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_136])])).

fof(f1972,plain,
    ( ! [X0] : k9_relat_1(sK2,X0) = k9_relat_1(sK2,k10_relat_1(sK2,k9_relat_1(sK2,X0)))
    | ~ spl9_126
    | ~ spl9_136 ),
    inference(resolution,[],[f870,f896])).

fof(f896,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK2,X0),u1_struct_0(sK1))
    | ~ spl9_136 ),
    inference(avatar_component_clause,[],[f895])).

fof(f2215,plain,
    ( spl9_244
    | ~ spl9_62
    | ~ spl9_150 ),
    inference(avatar_split_clause,[],[f1936,f1041,f540,f2072])).

fof(f540,plain,
    ( spl9_62
  <=> ! [X0] : k9_relat_1(sK2,X0) = k10_relat_1(k2_funct_1(sK2),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_62])])).

fof(f1936,plain,
    ( ! [X2] : k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2),X2) = k9_relat_1(sK2,X2)
    | ~ spl9_62
    | ~ spl9_150 ),
    inference(forward_demodulation,[],[f1931,f541])).

fof(f541,plain,
    ( ! [X0] : k9_relat_1(sK2,X0) = k10_relat_1(k2_funct_1(sK2),X0)
    | ~ spl9_62 ),
    inference(avatar_component_clause,[],[f540])).

fof(f1931,plain,
    ( ! [X2] : k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2),X2) = k10_relat_1(k2_funct_1(sK2),X2)
    | ~ spl9_150 ),
    inference(resolution,[],[f1042,f186])).

fof(f186,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',redefinition_k8_relset_1)).

fof(f2205,plain,
    ( spl9_256
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_22
    | spl9_57 ),
    inference(avatar_split_clause,[],[f2198,f510,f285,f253,f224,f217,f203,f2203])).

fof(f2198,plain,
    ( r1_tarski(sK4(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_22
    | ~ spl9_57 ),
    inference(subsumption_resolution,[],[f2141,f511])).

fof(f2141,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | r1_tarski(sK4(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f2140,f204])).

fof(f2140,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | r1_tarski(sK4(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f2139,f218])).

fof(f2139,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | r1_tarski(sK4(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f2138,f225])).

fof(f2138,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | r1_tarski(sK4(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl9_14
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f1255,f286])).

fof(f1255,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | r1_tarski(sK4(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl9_14 ),
    inference(resolution,[],[f553,f254])).

fof(f553,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | v5_pre_topc(X0,X1,X2)
      | ~ v1_funct_1(X0)
      | ~ l1_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | r1_tarski(sK4(X1,X2,X0),u1_struct_0(X2)) ) ),
    inference(resolution,[],[f146,f163])).

fof(f163,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',t3_subset)).

fof(f2181,plain,
    ( spl9_250
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_22
    | spl9_57 ),
    inference(avatar_split_clause,[],[f2170,f510,f285,f253,f224,f217,f203,f2179])).

fof(f2170,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_22
    | ~ spl9_57 ),
    inference(subsumption_resolution,[],[f2132,f511])).

fof(f2132,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f1796,f286])).

fof(f1796,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f1795,f204])).

fof(f1795,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f1794,f218])).

fof(f1794,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_6
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f1774,f225])).

fof(f1774,plain,
    ( v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_14 ),
    inference(resolution,[],[f254,f147])).

fof(f2174,plain,
    ( spl9_248
    | spl9_17
    | ~ spl9_116 ),
    inference(avatar_split_clause,[],[f2169,f809,f257,f2172])).

fof(f809,plain,
    ( spl9_116
  <=> ! [X4] : k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4) = k9_relat_1(sK2,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_116])])).

fof(f2169,plain,
    ( ! [X4] :
        ( v4_pre_topc(k9_relat_1(sK2,X4),sK1)
        | ~ v4_pre_topc(X4,sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl9_17
    | ~ spl9_116 ),
    inference(subsumption_resolution,[],[f2131,f258])).

fof(f2131,plain,
    ( ! [X4] :
        ( v4_pre_topc(k9_relat_1(sK2,X4),sK1)
        | ~ v4_pre_topc(X4,sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tops_2(sK2,sK0,sK1) )
    | ~ spl9_116 ),
    inference(forward_demodulation,[],[f129,f810])).

fof(f810,plain,
    ( ! [X4] : k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4) = k9_relat_1(sK2,X4)
    | ~ spl9_116 ),
    inference(avatar_component_clause,[],[f809])).

fof(f129,plain,(
    ! [X4] :
      ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4),sK1)
      | ~ v4_pre_topc(X4,sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_tops_2(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f103,plain,
    ( ( ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
          | ~ v4_pre_topc(sK3,sK0) )
        & ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
          | v4_pre_topc(sK3,sK0) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ v2_funct_1(sK2)
      | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
      | ~ v3_tops_2(sK2,sK0,sK1) )
    & ( ( ! [X4] :
            ( ( ( v4_pre_topc(X4,sK0)
                | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4),sK1) )
              & ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4),sK1)
                | ~ v4_pre_topc(X4,sK0) ) )
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
        & v2_funct_1(sK2)
        & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
        & k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0) )
      | v3_tops_2(sK2,sK0,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f98,f102,f101,f100,f99])).

fof(f99,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                        | ~ v4_pre_topc(X3,X0) )
                      & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                        | v4_pre_topc(X3,X0) )
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v2_funct_1(X2)
                  | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
                  | ~ v3_tops_2(X2,X0,X1) )
                & ( ( ! [X4] :
                        ( ( ( v4_pre_topc(X4,X0)
                            | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1) )
                          & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1)
                            | ~ v4_pre_topc(X4,X0) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & v2_funct_1(X2)
                    & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                  | v3_tops_2(X2,X0,X1) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3),X1)
                      | ~ v4_pre_topc(X3,sK0) )
                    & ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X3),X1)
                      | v4_pre_topc(X3,sK0) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
                | ~ v2_funct_1(X2)
                | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
                | k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) != k2_struct_0(sK0)
                | ~ v3_tops_2(X2,sK0,X1) )
              & ( ( ! [X4] :
                      ( ( ( v4_pre_topc(X4,sK0)
                          | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X4),X1) )
                        & ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,X4),X1)
                          | ~ v4_pre_topc(X4,sK0) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(sK0) )
                | v3_tops_2(X2,sK0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f100,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                      | ~ v4_pre_topc(X3,X0) )
                    & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                      | v4_pre_topc(X3,X0) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v2_funct_1(X2)
                | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
                | ~ v3_tops_2(X2,X0,X1) )
              & ( ( ! [X4] :
                      ( ( ( v4_pre_topc(X4,X0)
                          | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1) )
                        & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1)
                          | ~ v4_pre_topc(X4,X0) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                | v3_tops_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( ? [X3] :
                  ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,X3),sK1)
                    | ~ v4_pre_topc(X3,X0) )
                  & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,X3),sK1)
                    | v4_pre_topc(X3,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_funct_1(X2)
              | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2)
              | k1_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) != k2_struct_0(X0)
              | ~ v3_tops_2(X2,X0,sK1) )
            & ( ( ! [X4] :
                    ( ( ( v4_pre_topc(X4,X0)
                        | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,X4),sK1) )
                      & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2,X4),sK1)
                        | ~ v4_pre_topc(X4,X0) ) )
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_funct_1(X2)
                & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2)
                & k1_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(X0) )
              | v3_tops_2(X2,X0,sK1) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                  | ~ v4_pre_topc(X3,X0) )
                & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                  | v4_pre_topc(X3,X0) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_funct_1(X2)
            | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
            | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
            | ~ v3_tops_2(X2,X0,X1) )
          & ( ( ! [X4] :
                  ( ( ( v4_pre_topc(X4,X0)
                      | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1) )
                    & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1)
                      | ~ v4_pre_topc(X4,X0) ) )
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
            | v3_tops_2(X2,X0,X1) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ( ? [X3] :
              ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,X3),X1)
                | ~ v4_pre_topc(X3,X0) )
              & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,X3),X1)
                | v4_pre_topc(X3,X0) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_funct_1(sK2)
          | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
          | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) != k2_struct_0(X0)
          | ~ v3_tops_2(sK2,X0,X1) )
        & ( ( ! [X4] :
                ( ( ( v4_pre_topc(X4,X0)
                    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,X4),X1) )
                  & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,X4),X1)
                    | ~ v4_pre_topc(X4,X0) ) )
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            & v2_funct_1(sK2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
            & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X0) )
          | v3_tops_2(sK2,X0,X1) )
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
            | ~ v4_pre_topc(X3,X0) )
          & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
            | v4_pre_topc(X3,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3),X1)
          | ~ v4_pre_topc(sK3,X0) )
        & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3),X1)
          | v4_pre_topc(sK3,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f98,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                      | ~ v4_pre_topc(X3,X0) )
                    & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                      | v4_pre_topc(X3,X0) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v2_funct_1(X2)
                | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
                | ~ v3_tops_2(X2,X0,X1) )
              & ( ( ! [X4] :
                      ( ( ( v4_pre_topc(X4,X0)
                          | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1) )
                        & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X1)
                          | ~ v4_pre_topc(X4,X0) ) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                | v3_tops_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0) ) ),
    inference(rectify,[],[f97])).

fof(f97,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                      | ~ v4_pre_topc(X3,X0) )
                    & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                      | v4_pre_topc(X3,X0) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v2_funct_1(X2)
                | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
                | ~ v3_tops_2(X2,X0,X1) )
              & ( ( ! [X3] :
                      ( ( ( v4_pre_topc(X3,X0)
                          | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) )
                        & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                          | ~ v4_pre_topc(X3,X0) ) )
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                | v3_tops_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f96])).

fof(f96,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                      | ~ v4_pre_topc(X3,X0) )
                    & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                      | v4_pre_topc(X3,X0) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ v2_funct_1(X2)
                | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
                | ~ v3_tops_2(X2,X0,X1) )
              & ( ( ! [X3] :
                      ( ( ( v4_pre_topc(X3,X0)
                          | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) )
                        & ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                          | ~ v4_pre_topc(X3,X0) ) )
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                | v3_tops_2(X2,X0,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <~> ( ! [X3] :
                      ( ( v4_pre_topc(X3,X0)
                      <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) )
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <~> ( ! [X3] :
                      ( ( v4_pre_topc(X3,X0)
                      <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) )
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( v3_tops_2(X2,X0,X1)
                <=> ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( v4_pre_topc(X3,X0)
                        <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) ) )
                    & v2_funct_1(X2)
                    & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_tops_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( v4_pre_topc(X3,X0)
                      <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) ) )
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',t72_tops_2)).

fof(f2159,plain,
    ( spl9_246
    | spl9_17
    | ~ spl9_116 ),
    inference(avatar_split_clause,[],[f2155,f809,f257,f2157])).

fof(f2155,plain,
    ( ! [X4] :
        ( ~ v4_pre_topc(k9_relat_1(sK2,X4),sK1)
        | v4_pre_topc(X4,sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl9_17
    | ~ spl9_116 ),
    inference(subsumption_resolution,[],[f2130,f258])).

fof(f2130,plain,
    ( ! [X4] :
        ( ~ v4_pre_topc(k9_relat_1(sK2,X4),sK1)
        | v4_pre_topc(X4,sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_tops_2(sK2,sK0,sK1) )
    | ~ spl9_116 ),
    inference(forward_demodulation,[],[f130,f810])).

fof(f130,plain,(
    ! [X4] :
      ( v4_pre_topc(X4,sK0)
      | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4),sK1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_tops_2(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f2077,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK3)) != sK3
    | v4_pre_topc(sK3,sK0)
    | ~ v4_pre_topc(k10_relat_1(sK2,k9_relat_1(sK2,sK3)),sK0) ),
    introduced(theory_axiom,[])).

fof(f2076,plain,
    ( ~ spl9_62
    | spl9_121
    | ~ spl9_150
    | ~ spl9_184 ),
    inference(avatar_contradiction_clause,[],[f2075])).

fof(f2075,plain,
    ( $false
    | ~ spl9_62
    | ~ spl9_121
    | ~ spl9_150
    | ~ spl9_184 ),
    inference(subsumption_resolution,[],[f2070,f824])).

fof(f824,plain,
    ( ~ v4_pre_topc(k9_relat_1(sK2,sK3),sK1)
    | ~ spl9_121 ),
    inference(avatar_component_clause,[],[f823])).

fof(f823,plain,
    ( spl9_121
  <=> ~ v4_pre_topc(k9_relat_1(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_121])])).

fof(f2070,plain,
    ( v4_pre_topc(k9_relat_1(sK2,sK3),sK1)
    | ~ spl9_62
    | ~ spl9_150
    | ~ spl9_184 ),
    inference(backward_demodulation,[],[f1055,f1378])).

fof(f1378,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2),sK3),sK1)
    | ~ spl9_184 ),
    inference(avatar_component_clause,[],[f1377])).

fof(f1377,plain,
    ( spl9_184
  <=> v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2),sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_184])])).

fof(f1055,plain,
    ( ! [X2] : k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2),X2) = k9_relat_1(sK2,X2)
    | ~ spl9_62
    | ~ spl9_150 ),
    inference(forward_demodulation,[],[f1051,f541])).

fof(f1051,plain,
    ( ! [X2] : k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2),X2) = k10_relat_1(k2_funct_1(sK2),X2)
    | ~ spl9_150 ),
    inference(resolution,[],[f1042,f186])).

fof(f1991,plain,
    ( spl9_238
    | ~ spl9_84
    | ~ spl9_210 ),
    inference(avatar_split_clause,[],[f1604,f1558,f670,f1989])).

fof(f1989,plain,
    ( spl9_238
  <=> k10_relat_1(sK2,k9_relat_1(sK2,sK3)) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_238])])).

fof(f670,plain,
    ( spl9_84
  <=> r1_tarski(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_84])])).

fof(f1604,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,sK3)) = sK3
    | ~ spl9_84
    | ~ spl9_210 ),
    inference(resolution,[],[f1559,f671])).

fof(f671,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl9_84 ),
    inference(avatar_component_clause,[],[f670])).

fof(f1560,plain,
    ( spl9_210
    | ~ spl9_28
    | ~ spl9_50
    | ~ spl9_94 ),
    inference(avatar_split_clause,[],[f1226,f721,f435,f320,f1558])).

fof(f320,plain,
    ( spl9_28
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f435,plain,
    ( spl9_50
  <=> ! [X0] : r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_50])])).

fof(f721,plain,
    ( spl9_94
  <=> u1_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_94])])).

fof(f1226,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 )
    | ~ spl9_28
    | ~ spl9_50
    | ~ spl9_94 ),
    inference(forward_demodulation,[],[f1225,f722])).

fof(f722,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl9_94 ),
    inference(avatar_component_clause,[],[f721])).

fof(f1225,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_relat_1(sK2))
        | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 )
    | ~ spl9_28
    | ~ spl9_50 ),
    inference(subsumption_resolution,[],[f1221,f321])).

fof(f321,plain,
    ( v1_relat_1(sK2)
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f320])).

fof(f1221,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | ~ r1_tarski(X0,k1_relat_1(sK2))
        | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 )
    | ~ spl9_50 ),
    inference(resolution,[],[f349,f436])).

fof(f436,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)
    | ~ spl9_50 ),
    inference(avatar_component_clause,[],[f435])).

fof(f349,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ),
    inference(resolution,[],[f153,f162])).

fof(f162,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',d10_xboole_0)).

fof(f153,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',t146_funct_1)).

fof(f1401,plain,
    ( spl9_186
    | ~ spl9_0
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_22
    | ~ spl9_56
    | ~ spl9_114
    | ~ spl9_168 ),
    inference(avatar_split_clause,[],[f1394,f1259,f802,f513,f285,f253,f224,f203,f1399])).

fof(f1399,plain,
    ( spl9_186
  <=> v4_pre_topc(k10_relat_1(sK2,k9_relat_1(sK2,sK3)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_186])])).

fof(f1259,plain,
    ( spl9_168
  <=> ! [X1,X0] :
        ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X1,k9_relat_1(sK2,sK3)),X0)
        | ~ v5_pre_topc(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_168])])).

fof(f1394,plain,
    ( v4_pre_topc(k10_relat_1(sK2,k9_relat_1(sK2,sK3)),sK0)
    | ~ spl9_0
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_22
    | ~ spl9_56
    | ~ spl9_114
    | ~ spl9_168 ),
    inference(forward_demodulation,[],[f1393,f803])).

fof(f1393,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k9_relat_1(sK2,sK3)),sK0)
    | ~ spl9_0
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_22
    | ~ spl9_56
    | ~ spl9_168 ),
    inference(subsumption_resolution,[],[f1392,f204])).

fof(f1392,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k9_relat_1(sK2,sK3)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_22
    | ~ spl9_56
    | ~ spl9_168 ),
    inference(subsumption_resolution,[],[f1391,f225])).

fof(f1391,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k9_relat_1(sK2,sK3)),sK0)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_14
    | ~ spl9_22
    | ~ spl9_56
    | ~ spl9_168 ),
    inference(subsumption_resolution,[],[f1390,f286])).

fof(f1390,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k9_relat_1(sK2,sK3)),sK0)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_14
    | ~ spl9_56
    | ~ spl9_168 ),
    inference(subsumption_resolution,[],[f1389,f514])).

fof(f1389,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k9_relat_1(sK2,sK3)),sK0)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_14
    | ~ spl9_168 ),
    inference(resolution,[],[f1260,f254])).

fof(f1260,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v5_pre_topc(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X1,k9_relat_1(sK2,sK3)),X0)
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl9_168 ),
    inference(avatar_component_clause,[],[f1259])).

fof(f1379,plain,
    ( spl9_184
    | ~ spl9_4
    | ~ spl9_100
    | ~ spl9_102
    | ~ spl9_122
    | ~ spl9_150
    | ~ spl9_166 ),
    inference(avatar_split_clause,[],[f1282,f1241,f1041,f834,f760,f744,f217,f1377])).

fof(f1241,plain,
    ( spl9_166
  <=> ! [X1,X0] :
        ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(sK0),X1,sK3),X0)
        | ~ v5_pre_topc(X1,X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_166])])).

fof(f1282,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2),sK3),sK1)
    | ~ spl9_4
    | ~ spl9_100
    | ~ spl9_102
    | ~ spl9_122
    | ~ spl9_150
    | ~ spl9_166 ),
    inference(subsumption_resolution,[],[f1281,f218])).

fof(f1281,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2),sK3),sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl9_100
    | ~ spl9_102
    | ~ spl9_122
    | ~ spl9_150
    | ~ spl9_166 ),
    inference(subsumption_resolution,[],[f1280,f745])).

fof(f1280,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2),sK3),sK1)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ l1_pre_topc(sK1)
    | ~ spl9_102
    | ~ spl9_122
    | ~ spl9_150
    | ~ spl9_166 ),
    inference(subsumption_resolution,[],[f1279,f1042])).

fof(f1279,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2),sK3),sK1)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ l1_pre_topc(sK1)
    | ~ spl9_102
    | ~ spl9_122
    | ~ spl9_166 ),
    inference(subsumption_resolution,[],[f1278,f761])).

fof(f1278,plain,
    ( ~ v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2),sK3),sK1)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ l1_pre_topc(sK1)
    | ~ spl9_122
    | ~ spl9_166 ),
    inference(resolution,[],[f1242,f835])).

fof(f1242,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v5_pre_topc(X1,X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(sK0),X1,sK3),X0)
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl9_166 ),
    inference(avatar_component_clause,[],[f1241])).

fof(f1294,plain,
    ( spl9_174
    | ~ spl9_6
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f627,f266,f224,f1292])).

fof(f266,plain,
    ( spl9_18
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f627,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2),X1,X0)
        | ~ v5_pre_topc(sK2,X0,X1)
        | v3_tops_2(sK2,X0,X1)
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
        | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) != k2_struct_0(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl9_6
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f626,f225])).

fof(f626,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2),X1,X0)
        | ~ v5_pre_topc(sK2,X0,X1)
        | v3_tops_2(sK2,X0,X1)
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
        | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) != k2_struct_0(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v1_funct_1(sK2)
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl9_18 ),
    inference(resolution,[],[f144,f267])).

fof(f267,plain,
    ( v2_funct_1(sK2)
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f266])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ v5_pre_topc(X2,X0,X1)
      | v3_tops_2(X2,X0,X1)
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f105,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  | ~ v5_pre_topc(X2,X0,X1)
                  | ~ v2_funct_1(X2)
                  | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) )
                & ( ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                    & v5_pre_topc(X2,X0,X1)
                    & v2_funct_1(X2)
                    & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f104])).

fof(f104,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tops_2(X2,X0,X1)
                  | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  | ~ v5_pre_topc(X2,X0,X1)
                  | ~ v2_funct_1(X2)
                  | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) )
                & ( ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                    & v5_pre_topc(X2,X0,X1)
                    & v2_funct_1(X2)
                    & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) )
                  | ~ v3_tops_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',d5_tops_2)).

fof(f1261,plain,
    ( spl9_168
    | ~ spl9_4
    | ~ spl9_120
    | ~ spl9_134 ),
    inference(avatar_split_clause,[],[f1253,f891,f820,f217,f1259])).

fof(f820,plain,
    ( spl9_120
  <=> v4_pre_topc(k9_relat_1(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_120])])).

fof(f891,plain,
    ( spl9_134
  <=> ! [X4] : m1_subset_1(k9_relat_1(sK2,X4),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_134])])).

fof(f1253,plain,
    ( ! [X0,X1] :
        ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X1,k9_relat_1(sK2,sK3)),X0)
        | ~ v5_pre_topc(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl9_4
    | ~ spl9_120
    | ~ spl9_134 ),
    inference(subsumption_resolution,[],[f1252,f218])).

fof(f1252,plain,
    ( ! [X0,X1] :
        ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X1,k9_relat_1(sK2,sK3)),X0)
        | ~ v5_pre_topc(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(X0) )
    | ~ spl9_120
    | ~ spl9_134 ),
    inference(subsumption_resolution,[],[f1251,f892])).

fof(f892,plain,
    ( ! [X4] : m1_subset_1(k9_relat_1(sK2,X4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl9_134 ),
    inference(avatar_component_clause,[],[f891])).

fof(f1251,plain,
    ( ! [X0,X1] :
        ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X1,k9_relat_1(sK2,sK3)),X0)
        | ~ m1_subset_1(k9_relat_1(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK1)))
        | ~ v5_pre_topc(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK1))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(sK1)
        | ~ l1_pre_topc(X0) )
    | ~ spl9_120 ),
    inference(resolution,[],[f821,f145])).

fof(f145,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v4_pre_topc(X4,X1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f109])).

fof(f821,plain,
    ( v4_pre_topc(k9_relat_1(sK2,sK3),sK1)
    | ~ spl9_120 ),
    inference(avatar_component_clause,[],[f820])).

fof(f1250,plain,
    ( spl9_120
    | ~ spl9_88
    | ~ spl9_116 ),
    inference(avatar_split_clause,[],[f1247,f809,f683,f820])).

fof(f683,plain,
    ( spl9_88
  <=> v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_88])])).

fof(f1247,plain,
    ( v4_pre_topc(k9_relat_1(sK2,sK3),sK1)
    | ~ spl9_88
    | ~ spl9_116 ),
    inference(forward_demodulation,[],[f684,f810])).

fof(f684,plain,
    ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
    | ~ spl9_88 ),
    inference(avatar_component_clause,[],[f683])).

fof(f1243,plain,
    ( spl9_166
    | ~ spl9_0
    | ~ spl9_64
    | ~ spl9_86 ),
    inference(avatar_split_clause,[],[f688,f677,f547,f203,f1241])).

fof(f547,plain,
    ( spl9_64
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_64])])).

fof(f677,plain,
    ( spl9_86
  <=> v4_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_86])])).

fof(f688,plain,
    ( ! [X0,X1] :
        ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(sK0),X1,sK3),X0)
        | ~ v5_pre_topc(X1,X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0) )
    | ~ spl9_0
    | ~ spl9_64
    | ~ spl9_86 ),
    inference(subsumption_resolution,[],[f687,f204])).

fof(f687,plain,
    ( ! [X0,X1] :
        ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(sK0),X1,sK3),X0)
        | ~ v5_pre_topc(X1,X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(sK0)
        | ~ l1_pre_topc(X0) )
    | ~ spl9_64
    | ~ spl9_86 ),
    inference(subsumption_resolution,[],[f686,f548])).

fof(f548,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_64 ),
    inference(avatar_component_clause,[],[f547])).

fof(f686,plain,
    ( ! [X0,X1] :
        ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(sK0),X1,sK3),X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v5_pre_topc(X1,X0,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK0))))
        | ~ v1_funct_2(X1,u1_struct_0(X0),u1_struct_0(sK0))
        | ~ v1_funct_1(X1)
        | ~ l1_pre_topc(sK0)
        | ~ l1_pre_topc(X0) )
    | ~ spl9_86 ),
    inference(resolution,[],[f678,f145])).

fof(f678,plain,
    ( v4_pre_topc(sK3,sK0)
    | ~ spl9_86 ),
    inference(avatar_component_clause,[],[f677])).

fof(f1043,plain,
    ( spl9_150
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_22
    | ~ spl9_98 ),
    inference(avatar_split_clause,[],[f1036,f737,f285,f253,f224,f1041])).

fof(f1036,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_22
    | ~ spl9_98 ),
    inference(forward_demodulation,[],[f472,f738])).

fof(f472,plain,
    ( m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f471,f225])).

fof(f471,plain,
    ( m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK2)
    | ~ spl9_14
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f470,f286])).

fof(f470,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK2)
    | ~ spl9_14 ),
    inference(resolution,[],[f180,f254])).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f85])).

fof(f85,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',dt_k2_tops_2)).

fof(f897,plain,
    ( spl9_136
    | ~ spl9_116
    | ~ spl9_124 ),
    inference(avatar_split_clause,[],[f887,f863,f809,f895])).

fof(f863,plain,
    ( spl9_124
  <=> ! [X0] : r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_124])])).

fof(f887,plain,
    ( ! [X0] : r1_tarski(k9_relat_1(sK2,X0),u1_struct_0(sK1))
    | ~ spl9_116
    | ~ spl9_124 ),
    inference(backward_demodulation,[],[f810,f864])).

fof(f864,plain,
    ( ! [X0] : r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),u1_struct_0(sK1))
    | ~ spl9_124 ),
    inference(avatar_component_clause,[],[f863])).

fof(f893,plain,
    ( spl9_134
    | ~ spl9_108
    | ~ spl9_116 ),
    inference(avatar_split_clause,[],[f888,f809,f776,f891])).

fof(f776,plain,
    ( spl9_108
  <=> ! [X4] : m1_subset_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_108])])).

fof(f888,plain,
    ( ! [X4] : m1_subset_1(k9_relat_1(sK2,X4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl9_108
    | ~ spl9_116 ),
    inference(backward_demodulation,[],[f810,f777])).

fof(f777,plain,
    ( ! [X4] : m1_subset_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl9_108 ),
    inference(avatar_component_clause,[],[f776])).

fof(f886,plain,
    ( spl9_132
    | ~ spl9_130 ),
    inference(avatar_split_clause,[],[f882,f879,f884])).

fof(f882,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK2,X0),u1_struct_0(sK0))
    | ~ spl9_130 ),
    inference(resolution,[],[f880,f163])).

fof(f881,plain,
    ( spl9_130
    | ~ spl9_110
    | ~ spl9_114 ),
    inference(avatar_split_clause,[],[f876,f802,f784,f879])).

fof(f784,plain,
    ( spl9_110
  <=> ! [X4] : m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_110])])).

fof(f876,plain,
    ( ! [X4] : m1_subset_1(k10_relat_1(sK2,X4),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_110
    | ~ spl9_114 ),
    inference(backward_demodulation,[],[f803,f785])).

fof(f785,plain,
    ( ! [X4] : m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_110 ),
    inference(avatar_component_clause,[],[f784])).

fof(f871,plain,
    ( spl9_126
    | ~ spl9_6
    | ~ spl9_28
    | ~ spl9_96 ),
    inference(avatar_split_clause,[],[f790,f729,f320,f224,f869])).

fof(f729,plain,
    ( spl9_96
  <=> u1_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_96])])).

fof(f790,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK1))
        | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 )
    | ~ spl9_6
    | ~ spl9_28
    | ~ spl9_96 ),
    inference(forward_demodulation,[],[f410,f730])).

fof(f730,plain,
    ( u1_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl9_96 ),
    inference(avatar_component_clause,[],[f729])).

fof(f410,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_relat_1(sK2))
        | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0 )
    | ~ spl9_6
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f408,f321])).

fof(f408,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k2_relat_1(sK2))
        | k9_relat_1(sK2,k10_relat_1(sK2,X0)) = X0
        | ~ v1_relat_1(sK2) )
    | ~ spl9_6 ),
    inference(resolution,[],[f159,f225])).

fof(f159,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',t147_funct_1)).

fof(f865,plain,
    ( spl9_124
    | ~ spl9_108 ),
    inference(avatar_split_clause,[],[f861,f776,f863])).

fof(f861,plain,
    ( ! [X0] : r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),u1_struct_0(sK1))
    | ~ spl9_108 ),
    inference(resolution,[],[f777,f163])).

fof(f836,plain,
    ( spl9_122
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_22
    | ~ spl9_98 ),
    inference(avatar_split_clause,[],[f829,f737,f285,f253,f224,f834])).

fof(f829,plain,
    ( v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_22
    | ~ spl9_98 ),
    inference(forward_demodulation,[],[f463,f738])).

fof(f463,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f462,f225])).

fof(f462,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ spl9_14
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f461,f286])).

fof(f461,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ spl9_14 ),
    inference(resolution,[],[f179,f254])).

fof(f179,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f825,plain,
    ( ~ spl9_121
    | ~ spl9_22
    | spl9_89 ),
    inference(avatar_split_clause,[],[f807,f680,f285,f823])).

fof(f680,plain,
    ( spl9_89
  <=> ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_89])])).

fof(f807,plain,
    ( ~ v4_pre_topc(k9_relat_1(sK2,sK3),sK1)
    | ~ spl9_22
    | ~ spl9_89 ),
    inference(backward_demodulation,[],[f424,f681])).

fof(f681,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
    | ~ spl9_89 ),
    inference(avatar_component_clause,[],[f680])).

fof(f424,plain,
    ( ! [X4] : k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4) = k9_relat_1(sK2,X4)
    | ~ spl9_22 ),
    inference(resolution,[],[f187,f286])).

fof(f187,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f95,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',redefinition_k7_relset_1)).

fof(f811,plain,
    ( spl9_116
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f424,f285,f809])).

fof(f804,plain,
    ( spl9_114
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f414,f285,f802])).

fof(f414,plain,
    ( ! [X4] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4) = k10_relat_1(sK2,X4)
    | ~ spl9_22 ),
    inference(resolution,[],[f186,f286])).

fof(f786,plain,
    ( spl9_110
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f402,f285,f784])).

fof(f402,plain,
    ( ! [X4] : m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_22 ),
    inference(resolution,[],[f185,f286])).

fof(f185,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',dt_k8_relset_1)).

fof(f778,plain,
    ( spl9_108
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f398,f285,f776])).

fof(f398,plain,
    ( ! [X4] : m1_subset_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl9_22 ),
    inference(resolution,[],[f184,f286])).

fof(f184,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',dt_k7_relset_1)).

fof(f762,plain,
    ( spl9_102
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_22
    | ~ spl9_98 ),
    inference(avatar_split_clause,[],[f755,f737,f285,f260,f253,f224,f217,f203,f760])).

fof(f260,plain,
    ( spl9_16
  <=> v3_tops_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f755,plain,
    ( v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_22
    | ~ spl9_98 ),
    inference(subsumption_resolution,[],[f754,f204])).

fof(f754,plain,
    ( v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_22
    | ~ spl9_98 ),
    inference(subsumption_resolution,[],[f753,f218])).

fof(f753,plain,
    ( v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_22
    | ~ spl9_98 ),
    inference(subsumption_resolution,[],[f752,f225])).

fof(f752,plain,
    ( v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_22
    | ~ spl9_98 ),
    inference(subsumption_resolution,[],[f751,f254])).

fof(f751,plain,
    ( v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_16
    | ~ spl9_22
    | ~ spl9_98 ),
    inference(subsumption_resolution,[],[f750,f286])).

fof(f750,plain,
    ( v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_16
    | ~ spl9_98 ),
    inference(subsumption_resolution,[],[f749,f261])).

fof(f261,plain,
    ( v3_tops_2(sK2,sK0,sK1)
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f260])).

fof(f749,plain,
    ( v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ v3_tops_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_98 ),
    inference(superposition,[],[f143,f738])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f746,plain,
    ( spl9_100
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_18
    | ~ spl9_22
    | ~ spl9_54
    | ~ spl9_60 ),
    inference(avatar_split_clause,[],[f732,f530,f457,f285,f266,f253,f224,f744])).

fof(f457,plain,
    ( spl9_54
  <=> v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_54])])).

fof(f732,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_18
    | ~ spl9_22
    | ~ spl9_54
    | ~ spl9_60 ),
    inference(backward_demodulation,[],[f715,f458])).

fof(f458,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl9_54 ),
    inference(avatar_component_clause,[],[f457])).

fof(f715,plain,
    ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_18
    | ~ spl9_22
    | ~ spl9_60 ),
    inference(subsumption_resolution,[],[f714,f225])).

fof(f714,plain,
    ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl9_14
    | ~ spl9_18
    | ~ spl9_22
    | ~ spl9_60 ),
    inference(subsumption_resolution,[],[f713,f254])).

fof(f713,plain,
    ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl9_18
    | ~ spl9_22
    | ~ spl9_60 ),
    inference(subsumption_resolution,[],[f712,f286])).

fof(f712,plain,
    ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl9_18
    | ~ spl9_60 ),
    inference(subsumption_resolution,[],[f711,f267])).

fof(f711,plain,
    ( ~ v2_funct_1(sK2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl9_60 ),
    inference(trivial_inequality_removal,[],[f710])).

fof(f710,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl9_60 ),
    inference(superposition,[],[f181,f531])).

fof(f181,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f87])).

fof(f87,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',d4_tops_2)).

fof(f739,plain,
    ( spl9_98
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_18
    | ~ spl9_22
    | ~ spl9_60 ),
    inference(avatar_split_clause,[],[f715,f530,f285,f266,f253,f224,f737])).

fof(f731,plain,
    ( spl9_96
    | ~ spl9_60
    | ~ spl9_82 ),
    inference(avatar_split_clause,[],[f724,f657,f530,f729])).

fof(f657,plain,
    ( spl9_82
  <=> k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_82])])).

fof(f724,plain,
    ( u1_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl9_60
    | ~ spl9_82 ),
    inference(forward_demodulation,[],[f658,f531])).

fof(f658,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl9_82 ),
    inference(avatar_component_clause,[],[f657])).

fof(f723,plain,
    ( spl9_94
    | ~ spl9_32
    | ~ spl9_80 ),
    inference(avatar_split_clause,[],[f716,f645,f342,f721])).

fof(f645,plain,
    ( spl9_80
  <=> k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_80])])).

fof(f716,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl9_32
    | ~ spl9_80 ),
    inference(forward_demodulation,[],[f646,f343])).

fof(f646,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2)
    | ~ spl9_80 ),
    inference(avatar_component_clause,[],[f645])).

fof(f709,plain,
    ( spl9_60
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_22
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f571,f306,f285,f260,f253,f224,f217,f203,f530])).

fof(f571,plain,
    ( u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_22
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f570,f307])).

fof(f570,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f569,f204])).

fof(f569,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f568,f218])).

fof(f568,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f567,f225])).

fof(f567,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f566,f286])).

fof(f566,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_14
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f565,f261])).

fof(f565,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_14 ),
    inference(resolution,[],[f140,f254])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f706,plain,
    ( spl9_32
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_22
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f564,f296,f285,f260,f253,f224,f217,f203,f342])).

fof(f564,plain,
    ( u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_22
    | ~ spl9_24 ),
    inference(forward_demodulation,[],[f563,f297])).

fof(f563,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0)
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f562,f204])).

fof(f562,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f561,f218])).

fof(f561,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f560,f225])).

fof(f560,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f559,f286])).

fof(f559,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_14
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f558,f261])).

fof(f558,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_14 ),
    inference(resolution,[],[f139,f254])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f691,plain,
    ( ~ spl9_89
    | ~ spl9_61
    | ~ spl9_33
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_24
    | ~ spl9_26
    | ~ spl9_86 ),
    inference(avatar_split_clause,[],[f689,f677,f306,f296,f266,f260,f339,f527,f680])).

fof(f527,plain,
    ( spl9_61
  <=> u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_61])])).

fof(f339,plain,
    ( spl9_33
  <=> u1_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).

fof(f689,plain,
    ( u1_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_24
    | ~ spl9_26
    | ~ spl9_86 ),
    inference(subsumption_resolution,[],[f616,f678])).

fof(f616,plain,
    ( u1_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
    | ~ v4_pre_topc(sK3,sK0)
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_24
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f615,f297])).

fof(f615,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
    | ~ v4_pre_topc(sK3,sK0)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f614,f307])).

fof(f614,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
    | ~ v4_pre_topc(sK3,sK0)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ spl9_16
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f613,f261])).

fof(f613,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
    | ~ v4_pre_topc(sK3,sK0)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ v3_tops_2(sK2,sK0,sK1)
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f133,f267])).

fof(f133,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
    | ~ v4_pre_topc(sK3,sK0)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f103])).

fof(f685,plain,
    ( spl9_86
    | spl9_88
    | ~ spl9_61
    | ~ spl9_33
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_24
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f599,f306,f296,f266,f260,f339,f527,f683,f677])).

fof(f599,plain,
    ( u1_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
    | v4_pre_topc(sK3,sK0)
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_24
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f598,f297])).

fof(f598,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
    | v4_pre_topc(sK3,sK0)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f597,f307])).

fof(f597,plain,
    ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
    | v4_pre_topc(sK3,sK0)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ spl9_16
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f596,f261])).

fof(f596,plain,
    ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
    | v4_pre_topc(sK3,sK0)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ v3_tops_2(sK2,sK0,sK1)
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f132,f267])).

fof(f132,plain,
    ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3),sK1)
    | v4_pre_topc(sK3,sK0)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f103])).

fof(f672,plain,
    ( spl9_84
    | ~ spl9_64 ),
    inference(avatar_split_clause,[],[f665,f547,f670])).

fof(f665,plain,
    ( r1_tarski(sK3,u1_struct_0(sK0))
    | ~ spl9_64 ),
    inference(resolution,[],[f548,f163])).

fof(f659,plain,
    ( spl9_82
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f367,f285,f657])).

fof(f367,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl9_22 ),
    inference(resolution,[],[f169,f286])).

fof(f169,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',redefinition_k2_relset_1)).

fof(f647,plain,
    ( spl9_80
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f363,f285,f645])).

fof(f363,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2)
    | ~ spl9_22 ),
    inference(resolution,[],[f168,f286])).

fof(f168,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',redefinition_k1_relset_1)).

fof(f549,plain,
    ( spl9_64
    | ~ spl9_61
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_24
    | ~ spl9_26
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f538,f342,f306,f296,f266,f260,f527,f547])).

fof(f538,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_24
    | ~ spl9_26
    | ~ spl9_32 ),
    inference(subsumption_resolution,[],[f537,f343])).

fof(f537,plain,
    ( u1_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_24
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f536,f297])).

fof(f536,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ spl9_16
    | ~ spl9_18
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f535,f307])).

fof(f535,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ spl9_16
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f534,f261])).

fof(f534,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ v3_tops_2(sK2,sK0,sK1)
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f131,f267])).

fof(f131,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f103])).

fof(f542,plain,
    ( spl9_62
    | ~ spl9_6
    | ~ spl9_18
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f496,f320,f266,f224,f540])).

fof(f496,plain,
    ( ! [X0] : k9_relat_1(sK2,X0) = k10_relat_1(k2_funct_1(sK2),X0)
    | ~ spl9_6
    | ~ spl9_18
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f495,f321])).

fof(f495,plain,
    ( ! [X0] :
        ( k9_relat_1(sK2,X0) = k10_relat_1(k2_funct_1(sK2),X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl9_6
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f493,f225])).

fof(f493,plain,
    ( ! [X0] :
        ( k9_relat_1(sK2,X0) = k10_relat_1(k2_funct_1(sK2),X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl9_18 ),
    inference(resolution,[],[f267,f158])).

fof(f158,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',t154_funct_1)).

fof(f532,plain,
    ( spl9_16
    | spl9_60
    | ~ spl9_26 ),
    inference(avatar_split_clause,[],[f337,f306,f530,f260])).

fof(f337,plain,
    ( u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v3_tops_2(sK2,sK0,sK1)
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f127,f307])).

fof(f127,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f103])).

fof(f515,plain,
    ( spl9_56
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f508,f285,f260,f253,f224,f217,f203,f513])).

fof(f508,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f507,f204])).

fof(f507,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f506,f218])).

fof(f506,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f505,f225])).

fof(f505,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f504,f286])).

fof(f504,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_14
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f503,f261])).

fof(f503,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_14 ),
    inference(resolution,[],[f142,f254])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f492,plain,
    ( spl9_18
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f491,f285,f260,f253,f224,f217,f203,f266])).

fof(f491,plain,
    ( v2_funct_1(sK2)
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f490,f204])).

fof(f490,plain,
    ( v2_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f489,f218])).

fof(f489,plain,
    ( v2_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f483,f225])).

fof(f483,plain,
    ( v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_14
    | ~ spl9_16
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f482,f286])).

fof(f482,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_14
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f480,f261])).

fof(f480,plain,
    ( ~ v3_tops_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl9_14 ),
    inference(resolution,[],[f141,f254])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v3_tops_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v2_funct_1(X2)
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f459,plain,
    ( spl9_54
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f441,f285,f253,f224,f457])).

fof(f441,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl9_6
    | ~ spl9_14
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f440,f225])).

fof(f440,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl9_14
    | ~ spl9_22 ),
    inference(subsumption_resolution,[],[f439,f286])).

fof(f439,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl9_14 ),
    inference(resolution,[],[f178,f254])).

fof(f178,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f437,plain,
    ( spl9_50
    | ~ spl9_6
    | ~ spl9_18
    | ~ spl9_28 ),
    inference(avatar_split_clause,[],[f354,f320,f266,f224,f435])).

fof(f354,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)
    | ~ spl9_6
    | ~ spl9_18
    | ~ spl9_28 ),
    inference(subsumption_resolution,[],[f353,f321])).

fof(f353,plain,
    ( ! [X0] :
        ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)
        | ~ v1_relat_1(sK2) )
    | ~ spl9_6
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f352,f225])).

fof(f352,plain,
    ( ! [X0] :
        ( r1_tarski(k10_relat_1(sK2,k9_relat_1(sK2,X0)),X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl9_18 ),
    inference(resolution,[],[f157,f267])).

fof(f157,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',t152_funct_1)).

fof(f344,plain,
    ( spl9_16
    | spl9_32
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f335,f296,f342,f260])).

fof(f335,plain,
    ( u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v3_tops_2(sK2,sK0,sK1)
    | ~ spl9_24 ),
    inference(forward_demodulation,[],[f126,f297])).

fof(f126,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f103])).

fof(f322,plain,
    ( spl9_28
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f314,f285,f320])).

fof(f314,plain,
    ( v1_relat_1(sK2)
    | ~ spl9_22 ),
    inference(resolution,[],[f167,f286])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',cc1_relset_1)).

fof(f308,plain,
    ( spl9_26
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f289,f217,f306])).

fof(f289,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl9_4 ),
    inference(resolution,[],[f270,f218])).

fof(f270,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(resolution,[],[f135,f138])).

fof(f138,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',dt_l1_pre_topc)).

fof(f135,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t72_tops_2.p',d3_struct_0)).

fof(f298,plain,
    ( spl9_24
    | ~ spl9_0 ),
    inference(avatar_split_clause,[],[f288,f203,f296])).

fof(f288,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl9_0 ),
    inference(resolution,[],[f270,f204])).

fof(f287,plain,(
    spl9_22 ),
    inference(avatar_split_clause,[],[f125,f285])).

fof(f125,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f103])).

fof(f268,plain,
    ( spl9_16
    | spl9_18 ),
    inference(avatar_split_clause,[],[f128,f266,f260])).

fof(f128,plain,
    ( v2_funct_1(sK2)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f103])).

fof(f255,plain,(
    spl9_14 ),
    inference(avatar_split_clause,[],[f124,f253])).

fof(f124,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f103])).

fof(f226,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f123,f224])).

fof(f123,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f103])).

fof(f219,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f122,f217])).

fof(f122,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f103])).

fof(f205,plain,(
    spl9_0 ),
    inference(avatar_split_clause,[],[f120,f203])).

fof(f120,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f103])).
%------------------------------------------------------------------------------
