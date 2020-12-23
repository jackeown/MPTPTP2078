%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:39 EST 2020

% Result     : Theorem 3.84s
% Output     : Refutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :  337 ( 626 expanded)
%              Number of leaves         :   88 ( 302 expanded)
%              Depth                    :   10
%              Number of atoms          : 1014 (1915 expanded)
%              Number of equality atoms :  207 ( 428 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9739,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f101,f106,f115,f117,f121,f125,f129,f133,f138,f142,f146,f150,f154,f158,f162,f166,f170,f174,f199,f225,f229,f233,f244,f250,f314,f321,f325,f331,f353,f357,f384,f394,f422,f457,f475,f512,f582,f595,f644,f653,f674,f685,f704,f710,f768,f851,f966,f1196,f1483,f1488,f1657,f1794,f1926,f1988,f2642,f2721,f4126,f5761,f6970,f7100,f8244,f8714,f9216,f9666,f9735])).

fof(f9735,plain,
    ( ~ spl2_16
    | spl2_44
    | ~ spl2_123
    | ~ spl2_205
    | ~ spl2_275 ),
    inference(avatar_contradiction_clause,[],[f9734])).

fof(f9734,plain,
    ( $false
    | ~ spl2_16
    | spl2_44
    | ~ spl2_123
    | ~ spl2_205
    | ~ spl2_275 ),
    inference(subsumption_resolution,[],[f581,f9733])).

fof(f9733,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_16
    | ~ spl2_123
    | ~ spl2_205
    | ~ spl2_275 ),
    inference(subsumption_resolution,[],[f2723,f9714])).

fof(f9714,plain,
    ( r1_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_205
    | ~ spl2_275 ),
    inference(superposition,[],[f9665,f6969])).

fof(f6969,plain,
    ( sK1 = k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_205 ),
    inference(avatar_component_clause,[],[f6967])).

fof(f6967,plain,
    ( spl2_205
  <=> sK1 = k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_205])])).

fof(f9665,plain,
    ( ! [X12,X11] : r1_xboole_0(k4_xboole_0(X11,X12),X12)
    | ~ spl2_275 ),
    inference(avatar_component_clause,[],[f9664])).

fof(f9664,plain,
    ( spl2_275
  <=> ! [X11,X12] : r1_xboole_0(k4_xboole_0(X11,X12),X12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_275])])).

fof(f2723,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ r1_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_16
    | ~ spl2_123 ),
    inference(superposition,[],[f2720,f161])).

fof(f161,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl2_16
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f2720,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_123 ),
    inference(avatar_component_clause,[],[f2718])).

fof(f2718,plain,
    ( spl2_123
  <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_123])])).

fof(f581,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | spl2_44 ),
    inference(avatar_component_clause,[],[f579])).

fof(f579,plain,
    ( spl2_44
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).

fof(f9666,plain,
    ( spl2_275
    | ~ spl2_8
    | ~ spl2_14
    | ~ spl2_65
    | ~ spl2_72
    | ~ spl2_96 ),
    inference(avatar_split_clause,[],[f1836,f1792,f964,f849,f152,f127,f9664])).

fof(f127,plain,
    ( spl2_8
  <=> ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f152,plain,
    ( spl2_14
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f849,plain,
    ( spl2_65
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_65])])).

fof(f964,plain,
    ( spl2_72
  <=> ! [X3,X2] : k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_72])])).

fof(f1792,plain,
    ( spl2_96
  <=> ! [X9,X8,X10] :
        ( k3_xboole_0(X8,X9) != k3_xboole_0(X8,k4_xboole_0(X9,X10))
        | r1_xboole_0(k3_xboole_0(X8,X9),X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_96])])).

fof(f1836,plain,
    ( ! [X12,X11] : r1_xboole_0(k4_xboole_0(X11,X12),X12)
    | ~ spl2_8
    | ~ spl2_14
    | ~ spl2_65
    | ~ spl2_72
    | ~ spl2_96 ),
    inference(forward_demodulation,[],[f1835,f965])).

fof(f965,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3))
    | ~ spl2_72 ),
    inference(avatar_component_clause,[],[f964])).

fof(f1835,plain,
    ( ! [X12,X11] : r1_xboole_0(k3_xboole_0(X11,k4_xboole_0(X11,X12)),X12)
    | ~ spl2_8
    | ~ spl2_14
    | ~ spl2_65
    | ~ spl2_72
    | ~ spl2_96 ),
    inference(forward_demodulation,[],[f1834,f854])).

fof(f854,plain,
    ( ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)
    | ~ spl2_14
    | ~ spl2_65 ),
    inference(superposition,[],[f850,f153])).

fof(f153,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f152])).

fof(f850,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))
    | ~ spl2_65 ),
    inference(avatar_component_clause,[],[f849])).

fof(f1834,plain,
    ( ! [X12,X11] : r1_xboole_0(k3_xboole_0(k4_xboole_0(X11,X12),X11),X12)
    | ~ spl2_8
    | ~ spl2_14
    | ~ spl2_65
    | ~ spl2_72
    | ~ spl2_96 ),
    inference(trivial_inequality_removal,[],[f1833])).

fof(f1833,plain,
    ( ! [X12,X11] :
        ( k4_xboole_0(X11,X12) != k4_xboole_0(X11,X12)
        | r1_xboole_0(k3_xboole_0(k4_xboole_0(X11,X12),X11),X12) )
    | ~ spl2_8
    | ~ spl2_14
    | ~ spl2_65
    | ~ spl2_72
    | ~ spl2_96 ),
    inference(forward_demodulation,[],[f1832,f965])).

fof(f1832,plain,
    ( ! [X12,X11] :
        ( k4_xboole_0(X11,X12) != k3_xboole_0(X11,k4_xboole_0(X11,X12))
        | r1_xboole_0(k3_xboole_0(k4_xboole_0(X11,X12),X11),X12) )
    | ~ spl2_8
    | ~ spl2_14
    | ~ spl2_65
    | ~ spl2_96 ),
    inference(forward_demodulation,[],[f1813,f854])).

fof(f1813,plain,
    ( ! [X12,X11] :
        ( k4_xboole_0(X11,X12) != k3_xboole_0(k4_xboole_0(X11,X12),X11)
        | r1_xboole_0(k3_xboole_0(k4_xboole_0(X11,X12),X11),X12) )
    | ~ spl2_8
    | ~ spl2_96 ),
    inference(superposition,[],[f1793,f128])).

fof(f128,plain,
    ( ! [X0] : k3_xboole_0(X0,X0) = X0
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f127])).

fof(f1793,plain,
    ( ! [X10,X8,X9] :
        ( k3_xboole_0(X8,X9) != k3_xboole_0(X8,k4_xboole_0(X9,X10))
        | r1_xboole_0(k3_xboole_0(X8,X9),X10) )
    | ~ spl2_96 ),
    inference(avatar_component_clause,[],[f1792])).

fof(f9216,plain,
    ( spl2_213
    | ~ spl2_158
    | ~ spl2_259 ),
    inference(avatar_split_clause,[],[f8990,f8712,f4123,f7097])).

fof(f7097,plain,
    ( spl2_213
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_213])])).

fof(f4123,plain,
    ( spl2_158
  <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_158])])).

fof(f8712,plain,
    ( spl2_259
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_259])])).

fof(f8990,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_158
    | ~ spl2_259 ),
    inference(superposition,[],[f8713,f4125])).

fof(f4125,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_158 ),
    inference(avatar_component_clause,[],[f4123])).

fof(f8713,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl2_259 ),
    inference(avatar_component_clause,[],[f8712])).

fof(f8714,plain,
    ( spl2_259
    | ~ spl2_189
    | ~ spl2_256 ),
    inference(avatar_split_clause,[],[f8251,f8242,f5759,f8712])).

fof(f5759,plain,
    ( spl2_189
  <=> ! [X29,X28,X30] :
        ( k1_xboole_0 != k4_xboole_0(X28,X29)
        | r1_tarski(X28,k2_xboole_0(X29,X30)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_189])])).

fof(f8242,plain,
    ( spl2_256
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_256])])).

fof(f8251,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl2_189
    | ~ spl2_256 ),
    inference(unit_resulting_resolution,[],[f8243,f5760])).

fof(f5760,plain,
    ( ! [X30,X28,X29] :
        ( k1_xboole_0 != k4_xboole_0(X28,X29)
        | r1_tarski(X28,k2_xboole_0(X29,X30)) )
    | ~ spl2_189 ),
    inference(avatar_component_clause,[],[f5759])).

fof(f8243,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl2_256 ),
    inference(avatar_component_clause,[],[f8242])).

fof(f8244,plain,
    ( spl2_256
    | ~ spl2_11
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f204,f172,f140,f8242])).

fof(f140,plain,
    ( spl2_11
  <=> ! [X0] : r1_tarski(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f172,plain,
    ( spl2_19
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f204,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl2_11
    | ~ spl2_19 ),
    inference(unit_resulting_resolution,[],[f141,f173])).

fof(f173,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f172])).

fof(f141,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f140])).

fof(f7100,plain,
    ( ~ spl2_213
    | ~ spl2_13
    | spl2_204 ),
    inference(avatar_split_clause,[],[f6971,f6963,f148,f7097])).

fof(f148,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f6963,plain,
    ( spl2_204
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_204])])).

fof(f6971,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_13
    | spl2_204 ),
    inference(unit_resulting_resolution,[],[f6965,f149])).

fof(f149,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f148])).

fof(f6965,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | spl2_204 ),
    inference(avatar_component_clause,[],[f6963])).

fof(f6970,plain,
    ( ~ spl2_204
    | spl2_205
    | ~ spl2_54
    | ~ spl2_92 ),
    inference(avatar_split_clause,[],[f1679,f1655,f671,f6967,f6963])).

fof(f671,plain,
    ( spl2_54
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).

fof(f1655,plain,
    ( spl2_92
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_92])])).

fof(f1679,plain,
    ( sK1 = k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_54
    | ~ spl2_92 ),
    inference(superposition,[],[f1656,f673])).

fof(f673,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_54 ),
    inference(avatar_component_clause,[],[f671])).

fof(f1656,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_92 ),
    inference(avatar_component_clause,[],[f1655])).

fof(f5761,plain,
    ( spl2_189
    | ~ spl2_18
    | ~ spl2_29
    | ~ spl2_98
    | ~ spl2_99
    | ~ spl2_121 ),
    inference(avatar_split_clause,[],[f2692,f2640,f1986,f1924,f311,f168,f5759])).

fof(f168,plain,
    ( spl2_18
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f311,plain,
    ( spl2_29
  <=> k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f1924,plain,
    ( spl2_98
  <=> ! [X9,X8,X10] :
        ( k4_xboole_0(X8,X9) = k4_xboole_0(X8,k2_xboole_0(X9,X10))
        | ~ r1_xboole_0(k4_xboole_0(X8,X9),X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_98])])).

fof(f1986,plain,
    ( spl2_99
  <=> ! [X9,X8,X10] :
        ( k4_xboole_0(X8,X9) != k4_xboole_0(X8,k2_xboole_0(X9,X10))
        | r1_xboole_0(k4_xboole_0(X8,X9),X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_99])])).

fof(f2640,plain,
    ( spl2_121
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(u1_struct_0(sK0),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_121])])).

fof(f2692,plain,
    ( ! [X30,X28,X29] :
        ( k1_xboole_0 != k4_xboole_0(X28,X29)
        | r1_tarski(X28,k2_xboole_0(X29,X30)) )
    | ~ spl2_18
    | ~ spl2_29
    | ~ spl2_98
    | ~ spl2_99
    | ~ spl2_121 ),
    inference(subsumption_resolution,[],[f1975,f2691])).

fof(f2691,plain,
    ( ! [X6] : r1_xboole_0(k1_xboole_0,X6)
    | ~ spl2_29
    | ~ spl2_99
    | ~ spl2_121 ),
    inference(forward_demodulation,[],[f2690,f313])).

fof(f313,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0))
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f311])).

fof(f2690,plain,
    ( ! [X6] : r1_xboole_0(k4_xboole_0(sK1,u1_struct_0(sK0)),X6)
    | ~ spl2_29
    | ~ spl2_99
    | ~ spl2_121 ),
    inference(trivial_inequality_removal,[],[f2689])).

fof(f2689,plain,
    ( ! [X6] :
        ( k1_xboole_0 != k1_xboole_0
        | r1_xboole_0(k4_xboole_0(sK1,u1_struct_0(sK0)),X6) )
    | ~ spl2_29
    | ~ spl2_99
    | ~ spl2_121 ),
    inference(forward_demodulation,[],[f2660,f313])).

fof(f2660,plain,
    ( ! [X6] :
        ( k1_xboole_0 != k4_xboole_0(sK1,u1_struct_0(sK0))
        | r1_xboole_0(k4_xboole_0(sK1,u1_struct_0(sK0)),X6) )
    | ~ spl2_99
    | ~ spl2_121 ),
    inference(superposition,[],[f1987,f2641])).

fof(f2641,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(u1_struct_0(sK0),X0))
    | ~ spl2_121 ),
    inference(avatar_component_clause,[],[f2640])).

fof(f1987,plain,
    ( ! [X10,X8,X9] :
        ( k4_xboole_0(X8,X9) != k4_xboole_0(X8,k2_xboole_0(X9,X10))
        | r1_xboole_0(k4_xboole_0(X8,X9),X10) )
    | ~ spl2_99 ),
    inference(avatar_component_clause,[],[f1986])).

fof(f1975,plain,
    ( ! [X30,X28,X29] :
        ( k1_xboole_0 != k4_xboole_0(X28,X29)
        | r1_tarski(X28,k2_xboole_0(X29,X30))
        | ~ r1_xboole_0(k1_xboole_0,X30) )
    | ~ spl2_18
    | ~ spl2_98 ),
    inference(inner_rewriting,[],[f1946])).

fof(f1946,plain,
    ( ! [X30,X28,X29] :
        ( k1_xboole_0 != k4_xboole_0(X28,X29)
        | r1_tarski(X28,k2_xboole_0(X29,X30))
        | ~ r1_xboole_0(k4_xboole_0(X28,X29),X30) )
    | ~ spl2_18
    | ~ spl2_98 ),
    inference(superposition,[],[f169,f1925])).

fof(f1925,plain,
    ( ! [X10,X8,X9] :
        ( k4_xboole_0(X8,X9) = k4_xboole_0(X8,k2_xboole_0(X9,X10))
        | ~ r1_xboole_0(k4_xboole_0(X8,X9),X10) )
    | ~ spl2_98 ),
    inference(avatar_component_clause,[],[f1924])).

fof(f169,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) != k1_xboole_0
        | r1_tarski(X0,X1) )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f168])).

fof(f4126,plain,
    ( spl2_158
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_32
    | ~ spl2_34
    | ~ spl2_42 ),
    inference(avatar_split_clause,[],[f533,f509,f351,f329,f103,f98,f4123])).

fof(f98,plain,
    ( spl2_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f103,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f329,plain,
    ( spl2_32
  <=> ! [X1,X0,X2] :
        ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f351,plain,
    ( spl2_34
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f509,plain,
    ( spl2_42
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f533,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_32
    | ~ spl2_34
    | ~ spl2_42 ),
    inference(forward_demodulation,[],[f529,f365])).

fof(f365,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_34 ),
    inference(unit_resulting_resolution,[],[f100,f105,f352])).

fof(f352,plain,
    ( ! [X0,X1] :
        ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f351])).

fof(f105,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f100,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f529,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_32
    | ~ spl2_42 ),
    inference(unit_resulting_resolution,[],[f105,f511,f330])).

fof(f330,plain,
    ( ! [X2,X0,X1] :
        ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f329])).

fof(f511,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_42 ),
    inference(avatar_component_clause,[],[f509])).

fof(f2721,plain,
    ( spl2_123
    | ~ spl2_46
    | ~ spl2_52 ),
    inference(avatar_split_clause,[],[f645,f641,f593,f2718])).

fof(f593,plain,
    ( spl2_46
  <=> ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).

fof(f641,plain,
    ( spl2_52
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).

fof(f645,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_46
    | ~ spl2_52 ),
    inference(superposition,[],[f643,f594])).

fof(f594,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl2_46 ),
    inference(avatar_component_clause,[],[f593])).

fof(f643,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_52 ),
    inference(avatar_component_clause,[],[f641])).

fof(f2642,plain,
    ( spl2_121
    | ~ spl2_21
    | ~ spl2_88 ),
    inference(avatar_split_clause,[],[f1504,f1486,f196,f2640])).

fof(f196,plain,
    ( spl2_21
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f1486,plain,
    ( spl2_88
  <=> ! [X3,X2,X4] :
        ( k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X4))
        | ~ r1_tarski(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_88])])).

fof(f1504,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(u1_struct_0(sK0),X0))
    | ~ spl2_21
    | ~ spl2_88 ),
    inference(unit_resulting_resolution,[],[f198,f1487])).

fof(f1487,plain,
    ( ! [X4,X2,X3] :
        ( k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X4))
        | ~ r1_tarski(X2,X3) )
    | ~ spl2_88 ),
    inference(avatar_component_clause,[],[f1486])).

fof(f198,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f196])).

fof(f1988,plain,
    ( spl2_99
    | ~ spl2_17
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f303,f242,f164,f1986])).

fof(f164,plain,
    ( spl2_17
  <=> ! [X1,X0] :
        ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f242,plain,
    ( spl2_27
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f303,plain,
    ( ! [X10,X8,X9] :
        ( k4_xboole_0(X8,X9) != k4_xboole_0(X8,k2_xboole_0(X9,X10))
        | r1_xboole_0(k4_xboole_0(X8,X9),X10) )
    | ~ spl2_17
    | ~ spl2_27 ),
    inference(superposition,[],[f165,f243])).

fof(f243,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f242])).

fof(f165,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) != X0
        | r1_xboole_0(X0,X1) )
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f164])).

fof(f1926,plain,
    ( spl2_98
    | ~ spl2_16
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f299,f242,f160,f1924])).

fof(f299,plain,
    ( ! [X10,X8,X9] :
        ( k4_xboole_0(X8,X9) = k4_xboole_0(X8,k2_xboole_0(X9,X10))
        | ~ r1_xboole_0(k4_xboole_0(X8,X9),X10) )
    | ~ spl2_16
    | ~ spl2_27 ),
    inference(superposition,[],[f243,f161])).

fof(f1794,plain,
    ( spl2_96
    | ~ spl2_17
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f270,f231,f164,f1792])).

fof(f231,plain,
    ( spl2_25
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f270,plain,
    ( ! [X10,X8,X9] :
        ( k3_xboole_0(X8,X9) != k3_xboole_0(X8,k4_xboole_0(X9,X10))
        | r1_xboole_0(k3_xboole_0(X8,X9),X10) )
    | ~ spl2_17
    | ~ spl2_25 ),
    inference(superposition,[],[f165,f232])).

fof(f232,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f231])).

fof(f1657,plain,
    ( spl2_92
    | ~ spl2_23
    | ~ spl2_56
    | ~ spl2_80 ),
    inference(avatar_split_clause,[],[f1197,f1194,f708,f223,f1655])).

fof(f223,plain,
    ( spl2_23
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f708,plain,
    ( spl2_56
  <=> ! [X1,X0] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).

fof(f1194,plain,
    ( spl2_80
  <=> ! [X1,X0] :
        ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_80])])).

fof(f1197,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_23
    | ~ spl2_56
    | ~ spl2_80 ),
    inference(forward_demodulation,[],[f1195,f716])).

fof(f716,plain,
    ( ! [X0,X1] : k3_subset_1(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl2_23
    | ~ spl2_56 ),
    inference(unit_resulting_resolution,[],[f709,f224])).

fof(f224,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f223])).

fof(f709,plain,
    ( ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))
    | ~ spl2_56 ),
    inference(avatar_component_clause,[],[f708])).

fof(f1195,plain,
    ( ! [X0,X1] :
        ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_80 ),
    inference(avatar_component_clause,[],[f1194])).

fof(f1488,plain,
    ( spl2_88
    | ~ spl2_9
    | ~ spl2_57
    | ~ spl2_87 ),
    inference(avatar_split_clause,[],[f1484,f1481,f766,f131,f1486])).

fof(f131,plain,
    ( spl2_9
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f766,plain,
    ( spl2_57
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).

fof(f1481,plain,
    ( spl2_87
  <=> ! [X3,X2,X4] :
        ( k4_xboole_0(X2,k2_xboole_0(X3,X4)) = k4_xboole_0(k1_xboole_0,X4)
        | ~ r1_tarski(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_87])])).

fof(f1484,plain,
    ( ! [X4,X2,X3] :
        ( k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X4))
        | ~ r1_tarski(X2,X3) )
    | ~ spl2_9
    | ~ spl2_57
    | ~ spl2_87 ),
    inference(forward_demodulation,[],[f1482,f769])).

fof(f769,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl2_9
    | ~ spl2_57 ),
    inference(unit_resulting_resolution,[],[f132,f767])).

fof(f767,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl2_57 ),
    inference(avatar_component_clause,[],[f766])).

fof(f132,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f131])).

fof(f1482,plain,
    ( ! [X4,X2,X3] :
        ( k4_xboole_0(X2,k2_xboole_0(X3,X4)) = k4_xboole_0(k1_xboole_0,X4)
        | ~ r1_tarski(X2,X3) )
    | ~ spl2_87 ),
    inference(avatar_component_clause,[],[f1481])).

fof(f1483,plain,
    ( spl2_87
    | ~ spl2_19
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f293,f242,f172,f1481])).

fof(f293,plain,
    ( ! [X4,X2,X3] :
        ( k4_xboole_0(X2,k2_xboole_0(X3,X4)) = k4_xboole_0(k1_xboole_0,X4)
        | ~ r1_tarski(X2,X3) )
    | ~ spl2_19
    | ~ spl2_27 ),
    inference(superposition,[],[f243,f173])).

fof(f1196,plain,
    ( spl2_80
    | ~ spl2_23
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f259,f227,f223,f1194])).

fof(f227,plain,
    ( spl2_24
  <=> ! [X1,X0] :
        ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f259,plain,
    ( ! [X0,X1] :
        ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_23
    | ~ spl2_24 ),
    inference(duplicate_literal_removal,[],[f255])).

fof(f255,plain,
    ( ! [X0,X1] :
        ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_23
    | ~ spl2_24 ),
    inference(superposition,[],[f228,f224])).

fof(f228,plain,
    ( ! [X0,X1] :
        ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f227])).

fof(f966,plain,
    ( spl2_72
    | ~ spl2_8
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f262,f231,f127,f964])).

fof(f262,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3))
    | ~ spl2_8
    | ~ spl2_25 ),
    inference(superposition,[],[f232,f128])).

fof(f851,plain,
    ( spl2_65
    | ~ spl2_10
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f184,f152,f136,f849])).

fof(f136,plain,
    ( spl2_10
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f184,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))
    | ~ spl2_10
    | ~ spl2_14 ),
    inference(superposition,[],[f153,f137])).

fof(f137,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f136])).

fof(f768,plain,
    ( spl2_57
    | ~ spl2_6
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f188,f156,f119,f766])).

fof(f119,plain,
    ( spl2_6
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f156,plain,
    ( spl2_15
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f188,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_xboole_0) )
    | ~ spl2_6
    | ~ spl2_15 ),
    inference(superposition,[],[f157,f120])).

fof(f120,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f119])).

fof(f157,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f156])).

fof(f710,plain,
    ( spl2_56
    | ~ spl2_9
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f177,f148,f131,f708])).

fof(f177,plain,
    ( ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))
    | ~ spl2_9
    | ~ spl2_13 ),
    inference(unit_resulting_resolution,[],[f132,f149])).

fof(f704,plain,
    ( ~ spl2_4
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_38
    | spl2_44 ),
    inference(avatar_split_clause,[],[f583,f579,f392,f103,f98,f108])).

fof(f108,plain,
    ( spl2_4
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f392,plain,
    ( spl2_38
  <=> ! [X1,X3] :
        ( k1_tops_1(X1,X3) = X3
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v3_pre_topc(X3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f583,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_38
    | spl2_44 ),
    inference(unit_resulting_resolution,[],[f100,f105,f581,f393])).

fof(f393,plain,
    ( ! [X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | k1_tops_1(X1,X3) = X3
        | ~ v3_pre_topc(X3,X1) )
    | ~ spl2_38 ),
    inference(avatar_component_clause,[],[f392])).

fof(f685,plain,
    ( spl2_5
    | ~ spl2_44
    | ~ spl2_53 ),
    inference(avatar_contradiction_clause,[],[f684])).

fof(f684,plain,
    ( $false
    | spl2_5
    | ~ spl2_44
    | ~ spl2_53 ),
    inference(subsumption_resolution,[],[f113,f680])).

fof(f680,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_44
    | ~ spl2_53 ),
    inference(superposition,[],[f652,f580])).

fof(f580,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_44 ),
    inference(avatar_component_clause,[],[f579])).

fof(f652,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_53 ),
    inference(avatar_component_clause,[],[f650])).

fof(f650,plain,
    ( spl2_53
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).

fof(f113,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl2_5
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f674,plain,
    ( spl2_54
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_28
    | ~ spl2_31
    | ~ spl2_34
    | ~ spl2_42 ),
    inference(avatar_split_clause,[],[f536,f509,f351,f323,f248,f112,f103,f98,f671])).

fof(f248,plain,
    ( spl2_28
  <=> ! [X1,X0,X2] :
        ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f323,plain,
    ( spl2_31
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f536,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_5
    | ~ spl2_28
    | ~ spl2_31
    | ~ spl2_34
    | ~ spl2_42 ),
    inference(subsumption_resolution,[],[f316,f535])).

fof(f535,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_31
    | ~ spl2_34
    | ~ spl2_42 ),
    inference(forward_demodulation,[],[f525,f365])).

fof(f525,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3
    | ~ spl2_31
    | ~ spl2_42 ),
    inference(unit_resulting_resolution,[],[f105,f511,f324])).

fof(f324,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f323])).

fof(f316,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_5
    | ~ spl2_28 ),
    inference(superposition,[],[f249,f114])).

fof(f114,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f112])).

fof(f249,plain,
    ( ! [X2,X0,X1] :
        ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f248])).

fof(f653,plain,
    ( spl2_53
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_36 ),
    inference(avatar_split_clause,[],[f385,f382,f103,f98,f650])).

fof(f382,plain,
    ( spl2_36
  <=> ! [X1,X0] :
        ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f385,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_36 ),
    inference(unit_resulting_resolution,[],[f100,f105,f383])).

fof(f383,plain,
    ( ! [X0,X1] :
        ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_36 ),
    inference(avatar_component_clause,[],[f382])).

fof(f644,plain,
    ( spl2_52
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_35 ),
    inference(avatar_split_clause,[],[f374,f355,f103,f98,f641])).

fof(f355,plain,
    ( spl2_35
  <=> ! [X1,X0] :
        ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f374,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_35 ),
    inference(unit_resulting_resolution,[],[f100,f105,f356])).

fof(f356,plain,
    ( ! [X0,X1] :
        ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_35 ),
    inference(avatar_component_clause,[],[f355])).

fof(f595,plain,
    ( spl2_46
    | ~ spl2_3
    | ~ spl2_28 ),
    inference(avatar_split_clause,[],[f315,f248,f103,f593])).

fof(f315,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl2_3
    | ~ spl2_28 ),
    inference(unit_resulting_resolution,[],[f105,f249])).

fof(f582,plain,
    ( ~ spl2_44
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_41 ),
    inference(avatar_split_clause,[],[f507,f455,f108,f103,f98,f93,f579])).

fof(f93,plain,
    ( spl2_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f455,plain,
    ( spl2_41
  <=> ! [X0,X2] :
        ( v3_pre_topc(X2,X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_tops_1(X0,X2) != X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).

fof(f507,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_41 ),
    inference(unit_resulting_resolution,[],[f100,f95,f109,f105,f456])).

fof(f456,plain,
    ( ! [X2,X0] :
        ( k1_tops_1(X0,X2) != X2
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | v3_pre_topc(X2,X0) )
    | ~ spl2_41 ),
    inference(avatar_component_clause,[],[f455])).

fof(f109,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f95,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f512,plain,
    ( spl2_42
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_30 ),
    inference(avatar_split_clause,[],[f326,f319,f103,f98,f509])).

fof(f319,plain,
    ( spl2_30
  <=> ! [X1,X0] :
        ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f326,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_30 ),
    inference(unit_resulting_resolution,[],[f100,f105,f320])).

fof(f320,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f319])).

fof(f475,plain,
    ( ~ spl2_2
    | ~ spl2_3
    | ~ spl2_40 ),
    inference(avatar_contradiction_clause,[],[f472])).

fof(f472,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_40 ),
    inference(subsumption_resolution,[],[f105,f460])).

fof(f460,plain,
    ( ! [X0] : ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_40 ),
    inference(unit_resulting_resolution,[],[f100,f453])).

fof(f453,plain,
    ( ! [X3,X1] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1) )
    | ~ spl2_40 ),
    inference(avatar_component_clause,[],[f452])).

fof(f452,plain,
    ( spl2_40
  <=> ! [X1,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f457,plain,
    ( spl2_40
    | spl2_41 ),
    inference(avatar_split_clause,[],[f69,f455,f452])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).

fof(f422,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_37 ),
    inference(avatar_contradiction_clause,[],[f418])).

fof(f418,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_37 ),
    inference(subsumption_resolution,[],[f105,f400])).

fof(f400,plain,
    ( ! [X0] : ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_37 ),
    inference(unit_resulting_resolution,[],[f100,f95,f390])).

fof(f390,plain,
    ( ! [X2,X0] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f389])).

fof(f389,plain,
    ( spl2_37
  <=> ! [X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f394,plain,
    ( spl2_37
    | spl2_38 ),
    inference(avatar_split_clause,[],[f68,f392,f389])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f384,plain,(
    spl2_36 ),
    inference(avatar_split_clause,[],[f67,f382])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f357,plain,(
    spl2_35 ),
    inference(avatar_split_clause,[],[f66,f355])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f353,plain,(
    spl2_34 ),
    inference(avatar_split_clause,[],[f65,f351])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f331,plain,(
    spl2_32 ),
    inference(avatar_split_clause,[],[f91,f329])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f325,plain,(
    spl2_31 ),
    inference(avatar_split_clause,[],[f90,f323])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f321,plain,(
    spl2_30 ),
    inference(avatar_split_clause,[],[f79,f319])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f314,plain,
    ( spl2_29
    | ~ spl2_19
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f238,f196,f172,f311])).

fof(f238,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0))
    | ~ spl2_19
    | ~ spl2_21 ),
    inference(unit_resulting_resolution,[],[f198,f173])).

fof(f250,plain,(
    spl2_28 ),
    inference(avatar_split_clause,[],[f89,f248])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f244,plain,(
    spl2_27 ),
    inference(avatar_split_clause,[],[f88,f242])).

fof(f88,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f233,plain,(
    spl2_25 ),
    inference(avatar_split_clause,[],[f86,f231])).

fof(f86,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f229,plain,(
    spl2_24 ),
    inference(avatar_split_clause,[],[f78,f227])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f225,plain,(
    spl2_23 ),
    inference(avatar_split_clause,[],[f77,f223])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f199,plain,
    ( spl2_21
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f175,f144,f103,f196])).

fof(f144,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f175,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(unit_resulting_resolution,[],[f105,f145])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f144])).

fof(f174,plain,(
    spl2_19 ),
    inference(avatar_split_clause,[],[f85,f172])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f170,plain,(
    spl2_18 ),
    inference(avatar_split_clause,[],[f84,f168])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f166,plain,(
    spl2_17 ),
    inference(avatar_split_clause,[],[f81,f164])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f162,plain,(
    spl2_16 ),
    inference(avatar_split_clause,[],[f80,f160])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f158,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f75,f156])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f154,plain,(
    spl2_14 ),
    inference(avatar_split_clause,[],[f73,f152])).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f150,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f83,f148])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f146,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f82,f144])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f142,plain,
    ( spl2_11
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f134,f131,f123,f140])).

fof(f123,plain,
    ( spl2_7
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f134,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(superposition,[],[f132,f124])).

fof(f124,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f123])).

fof(f138,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f72,f136])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f133,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f71,f131])).

fof(f71,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f129,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f70,f127])).

fof(f70,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f125,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f63,f123])).

fof(f63,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f121,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f62,f119])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f117,plain,
    ( ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f116,f112,f108])).

fof(f116,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f61,f114])).

fof(f61,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f50,f52,f51])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | ~ v3_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f115,plain,
    ( spl2_4
    | spl2_5 ),
    inference(avatar_split_clause,[],[f60,f112,f108])).

fof(f60,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f106,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f59,f103])).

fof(f59,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f53])).

fof(f101,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f58,f98])).

fof(f58,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f96,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f57,f93])).

fof(f57,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:16:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (17329)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (17339)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (17331)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (17337)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.50  % (17328)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (17330)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (17333)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (17332)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (17336)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.51  % (17338)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.51  % (17340)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.51  % (17341)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (17334)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.52  % (17326)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.52  % (17335)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.52  % (17343)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.53  % (17327)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 1.36/0.53  % (17342)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 3.84/0.86  % (17331)Refutation found. Thanks to Tanya!
% 3.84/0.86  % SZS status Theorem for theBenchmark
% 3.84/0.86  % SZS output start Proof for theBenchmark
% 3.84/0.86  fof(f9739,plain,(
% 3.84/0.86    $false),
% 3.84/0.86    inference(avatar_sat_refutation,[],[f96,f101,f106,f115,f117,f121,f125,f129,f133,f138,f142,f146,f150,f154,f158,f162,f166,f170,f174,f199,f225,f229,f233,f244,f250,f314,f321,f325,f331,f353,f357,f384,f394,f422,f457,f475,f512,f582,f595,f644,f653,f674,f685,f704,f710,f768,f851,f966,f1196,f1483,f1488,f1657,f1794,f1926,f1988,f2642,f2721,f4126,f5761,f6970,f7100,f8244,f8714,f9216,f9666,f9735])).
% 3.84/0.86  fof(f9735,plain,(
% 3.84/0.86    ~spl2_16 | spl2_44 | ~spl2_123 | ~spl2_205 | ~spl2_275),
% 3.84/0.86    inference(avatar_contradiction_clause,[],[f9734])).
% 3.84/0.86  fof(f9734,plain,(
% 3.84/0.86    $false | (~spl2_16 | spl2_44 | ~spl2_123 | ~spl2_205 | ~spl2_275)),
% 3.84/0.86    inference(subsumption_resolution,[],[f581,f9733])).
% 3.84/0.86  fof(f9733,plain,(
% 3.84/0.86    sK1 = k1_tops_1(sK0,sK1) | (~spl2_16 | ~spl2_123 | ~spl2_205 | ~spl2_275)),
% 3.84/0.86    inference(subsumption_resolution,[],[f2723,f9714])).
% 3.84/0.86  fof(f9714,plain,(
% 3.84/0.86    r1_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_205 | ~spl2_275)),
% 3.84/0.86    inference(superposition,[],[f9665,f6969])).
% 3.84/0.86  fof(f6969,plain,(
% 3.84/0.86    sK1 = k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl2_205),
% 3.84/0.86    inference(avatar_component_clause,[],[f6967])).
% 3.84/0.86  fof(f6967,plain,(
% 3.84/0.86    spl2_205 <=> sK1 = k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_205])])).
% 3.84/0.86  fof(f9665,plain,(
% 3.84/0.86    ( ! [X12,X11] : (r1_xboole_0(k4_xboole_0(X11,X12),X12)) ) | ~spl2_275),
% 3.84/0.86    inference(avatar_component_clause,[],[f9664])).
% 3.84/0.86  fof(f9664,plain,(
% 3.84/0.86    spl2_275 <=> ! [X11,X12] : r1_xboole_0(k4_xboole_0(X11,X12),X12)),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_275])])).
% 3.84/0.86  fof(f2723,plain,(
% 3.84/0.86    sK1 = k1_tops_1(sK0,sK1) | ~r1_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_16 | ~spl2_123)),
% 3.84/0.86    inference(superposition,[],[f2720,f161])).
% 3.84/0.86  fof(f161,plain,(
% 3.84/0.86    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) ) | ~spl2_16),
% 3.84/0.86    inference(avatar_component_clause,[],[f160])).
% 3.84/0.86  fof(f160,plain,(
% 3.84/0.86    spl2_16 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 3.84/0.86  fof(f2720,plain,(
% 3.84/0.86    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_123),
% 3.84/0.86    inference(avatar_component_clause,[],[f2718])).
% 3.84/0.86  fof(f2718,plain,(
% 3.84/0.86    spl2_123 <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_123])])).
% 3.84/0.86  fof(f581,plain,(
% 3.84/0.86    sK1 != k1_tops_1(sK0,sK1) | spl2_44),
% 3.84/0.86    inference(avatar_component_clause,[],[f579])).
% 3.84/0.86  fof(f579,plain,(
% 3.84/0.86    spl2_44 <=> sK1 = k1_tops_1(sK0,sK1)),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_44])])).
% 3.84/0.86  fof(f9666,plain,(
% 3.84/0.86    spl2_275 | ~spl2_8 | ~spl2_14 | ~spl2_65 | ~spl2_72 | ~spl2_96),
% 3.84/0.86    inference(avatar_split_clause,[],[f1836,f1792,f964,f849,f152,f127,f9664])).
% 3.84/0.86  fof(f127,plain,(
% 3.84/0.86    spl2_8 <=> ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 3.84/0.86  fof(f152,plain,(
% 3.84/0.86    spl2_14 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 3.84/0.86  fof(f849,plain,(
% 3.84/0.86    spl2_65 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_65])])).
% 3.84/0.86  fof(f964,plain,(
% 3.84/0.86    spl2_72 <=> ! [X3,X2] : k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_72])])).
% 3.84/0.86  fof(f1792,plain,(
% 3.84/0.86    spl2_96 <=> ! [X9,X8,X10] : (k3_xboole_0(X8,X9) != k3_xboole_0(X8,k4_xboole_0(X9,X10)) | r1_xboole_0(k3_xboole_0(X8,X9),X10))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_96])])).
% 3.84/0.86  fof(f1836,plain,(
% 3.84/0.86    ( ! [X12,X11] : (r1_xboole_0(k4_xboole_0(X11,X12),X12)) ) | (~spl2_8 | ~spl2_14 | ~spl2_65 | ~spl2_72 | ~spl2_96)),
% 3.84/0.86    inference(forward_demodulation,[],[f1835,f965])).
% 3.84/0.86  fof(f965,plain,(
% 3.84/0.86    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3))) ) | ~spl2_72),
% 3.84/0.86    inference(avatar_component_clause,[],[f964])).
% 3.84/0.86  fof(f1835,plain,(
% 3.84/0.86    ( ! [X12,X11] : (r1_xboole_0(k3_xboole_0(X11,k4_xboole_0(X11,X12)),X12)) ) | (~spl2_8 | ~spl2_14 | ~spl2_65 | ~spl2_72 | ~spl2_96)),
% 3.84/0.86    inference(forward_demodulation,[],[f1834,f854])).
% 3.84/0.86  fof(f854,plain,(
% 3.84/0.86    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) ) | (~spl2_14 | ~spl2_65)),
% 3.84/0.86    inference(superposition,[],[f850,f153])).
% 3.84/0.86  fof(f153,plain,(
% 3.84/0.86    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) ) | ~spl2_14),
% 3.84/0.86    inference(avatar_component_clause,[],[f152])).
% 3.84/0.86  fof(f850,plain,(
% 3.84/0.86    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) ) | ~spl2_65),
% 3.84/0.86    inference(avatar_component_clause,[],[f849])).
% 3.84/0.86  fof(f1834,plain,(
% 3.84/0.86    ( ! [X12,X11] : (r1_xboole_0(k3_xboole_0(k4_xboole_0(X11,X12),X11),X12)) ) | (~spl2_8 | ~spl2_14 | ~spl2_65 | ~spl2_72 | ~spl2_96)),
% 3.84/0.86    inference(trivial_inequality_removal,[],[f1833])).
% 3.84/0.86  fof(f1833,plain,(
% 3.84/0.86    ( ! [X12,X11] : (k4_xboole_0(X11,X12) != k4_xboole_0(X11,X12) | r1_xboole_0(k3_xboole_0(k4_xboole_0(X11,X12),X11),X12)) ) | (~spl2_8 | ~spl2_14 | ~spl2_65 | ~spl2_72 | ~spl2_96)),
% 3.84/0.86    inference(forward_demodulation,[],[f1832,f965])).
% 3.84/0.86  fof(f1832,plain,(
% 3.84/0.86    ( ! [X12,X11] : (k4_xboole_0(X11,X12) != k3_xboole_0(X11,k4_xboole_0(X11,X12)) | r1_xboole_0(k3_xboole_0(k4_xboole_0(X11,X12),X11),X12)) ) | (~spl2_8 | ~spl2_14 | ~spl2_65 | ~spl2_96)),
% 3.84/0.86    inference(forward_demodulation,[],[f1813,f854])).
% 3.84/0.86  fof(f1813,plain,(
% 3.84/0.86    ( ! [X12,X11] : (k4_xboole_0(X11,X12) != k3_xboole_0(k4_xboole_0(X11,X12),X11) | r1_xboole_0(k3_xboole_0(k4_xboole_0(X11,X12),X11),X12)) ) | (~spl2_8 | ~spl2_96)),
% 3.84/0.86    inference(superposition,[],[f1793,f128])).
% 3.84/0.86  fof(f128,plain,(
% 3.84/0.86    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) ) | ~spl2_8),
% 3.84/0.86    inference(avatar_component_clause,[],[f127])).
% 3.84/0.86  fof(f1793,plain,(
% 3.84/0.86    ( ! [X10,X8,X9] : (k3_xboole_0(X8,X9) != k3_xboole_0(X8,k4_xboole_0(X9,X10)) | r1_xboole_0(k3_xboole_0(X8,X9),X10)) ) | ~spl2_96),
% 3.84/0.86    inference(avatar_component_clause,[],[f1792])).
% 3.84/0.86  fof(f9216,plain,(
% 3.84/0.86    spl2_213 | ~spl2_158 | ~spl2_259),
% 3.84/0.86    inference(avatar_split_clause,[],[f8990,f8712,f4123,f7097])).
% 3.84/0.86  fof(f7097,plain,(
% 3.84/0.86    spl2_213 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_213])])).
% 3.84/0.86  fof(f4123,plain,(
% 3.84/0.86    spl2_158 <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_158])])).
% 3.84/0.86  fof(f8712,plain,(
% 3.84/0.86    spl2_259 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_259])])).
% 3.84/0.86  fof(f8990,plain,(
% 3.84/0.86    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | (~spl2_158 | ~spl2_259)),
% 3.84/0.86    inference(superposition,[],[f8713,f4125])).
% 3.84/0.86  fof(f4125,plain,(
% 3.84/0.86    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_158),
% 3.84/0.86    inference(avatar_component_clause,[],[f4123])).
% 3.84/0.86  fof(f8713,plain,(
% 3.84/0.86    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl2_259),
% 3.84/0.86    inference(avatar_component_clause,[],[f8712])).
% 3.84/0.86  fof(f8714,plain,(
% 3.84/0.86    spl2_259 | ~spl2_189 | ~spl2_256),
% 3.84/0.86    inference(avatar_split_clause,[],[f8251,f8242,f5759,f8712])).
% 3.84/0.86  fof(f5759,plain,(
% 3.84/0.86    spl2_189 <=> ! [X29,X28,X30] : (k1_xboole_0 != k4_xboole_0(X28,X29) | r1_tarski(X28,k2_xboole_0(X29,X30)))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_189])])).
% 3.84/0.86  fof(f8242,plain,(
% 3.84/0.86    spl2_256 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_256])])).
% 3.84/0.86  fof(f8251,plain,(
% 3.84/0.86    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | (~spl2_189 | ~spl2_256)),
% 3.84/0.86    inference(unit_resulting_resolution,[],[f8243,f5760])).
% 3.84/0.86  fof(f5760,plain,(
% 3.84/0.86    ( ! [X30,X28,X29] : (k1_xboole_0 != k4_xboole_0(X28,X29) | r1_tarski(X28,k2_xboole_0(X29,X30))) ) | ~spl2_189),
% 3.84/0.86    inference(avatar_component_clause,[],[f5759])).
% 3.84/0.86  fof(f8243,plain,(
% 3.84/0.86    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl2_256),
% 3.84/0.86    inference(avatar_component_clause,[],[f8242])).
% 3.84/0.86  fof(f8244,plain,(
% 3.84/0.86    spl2_256 | ~spl2_11 | ~spl2_19),
% 3.84/0.86    inference(avatar_split_clause,[],[f204,f172,f140,f8242])).
% 3.84/0.86  fof(f140,plain,(
% 3.84/0.86    spl2_11 <=> ! [X0] : r1_tarski(X0,X0)),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 3.84/0.86  fof(f172,plain,(
% 3.84/0.86    spl2_19 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 3.84/0.86  fof(f204,plain,(
% 3.84/0.86    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | (~spl2_11 | ~spl2_19)),
% 3.84/0.86    inference(unit_resulting_resolution,[],[f141,f173])).
% 3.84/0.86  fof(f173,plain,(
% 3.84/0.86    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) ) | ~spl2_19),
% 3.84/0.86    inference(avatar_component_clause,[],[f172])).
% 3.84/0.86  fof(f141,plain,(
% 3.84/0.86    ( ! [X0] : (r1_tarski(X0,X0)) ) | ~spl2_11),
% 3.84/0.86    inference(avatar_component_clause,[],[f140])).
% 3.84/0.86  fof(f7100,plain,(
% 3.84/0.86    ~spl2_213 | ~spl2_13 | spl2_204),
% 3.84/0.86    inference(avatar_split_clause,[],[f6971,f6963,f148,f7097])).
% 3.84/0.86  fof(f148,plain,(
% 3.84/0.86    spl2_13 <=> ! [X1,X0] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 3.84/0.86  fof(f6963,plain,(
% 3.84/0.86    spl2_204 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_204])])).
% 3.84/0.86  fof(f6971,plain,(
% 3.84/0.86    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | (~spl2_13 | spl2_204)),
% 3.84/0.86    inference(unit_resulting_resolution,[],[f6965,f149])).
% 3.84/0.86  fof(f149,plain,(
% 3.84/0.86    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) ) | ~spl2_13),
% 3.84/0.86    inference(avatar_component_clause,[],[f148])).
% 3.84/0.86  fof(f6965,plain,(
% 3.84/0.86    ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | spl2_204),
% 3.84/0.86    inference(avatar_component_clause,[],[f6963])).
% 3.84/0.86  fof(f6970,plain,(
% 3.84/0.86    ~spl2_204 | spl2_205 | ~spl2_54 | ~spl2_92),
% 3.84/0.86    inference(avatar_split_clause,[],[f1679,f1655,f671,f6967,f6963])).
% 3.84/0.86  fof(f671,plain,(
% 3.84/0.86    spl2_54 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_54])])).
% 3.84/0.86  fof(f1655,plain,(
% 3.84/0.86    spl2_92 <=> ! [X1,X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_92])])).
% 3.84/0.86  fof(f1679,plain,(
% 3.84/0.86    sK1 = k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | (~spl2_54 | ~spl2_92)),
% 3.84/0.86    inference(superposition,[],[f1656,f673])).
% 3.84/0.86  fof(f673,plain,(
% 3.84/0.86    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl2_54),
% 3.84/0.86    inference(avatar_component_clause,[],[f671])).
% 3.84/0.86  fof(f1656,plain,(
% 3.84/0.86    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_92),
% 3.84/0.86    inference(avatar_component_clause,[],[f1655])).
% 3.84/0.86  fof(f5761,plain,(
% 3.84/0.86    spl2_189 | ~spl2_18 | ~spl2_29 | ~spl2_98 | ~spl2_99 | ~spl2_121),
% 3.84/0.86    inference(avatar_split_clause,[],[f2692,f2640,f1986,f1924,f311,f168,f5759])).
% 3.84/0.86  fof(f168,plain,(
% 3.84/0.86    spl2_18 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0)),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 3.84/0.86  fof(f311,plain,(
% 3.84/0.86    spl2_29 <=> k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 3.84/0.86  fof(f1924,plain,(
% 3.84/0.86    spl2_98 <=> ! [X9,X8,X10] : (k4_xboole_0(X8,X9) = k4_xboole_0(X8,k2_xboole_0(X9,X10)) | ~r1_xboole_0(k4_xboole_0(X8,X9),X10))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_98])])).
% 3.84/0.86  fof(f1986,plain,(
% 3.84/0.86    spl2_99 <=> ! [X9,X8,X10] : (k4_xboole_0(X8,X9) != k4_xboole_0(X8,k2_xboole_0(X9,X10)) | r1_xboole_0(k4_xboole_0(X8,X9),X10))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_99])])).
% 3.84/0.86  fof(f2640,plain,(
% 3.84/0.86    spl2_121 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(u1_struct_0(sK0),X0))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_121])])).
% 3.84/0.86  fof(f2692,plain,(
% 3.84/0.86    ( ! [X30,X28,X29] : (k1_xboole_0 != k4_xboole_0(X28,X29) | r1_tarski(X28,k2_xboole_0(X29,X30))) ) | (~spl2_18 | ~spl2_29 | ~spl2_98 | ~spl2_99 | ~spl2_121)),
% 3.84/0.86    inference(subsumption_resolution,[],[f1975,f2691])).
% 3.84/0.86  fof(f2691,plain,(
% 3.84/0.86    ( ! [X6] : (r1_xboole_0(k1_xboole_0,X6)) ) | (~spl2_29 | ~spl2_99 | ~spl2_121)),
% 3.84/0.86    inference(forward_demodulation,[],[f2690,f313])).
% 3.84/0.86  fof(f313,plain,(
% 3.84/0.86    k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0)) | ~spl2_29),
% 3.84/0.86    inference(avatar_component_clause,[],[f311])).
% 3.84/0.86  fof(f2690,plain,(
% 3.84/0.86    ( ! [X6] : (r1_xboole_0(k4_xboole_0(sK1,u1_struct_0(sK0)),X6)) ) | (~spl2_29 | ~spl2_99 | ~spl2_121)),
% 3.84/0.86    inference(trivial_inequality_removal,[],[f2689])).
% 3.84/0.86  fof(f2689,plain,(
% 3.84/0.86    ( ! [X6] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k4_xboole_0(sK1,u1_struct_0(sK0)),X6)) ) | (~spl2_29 | ~spl2_99 | ~spl2_121)),
% 3.84/0.86    inference(forward_demodulation,[],[f2660,f313])).
% 3.84/0.86  fof(f2660,plain,(
% 3.84/0.86    ( ! [X6] : (k1_xboole_0 != k4_xboole_0(sK1,u1_struct_0(sK0)) | r1_xboole_0(k4_xboole_0(sK1,u1_struct_0(sK0)),X6)) ) | (~spl2_99 | ~spl2_121)),
% 3.84/0.86    inference(superposition,[],[f1987,f2641])).
% 3.84/0.86  fof(f2641,plain,(
% 3.84/0.86    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(u1_struct_0(sK0),X0))) ) | ~spl2_121),
% 3.84/0.86    inference(avatar_component_clause,[],[f2640])).
% 3.84/0.86  fof(f1987,plain,(
% 3.84/0.86    ( ! [X10,X8,X9] : (k4_xboole_0(X8,X9) != k4_xboole_0(X8,k2_xboole_0(X9,X10)) | r1_xboole_0(k4_xboole_0(X8,X9),X10)) ) | ~spl2_99),
% 3.84/0.86    inference(avatar_component_clause,[],[f1986])).
% 3.84/0.86  fof(f1975,plain,(
% 3.84/0.86    ( ! [X30,X28,X29] : (k1_xboole_0 != k4_xboole_0(X28,X29) | r1_tarski(X28,k2_xboole_0(X29,X30)) | ~r1_xboole_0(k1_xboole_0,X30)) ) | (~spl2_18 | ~spl2_98)),
% 3.84/0.86    inference(inner_rewriting,[],[f1946])).
% 3.84/0.86  fof(f1946,plain,(
% 3.84/0.86    ( ! [X30,X28,X29] : (k1_xboole_0 != k4_xboole_0(X28,X29) | r1_tarski(X28,k2_xboole_0(X29,X30)) | ~r1_xboole_0(k4_xboole_0(X28,X29),X30)) ) | (~spl2_18 | ~spl2_98)),
% 3.84/0.86    inference(superposition,[],[f169,f1925])).
% 3.84/0.86  fof(f1925,plain,(
% 3.84/0.86    ( ! [X10,X8,X9] : (k4_xboole_0(X8,X9) = k4_xboole_0(X8,k2_xboole_0(X9,X10)) | ~r1_xboole_0(k4_xboole_0(X8,X9),X10)) ) | ~spl2_98),
% 3.84/0.86    inference(avatar_component_clause,[],[f1924])).
% 3.84/0.86  fof(f169,plain,(
% 3.84/0.86    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) ) | ~spl2_18),
% 3.84/0.86    inference(avatar_component_clause,[],[f168])).
% 3.84/0.86  fof(f4126,plain,(
% 3.84/0.86    spl2_158 | ~spl2_2 | ~spl2_3 | ~spl2_32 | ~spl2_34 | ~spl2_42),
% 3.84/0.86    inference(avatar_split_clause,[],[f533,f509,f351,f329,f103,f98,f4123])).
% 3.84/0.86  fof(f98,plain,(
% 3.84/0.86    spl2_2 <=> l1_pre_topc(sK0)),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 3.84/0.86  fof(f103,plain,(
% 3.84/0.86    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 3.84/0.86  fof(f329,plain,(
% 3.84/0.86    spl2_32 <=> ! [X1,X0,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 3.84/0.86  fof(f351,plain,(
% 3.84/0.86    spl2_34 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 3.84/0.86  fof(f509,plain,(
% 3.84/0.86    spl2_42 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 3.84/0.86  fof(f533,plain,(
% 3.84/0.86    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_32 | ~spl2_34 | ~spl2_42)),
% 3.84/0.86    inference(forward_demodulation,[],[f529,f365])).
% 3.84/0.86  fof(f365,plain,(
% 3.84/0.86    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_34)),
% 3.84/0.86    inference(unit_resulting_resolution,[],[f100,f105,f352])).
% 3.84/0.86  fof(f352,plain,(
% 3.84/0.86    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_34),
% 3.84/0.86    inference(avatar_component_clause,[],[f351])).
% 3.84/0.86  fof(f105,plain,(
% 3.84/0.86    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 3.84/0.86    inference(avatar_component_clause,[],[f103])).
% 3.84/0.86  fof(f100,plain,(
% 3.84/0.86    l1_pre_topc(sK0) | ~spl2_2),
% 3.84/0.86    inference(avatar_component_clause,[],[f98])).
% 3.84/0.86  fof(f529,plain,(
% 3.84/0.86    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_3 | ~spl2_32 | ~spl2_42)),
% 3.84/0.86    inference(unit_resulting_resolution,[],[f105,f511,f330])).
% 3.84/0.86  fof(f330,plain,(
% 3.84/0.86    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_32),
% 3.84/0.86    inference(avatar_component_clause,[],[f329])).
% 3.84/0.86  fof(f511,plain,(
% 3.84/0.86    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_42),
% 3.84/0.86    inference(avatar_component_clause,[],[f509])).
% 3.84/0.86  fof(f2721,plain,(
% 3.84/0.86    spl2_123 | ~spl2_46 | ~spl2_52),
% 3.84/0.86    inference(avatar_split_clause,[],[f645,f641,f593,f2718])).
% 3.84/0.86  fof(f593,plain,(
% 3.84/0.86    spl2_46 <=> ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_46])])).
% 3.84/0.86  fof(f641,plain,(
% 3.84/0.86    spl2_52 <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_52])])).
% 3.84/0.86  fof(f645,plain,(
% 3.84/0.86    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl2_46 | ~spl2_52)),
% 3.84/0.86    inference(superposition,[],[f643,f594])).
% 3.84/0.86  fof(f594,plain,(
% 3.84/0.86    ( ! [X0] : (k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl2_46),
% 3.84/0.86    inference(avatar_component_clause,[],[f593])).
% 3.84/0.86  fof(f643,plain,(
% 3.84/0.86    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl2_52),
% 3.84/0.86    inference(avatar_component_clause,[],[f641])).
% 3.84/0.86  fof(f2642,plain,(
% 3.84/0.86    spl2_121 | ~spl2_21 | ~spl2_88),
% 3.84/0.86    inference(avatar_split_clause,[],[f1504,f1486,f196,f2640])).
% 3.84/0.86  fof(f196,plain,(
% 3.84/0.86    spl2_21 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 3.84/0.86  fof(f1486,plain,(
% 3.84/0.86    spl2_88 <=> ! [X3,X2,X4] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X4)) | ~r1_tarski(X2,X3))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_88])])).
% 3.84/0.86  fof(f1504,plain,(
% 3.84/0.86    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK1,k2_xboole_0(u1_struct_0(sK0),X0))) ) | (~spl2_21 | ~spl2_88)),
% 3.84/0.86    inference(unit_resulting_resolution,[],[f198,f1487])).
% 3.84/0.86  fof(f1487,plain,(
% 3.84/0.86    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X4)) | ~r1_tarski(X2,X3)) ) | ~spl2_88),
% 3.84/0.86    inference(avatar_component_clause,[],[f1486])).
% 3.84/0.86  fof(f198,plain,(
% 3.84/0.86    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl2_21),
% 3.84/0.86    inference(avatar_component_clause,[],[f196])).
% 3.84/0.86  fof(f1988,plain,(
% 3.84/0.86    spl2_99 | ~spl2_17 | ~spl2_27),
% 3.84/0.86    inference(avatar_split_clause,[],[f303,f242,f164,f1986])).
% 3.84/0.86  fof(f164,plain,(
% 3.84/0.86    spl2_17 <=> ! [X1,X0] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0)),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 3.84/0.86  fof(f242,plain,(
% 3.84/0.86    spl2_27 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 3.84/0.86  fof(f303,plain,(
% 3.84/0.86    ( ! [X10,X8,X9] : (k4_xboole_0(X8,X9) != k4_xboole_0(X8,k2_xboole_0(X9,X10)) | r1_xboole_0(k4_xboole_0(X8,X9),X10)) ) | (~spl2_17 | ~spl2_27)),
% 3.84/0.86    inference(superposition,[],[f165,f243])).
% 3.84/0.86  fof(f243,plain,(
% 3.84/0.86    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl2_27),
% 3.84/0.86    inference(avatar_component_clause,[],[f242])).
% 3.84/0.86  fof(f165,plain,(
% 3.84/0.86    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) ) | ~spl2_17),
% 3.84/0.86    inference(avatar_component_clause,[],[f164])).
% 3.84/0.86  fof(f1926,plain,(
% 3.84/0.86    spl2_98 | ~spl2_16 | ~spl2_27),
% 3.84/0.86    inference(avatar_split_clause,[],[f299,f242,f160,f1924])).
% 3.84/0.86  fof(f299,plain,(
% 3.84/0.86    ( ! [X10,X8,X9] : (k4_xboole_0(X8,X9) = k4_xboole_0(X8,k2_xboole_0(X9,X10)) | ~r1_xboole_0(k4_xboole_0(X8,X9),X10)) ) | (~spl2_16 | ~spl2_27)),
% 3.84/0.86    inference(superposition,[],[f243,f161])).
% 3.84/0.86  fof(f1794,plain,(
% 3.84/0.86    spl2_96 | ~spl2_17 | ~spl2_25),
% 3.84/0.86    inference(avatar_split_clause,[],[f270,f231,f164,f1792])).
% 3.84/0.86  fof(f231,plain,(
% 3.84/0.86    spl2_25 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 3.84/0.86  fof(f270,plain,(
% 3.84/0.86    ( ! [X10,X8,X9] : (k3_xboole_0(X8,X9) != k3_xboole_0(X8,k4_xboole_0(X9,X10)) | r1_xboole_0(k3_xboole_0(X8,X9),X10)) ) | (~spl2_17 | ~spl2_25)),
% 3.84/0.86    inference(superposition,[],[f165,f232])).
% 3.84/0.86  fof(f232,plain,(
% 3.84/0.86    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) ) | ~spl2_25),
% 3.84/0.86    inference(avatar_component_clause,[],[f231])).
% 3.84/0.86  fof(f1657,plain,(
% 3.84/0.86    spl2_92 | ~spl2_23 | ~spl2_56 | ~spl2_80),
% 3.84/0.86    inference(avatar_split_clause,[],[f1197,f1194,f708,f223,f1655])).
% 3.84/0.86  fof(f223,plain,(
% 3.84/0.86    spl2_23 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 3.84/0.86  fof(f708,plain,(
% 3.84/0.86    spl2_56 <=> ! [X1,X0] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).
% 3.84/0.86  fof(f1194,plain,(
% 3.84/0.86    spl2_80 <=> ! [X1,X0] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_80])])).
% 3.84/0.86  fof(f1197,plain,(
% 3.84/0.86    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | (~spl2_23 | ~spl2_56 | ~spl2_80)),
% 3.84/0.86    inference(forward_demodulation,[],[f1195,f716])).
% 3.84/0.86  fof(f716,plain,(
% 3.84/0.86    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | (~spl2_23 | ~spl2_56)),
% 3.84/0.86    inference(unit_resulting_resolution,[],[f709,f224])).
% 3.84/0.86  fof(f224,plain,(
% 3.84/0.86    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_23),
% 3.84/0.86    inference(avatar_component_clause,[],[f223])).
% 3.84/0.86  fof(f709,plain,(
% 3.84/0.86    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) ) | ~spl2_56),
% 3.84/0.86    inference(avatar_component_clause,[],[f708])).
% 3.84/0.86  fof(f1195,plain,(
% 3.84/0.86    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_80),
% 3.84/0.86    inference(avatar_component_clause,[],[f1194])).
% 3.84/0.86  fof(f1488,plain,(
% 3.84/0.86    spl2_88 | ~spl2_9 | ~spl2_57 | ~spl2_87),
% 3.84/0.86    inference(avatar_split_clause,[],[f1484,f1481,f766,f131,f1486])).
% 3.84/0.86  fof(f131,plain,(
% 3.84/0.86    spl2_9 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 3.84/0.86  fof(f766,plain,(
% 3.84/0.86    spl2_57 <=> ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).
% 3.84/0.86  fof(f1481,plain,(
% 3.84/0.86    spl2_87 <=> ! [X3,X2,X4] : (k4_xboole_0(X2,k2_xboole_0(X3,X4)) = k4_xboole_0(k1_xboole_0,X4) | ~r1_tarski(X2,X3))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_87])])).
% 3.84/0.86  fof(f1484,plain,(
% 3.84/0.86    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X4)) | ~r1_tarski(X2,X3)) ) | (~spl2_9 | ~spl2_57 | ~spl2_87)),
% 3.84/0.86    inference(forward_demodulation,[],[f1482,f769])).
% 3.84/0.86  fof(f769,plain,(
% 3.84/0.86    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | (~spl2_9 | ~spl2_57)),
% 3.84/0.86    inference(unit_resulting_resolution,[],[f132,f767])).
% 3.84/0.86  fof(f767,plain,(
% 3.84/0.86    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl2_57),
% 3.84/0.86    inference(avatar_component_clause,[],[f766])).
% 3.84/0.86  fof(f132,plain,(
% 3.84/0.86    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl2_9),
% 3.84/0.86    inference(avatar_component_clause,[],[f131])).
% 3.84/0.86  fof(f1482,plain,(
% 3.84/0.86    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X3,X4)) = k4_xboole_0(k1_xboole_0,X4) | ~r1_tarski(X2,X3)) ) | ~spl2_87),
% 3.84/0.86    inference(avatar_component_clause,[],[f1481])).
% 3.84/0.86  fof(f1483,plain,(
% 3.84/0.86    spl2_87 | ~spl2_19 | ~spl2_27),
% 3.84/0.86    inference(avatar_split_clause,[],[f293,f242,f172,f1481])).
% 3.84/0.86  fof(f293,plain,(
% 3.84/0.86    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k2_xboole_0(X3,X4)) = k4_xboole_0(k1_xboole_0,X4) | ~r1_tarski(X2,X3)) ) | (~spl2_19 | ~spl2_27)),
% 3.84/0.86    inference(superposition,[],[f243,f173])).
% 3.84/0.86  fof(f1196,plain,(
% 3.84/0.86    spl2_80 | ~spl2_23 | ~spl2_24),
% 3.84/0.86    inference(avatar_split_clause,[],[f259,f227,f223,f1194])).
% 3.84/0.86  fof(f227,plain,(
% 3.84/0.86    spl2_24 <=> ! [X1,X0] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 3.84/0.86  fof(f259,plain,(
% 3.84/0.86    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | (~spl2_23 | ~spl2_24)),
% 3.84/0.86    inference(duplicate_literal_removal,[],[f255])).
% 3.84/0.86  fof(f255,plain,(
% 3.84/0.86    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | (~spl2_23 | ~spl2_24)),
% 3.84/0.86    inference(superposition,[],[f228,f224])).
% 3.84/0.86  fof(f228,plain,(
% 3.84/0.86    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_24),
% 3.84/0.86    inference(avatar_component_clause,[],[f227])).
% 3.84/0.86  fof(f966,plain,(
% 3.84/0.86    spl2_72 | ~spl2_8 | ~spl2_25),
% 3.84/0.86    inference(avatar_split_clause,[],[f262,f231,f127,f964])).
% 3.84/0.86  fof(f262,plain,(
% 3.84/0.86    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3))) ) | (~spl2_8 | ~spl2_25)),
% 3.84/0.86    inference(superposition,[],[f232,f128])).
% 3.84/0.86  fof(f851,plain,(
% 3.84/0.86    spl2_65 | ~spl2_10 | ~spl2_14),
% 3.84/0.86    inference(avatar_split_clause,[],[f184,f152,f136,f849])).
% 3.84/0.86  fof(f136,plain,(
% 3.84/0.86    spl2_10 <=> ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 3.84/0.86  fof(f184,plain,(
% 3.84/0.86    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) ) | (~spl2_10 | ~spl2_14)),
% 3.84/0.86    inference(superposition,[],[f153,f137])).
% 3.84/0.86  fof(f137,plain,(
% 3.84/0.86    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) ) | ~spl2_10),
% 3.84/0.86    inference(avatar_component_clause,[],[f136])).
% 3.84/0.86  fof(f768,plain,(
% 3.84/0.86    spl2_57 | ~spl2_6 | ~spl2_15),
% 3.84/0.86    inference(avatar_split_clause,[],[f188,f156,f119,f766])).
% 3.84/0.86  fof(f119,plain,(
% 3.84/0.86    spl2_6 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 3.84/0.86  fof(f156,plain,(
% 3.84/0.86    spl2_15 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 3.84/0.86  fof(f188,plain,(
% 3.84/0.86    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) ) | (~spl2_6 | ~spl2_15)),
% 3.84/0.86    inference(superposition,[],[f157,f120])).
% 3.84/0.86  fof(f120,plain,(
% 3.84/0.86    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl2_6),
% 3.84/0.86    inference(avatar_component_clause,[],[f119])).
% 3.84/0.86  fof(f157,plain,(
% 3.84/0.86    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl2_15),
% 3.84/0.86    inference(avatar_component_clause,[],[f156])).
% 3.84/0.86  fof(f710,plain,(
% 3.84/0.86    spl2_56 | ~spl2_9 | ~spl2_13),
% 3.84/0.86    inference(avatar_split_clause,[],[f177,f148,f131,f708])).
% 3.84/0.86  fof(f177,plain,(
% 3.84/0.86    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) ) | (~spl2_9 | ~spl2_13)),
% 3.84/0.86    inference(unit_resulting_resolution,[],[f132,f149])).
% 3.84/0.86  fof(f704,plain,(
% 3.84/0.86    ~spl2_4 | ~spl2_2 | ~spl2_3 | ~spl2_38 | spl2_44),
% 3.84/0.86    inference(avatar_split_clause,[],[f583,f579,f392,f103,f98,f108])).
% 3.84/0.86  fof(f108,plain,(
% 3.84/0.86    spl2_4 <=> v3_pre_topc(sK1,sK0)),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 3.84/0.86  fof(f392,plain,(
% 3.84/0.86    spl2_38 <=> ! [X1,X3] : (k1_tops_1(X1,X3) = X3 | ~l1_pre_topc(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 3.84/0.86  fof(f583,plain,(
% 3.84/0.86    ~v3_pre_topc(sK1,sK0) | (~spl2_2 | ~spl2_3 | ~spl2_38 | spl2_44)),
% 3.84/0.86    inference(unit_resulting_resolution,[],[f100,f105,f581,f393])).
% 3.84/0.86  fof(f393,plain,(
% 3.84/0.86    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1)) ) | ~spl2_38),
% 3.84/0.86    inference(avatar_component_clause,[],[f392])).
% 3.84/0.86  fof(f685,plain,(
% 3.84/0.86    spl2_5 | ~spl2_44 | ~spl2_53),
% 3.84/0.86    inference(avatar_contradiction_clause,[],[f684])).
% 3.84/0.86  fof(f684,plain,(
% 3.84/0.86    $false | (spl2_5 | ~spl2_44 | ~spl2_53)),
% 3.84/0.86    inference(subsumption_resolution,[],[f113,f680])).
% 3.84/0.86  fof(f680,plain,(
% 3.84/0.86    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | (~spl2_44 | ~spl2_53)),
% 3.84/0.86    inference(superposition,[],[f652,f580])).
% 3.84/0.86  fof(f580,plain,(
% 3.84/0.86    sK1 = k1_tops_1(sK0,sK1) | ~spl2_44),
% 3.84/0.86    inference(avatar_component_clause,[],[f579])).
% 3.84/0.86  fof(f652,plain,(
% 3.84/0.86    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl2_53),
% 3.84/0.86    inference(avatar_component_clause,[],[f650])).
% 3.84/0.86  fof(f650,plain,(
% 3.84/0.86    spl2_53 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).
% 3.84/0.86  fof(f113,plain,(
% 3.84/0.86    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl2_5),
% 3.84/0.86    inference(avatar_component_clause,[],[f112])).
% 3.84/0.86  fof(f112,plain,(
% 3.84/0.86    spl2_5 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 3.84/0.86  fof(f674,plain,(
% 3.84/0.86    spl2_54 | ~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_28 | ~spl2_31 | ~spl2_34 | ~spl2_42),
% 3.84/0.86    inference(avatar_split_clause,[],[f536,f509,f351,f323,f248,f112,f103,f98,f671])).
% 3.84/0.86  fof(f248,plain,(
% 3.84/0.86    spl2_28 <=> ! [X1,X0,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 3.84/0.86  fof(f323,plain,(
% 3.84/0.86    spl2_31 <=> ! [X1,X0,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 3.84/0.86  fof(f536,plain,(
% 3.84/0.86    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl2_2 | ~spl2_3 | ~spl2_5 | ~spl2_28 | ~spl2_31 | ~spl2_34 | ~spl2_42)),
% 3.84/0.86    inference(subsumption_resolution,[],[f316,f535])).
% 3.84/0.86  fof(f535,plain,(
% 3.84/0.86    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_3 | ~spl2_31 | ~spl2_34 | ~spl2_42)),
% 3.84/0.86    inference(forward_demodulation,[],[f525,f365])).
% 3.84/0.86  fof(f525,plain,(
% 3.84/0.86    m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_3 | ~spl2_31 | ~spl2_42)),
% 3.84/0.86    inference(unit_resulting_resolution,[],[f105,f511,f324])).
% 3.84/0.86  fof(f324,plain,(
% 3.84/0.86    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_31),
% 3.84/0.86    inference(avatar_component_clause,[],[f323])).
% 3.84/0.86  fof(f316,plain,(
% 3.84/0.86    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_5 | ~spl2_28)),
% 3.84/0.86    inference(superposition,[],[f249,f114])).
% 3.84/0.86  fof(f114,plain,(
% 3.84/0.86    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl2_5),
% 3.84/0.86    inference(avatar_component_clause,[],[f112])).
% 3.84/0.86  fof(f249,plain,(
% 3.84/0.86    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl2_28),
% 3.84/0.86    inference(avatar_component_clause,[],[f248])).
% 3.84/0.86  fof(f653,plain,(
% 3.84/0.86    spl2_53 | ~spl2_2 | ~spl2_3 | ~spl2_36),
% 3.84/0.86    inference(avatar_split_clause,[],[f385,f382,f103,f98,f650])).
% 3.84/0.86  fof(f382,plain,(
% 3.84/0.86    spl2_36 <=> ! [X1,X0] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 3.84/0.86  fof(f385,plain,(
% 3.84/0.86    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_36)),
% 3.84/0.86    inference(unit_resulting_resolution,[],[f100,f105,f383])).
% 3.84/0.86  fof(f383,plain,(
% 3.84/0.86    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_36),
% 3.84/0.86    inference(avatar_component_clause,[],[f382])).
% 3.84/0.86  fof(f644,plain,(
% 3.84/0.86    spl2_52 | ~spl2_2 | ~spl2_3 | ~spl2_35),
% 3.84/0.86    inference(avatar_split_clause,[],[f374,f355,f103,f98,f641])).
% 3.84/0.86  fof(f355,plain,(
% 3.84/0.86    spl2_35 <=> ! [X1,X0] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 3.84/0.86  fof(f374,plain,(
% 3.84/0.86    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_3 | ~spl2_35)),
% 3.84/0.86    inference(unit_resulting_resolution,[],[f100,f105,f356])).
% 3.84/0.86  fof(f356,plain,(
% 3.84/0.86    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_35),
% 3.84/0.86    inference(avatar_component_clause,[],[f355])).
% 3.84/0.86  fof(f595,plain,(
% 3.84/0.86    spl2_46 | ~spl2_3 | ~spl2_28),
% 3.84/0.86    inference(avatar_split_clause,[],[f315,f248,f103,f593])).
% 3.84/0.86  fof(f315,plain,(
% 3.84/0.86    ( ! [X0] : (k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) ) | (~spl2_3 | ~spl2_28)),
% 3.84/0.86    inference(unit_resulting_resolution,[],[f105,f249])).
% 3.84/0.86  fof(f582,plain,(
% 3.84/0.86    ~spl2_44 | ~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_41),
% 3.84/0.86    inference(avatar_split_clause,[],[f507,f455,f108,f103,f98,f93,f579])).
% 3.84/0.86  fof(f93,plain,(
% 3.84/0.86    spl2_1 <=> v2_pre_topc(sK0)),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 3.84/0.86  fof(f455,plain,(
% 3.84/0.86    spl2_41 <=> ! [X0,X2] : (v3_pre_topc(X2,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X2) != X2)),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).
% 3.84/0.86  fof(f507,plain,(
% 3.84/0.86    sK1 != k1_tops_1(sK0,sK1) | (~spl2_1 | ~spl2_2 | ~spl2_3 | spl2_4 | ~spl2_41)),
% 3.84/0.86    inference(unit_resulting_resolution,[],[f100,f95,f109,f105,f456])).
% 3.84/0.86  fof(f456,plain,(
% 3.84/0.86    ( ! [X2,X0] : (k1_tops_1(X0,X2) != X2 | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X2,X0)) ) | ~spl2_41),
% 3.84/0.86    inference(avatar_component_clause,[],[f455])).
% 3.84/0.86  fof(f109,plain,(
% 3.84/0.86    ~v3_pre_topc(sK1,sK0) | spl2_4),
% 3.84/0.86    inference(avatar_component_clause,[],[f108])).
% 3.84/0.86  fof(f95,plain,(
% 3.84/0.86    v2_pre_topc(sK0) | ~spl2_1),
% 3.84/0.86    inference(avatar_component_clause,[],[f93])).
% 3.84/0.86  fof(f512,plain,(
% 3.84/0.86    spl2_42 | ~spl2_2 | ~spl2_3 | ~spl2_30),
% 3.84/0.86    inference(avatar_split_clause,[],[f326,f319,f103,f98,f509])).
% 3.84/0.86  fof(f319,plain,(
% 3.84/0.86    spl2_30 <=> ! [X1,X0] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 3.84/0.86  fof(f326,plain,(
% 3.84/0.86    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_3 | ~spl2_30)),
% 3.84/0.86    inference(unit_resulting_resolution,[],[f100,f105,f320])).
% 3.84/0.86  fof(f320,plain,(
% 3.84/0.86    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) ) | ~spl2_30),
% 3.84/0.86    inference(avatar_component_clause,[],[f319])).
% 3.84/0.86  fof(f475,plain,(
% 3.84/0.86    ~spl2_2 | ~spl2_3 | ~spl2_40),
% 3.84/0.86    inference(avatar_contradiction_clause,[],[f472])).
% 3.84/0.86  fof(f472,plain,(
% 3.84/0.86    $false | (~spl2_2 | ~spl2_3 | ~spl2_40)),
% 3.84/0.86    inference(subsumption_resolution,[],[f105,f460])).
% 3.84/0.86  fof(f460,plain,(
% 3.84/0.86    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl2_2 | ~spl2_40)),
% 3.84/0.86    inference(unit_resulting_resolution,[],[f100,f453])).
% 3.84/0.86  fof(f453,plain,(
% 3.84/0.86    ( ! [X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1)) ) | ~spl2_40),
% 3.84/0.86    inference(avatar_component_clause,[],[f452])).
% 3.84/0.86  fof(f452,plain,(
% 3.84/0.86    spl2_40 <=> ! [X1,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).
% 3.84/0.86  fof(f457,plain,(
% 3.84/0.86    spl2_40 | spl2_41),
% 3.84/0.86    inference(avatar_split_clause,[],[f69,f455,f452])).
% 3.84/0.86  fof(f69,plain,(
% 3.84/0.86    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.84/0.86    inference(cnf_transformation,[],[f37])).
% 3.84/0.86  fof(f37,plain,(
% 3.84/0.86    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.84/0.86    inference(flattening,[],[f36])).
% 3.84/0.86  fof(f36,plain,(
% 3.84/0.86    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.84/0.86    inference(ennf_transformation,[],[f23])).
% 3.84/0.86  fof(f23,axiom,(
% 3.84/0.86    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 3.84/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_1)).
% 3.84/0.86  fof(f422,plain,(
% 3.84/0.86    ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_37),
% 3.84/0.86    inference(avatar_contradiction_clause,[],[f418])).
% 3.84/0.86  fof(f418,plain,(
% 3.84/0.86    $false | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_37)),
% 3.84/0.86    inference(subsumption_resolution,[],[f105,f400])).
% 3.84/0.86  fof(f400,plain,(
% 3.84/0.86    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl2_1 | ~spl2_2 | ~spl2_37)),
% 3.84/0.86    inference(unit_resulting_resolution,[],[f100,f95,f390])).
% 3.84/0.86  fof(f390,plain,(
% 3.84/0.86    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) ) | ~spl2_37),
% 3.84/0.86    inference(avatar_component_clause,[],[f389])).
% 3.84/0.86  fof(f389,plain,(
% 3.84/0.86    spl2_37 <=> ! [X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0))),
% 3.84/0.86    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 3.84/0.86  fof(f394,plain,(
% 3.84/0.86    spl2_37 | spl2_38),
% 3.84/0.86    inference(avatar_split_clause,[],[f68,f392,f389])).
% 3.84/0.86  fof(f68,plain,(
% 3.84/0.86    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.84/0.86    inference(cnf_transformation,[],[f37])).
% 3.84/0.86  fof(f384,plain,(
% 3.84/0.86    spl2_36),
% 3.84/0.86    inference(avatar_split_clause,[],[f67,f382])).
% 3.84/0.86  fof(f67,plain,(
% 3.84/0.86    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.84/0.86    inference(cnf_transformation,[],[f35])).
% 3.84/0.86  fof(f35,plain,(
% 3.84/0.86    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.84/0.86    inference(ennf_transformation,[],[f22])).
% 3.84/0.86  fof(f22,axiom,(
% 3.84/0.86    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 3.84/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 3.84/0.86  fof(f357,plain,(
% 3.84/0.86    spl2_35),
% 3.84/0.86    inference(avatar_split_clause,[],[f66,f355])).
% 3.84/0.86  fof(f66,plain,(
% 3.84/0.86    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.84/0.86    inference(cnf_transformation,[],[f34])).
% 3.84/0.86  fof(f34,plain,(
% 3.84/0.86    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.84/0.86    inference(ennf_transformation,[],[f26])).
% 3.84/0.86  fof(f26,axiom,(
% 3.84/0.86    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 3.84/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 3.84/0.86  fof(f353,plain,(
% 3.84/0.86    spl2_34),
% 3.84/0.86    inference(avatar_split_clause,[],[f65,f351])).
% 3.84/0.86  fof(f65,plain,(
% 3.84/0.86    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.84/0.86    inference(cnf_transformation,[],[f33])).
% 3.84/0.86  fof(f33,plain,(
% 3.84/0.86    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.84/0.86    inference(ennf_transformation,[],[f25])).
% 3.84/0.86  fof(f25,axiom,(
% 3.84/0.86    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 3.84/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 3.84/0.86  fof(f331,plain,(
% 3.84/0.86    spl2_32),
% 3.84/0.86    inference(avatar_split_clause,[],[f91,f329])).
% 3.84/0.86  fof(f91,plain,(
% 3.84/0.86    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.84/0.86    inference(cnf_transformation,[],[f48])).
% 3.84/0.86  fof(f48,plain,(
% 3.84/0.86    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.84/0.86    inference(flattening,[],[f47])).
% 3.84/0.86  fof(f47,plain,(
% 3.84/0.86    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.84/0.86    inference(ennf_transformation,[],[f17])).
% 3.84/0.86  fof(f17,axiom,(
% 3.84/0.86    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.84/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 3.84/0.86  fof(f325,plain,(
% 3.84/0.86    spl2_31),
% 3.84/0.86    inference(avatar_split_clause,[],[f90,f323])).
% 3.84/0.86  fof(f90,plain,(
% 3.84/0.86    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.84/0.86    inference(cnf_transformation,[],[f46])).
% 3.84/0.86  fof(f46,plain,(
% 3.84/0.86    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.84/0.86    inference(flattening,[],[f45])).
% 3.84/0.86  fof(f45,plain,(
% 3.84/0.86    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.84/0.86    inference(ennf_transformation,[],[f15])).
% 3.84/0.86  fof(f15,axiom,(
% 3.84/0.86    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.84/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 3.84/0.86  fof(f321,plain,(
% 3.84/0.86    spl2_30),
% 3.84/0.86    inference(avatar_split_clause,[],[f79,f319])).
% 3.84/0.86  fof(f79,plain,(
% 3.84/0.86    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.84/0.86    inference(cnf_transformation,[],[f43])).
% 3.84/0.86  fof(f43,plain,(
% 3.84/0.86    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.84/0.86    inference(flattening,[],[f42])).
% 3.84/0.87  fof(f42,plain,(
% 3.84/0.87    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.84/0.87    inference(ennf_transformation,[],[f21])).
% 3.84/0.87  fof(f21,axiom,(
% 3.84/0.87    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.84/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 3.84/0.87  fof(f314,plain,(
% 3.84/0.87    spl2_29 | ~spl2_19 | ~spl2_21),
% 3.84/0.87    inference(avatar_split_clause,[],[f238,f196,f172,f311])).
% 3.84/0.87  fof(f238,plain,(
% 3.84/0.87    k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0)) | (~spl2_19 | ~spl2_21)),
% 3.84/0.87    inference(unit_resulting_resolution,[],[f198,f173])).
% 3.84/0.87  fof(f250,plain,(
% 3.84/0.87    spl2_28),
% 3.84/0.87    inference(avatar_split_clause,[],[f89,f248])).
% 3.84/0.87  fof(f89,plain,(
% 3.84/0.87    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.84/0.87    inference(cnf_transformation,[],[f44])).
% 3.84/0.87  fof(f44,plain,(
% 3.84/0.87    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.84/0.87    inference(ennf_transformation,[],[f18])).
% 3.84/0.87  fof(f18,axiom,(
% 3.84/0.87    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.84/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 3.84/0.87  fof(f244,plain,(
% 3.84/0.87    spl2_27),
% 3.84/0.87    inference(avatar_split_clause,[],[f88,f242])).
% 3.84/0.87  fof(f88,plain,(
% 3.84/0.87    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 3.84/0.87    inference(cnf_transformation,[],[f9])).
% 3.84/0.87  fof(f9,axiom,(
% 3.84/0.87    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 3.84/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 3.84/0.87  fof(f233,plain,(
% 3.84/0.87    spl2_25),
% 3.84/0.87    inference(avatar_split_clause,[],[f86,f231])).
% 3.84/0.87  fof(f86,plain,(
% 3.84/0.87    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 3.84/0.87    inference(cnf_transformation,[],[f10])).
% 3.84/0.87  fof(f10,axiom,(
% 3.84/0.87    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 3.84/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 3.84/0.87  fof(f229,plain,(
% 3.84/0.87    spl2_24),
% 3.84/0.87    inference(avatar_split_clause,[],[f78,f227])).
% 3.84/0.87  fof(f78,plain,(
% 3.84/0.87    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.84/0.87    inference(cnf_transformation,[],[f41])).
% 3.84/0.87  fof(f41,plain,(
% 3.84/0.87    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.84/0.87    inference(ennf_transformation,[],[f16])).
% 3.84/0.87  fof(f16,axiom,(
% 3.84/0.87    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.84/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 3.84/0.87  fof(f225,plain,(
% 3.84/0.87    spl2_23),
% 3.84/0.87    inference(avatar_split_clause,[],[f77,f223])).
% 3.84/0.87  fof(f77,plain,(
% 3.84/0.87    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.84/0.87    inference(cnf_transformation,[],[f40])).
% 3.84/0.87  fof(f40,plain,(
% 3.84/0.87    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.84/0.87    inference(ennf_transformation,[],[f13])).
% 3.84/0.87  fof(f13,axiom,(
% 3.84/0.87    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.84/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 3.84/0.87  fof(f199,plain,(
% 3.84/0.87    spl2_21 | ~spl2_3 | ~spl2_12),
% 3.84/0.87    inference(avatar_split_clause,[],[f175,f144,f103,f196])).
% 3.84/0.87  fof(f144,plain,(
% 3.84/0.87    spl2_12 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 3.84/0.87    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 3.84/0.87  fof(f175,plain,(
% 3.84/0.87    r1_tarski(sK1,u1_struct_0(sK0)) | (~spl2_3 | ~spl2_12)),
% 3.84/0.87    inference(unit_resulting_resolution,[],[f105,f145])).
% 3.84/0.87  fof(f145,plain,(
% 3.84/0.87    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl2_12),
% 3.84/0.87    inference(avatar_component_clause,[],[f144])).
% 3.84/0.87  fof(f174,plain,(
% 3.84/0.87    spl2_19),
% 3.84/0.87    inference(avatar_split_clause,[],[f85,f172])).
% 3.84/0.87  fof(f85,plain,(
% 3.84/0.87    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 3.84/0.87    inference(cnf_transformation,[],[f56])).
% 3.84/0.87  fof(f56,plain,(
% 3.84/0.87    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.84/0.87    inference(nnf_transformation,[],[f2])).
% 3.84/0.87  fof(f2,axiom,(
% 3.84/0.87    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.84/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 3.84/0.87  fof(f170,plain,(
% 3.84/0.87    spl2_18),
% 3.84/0.87    inference(avatar_split_clause,[],[f84,f168])).
% 3.84/0.87  fof(f84,plain,(
% 3.84/0.87    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 3.84/0.87    inference(cnf_transformation,[],[f56])).
% 3.84/0.87  fof(f166,plain,(
% 3.84/0.87    spl2_17),
% 3.84/0.87    inference(avatar_split_clause,[],[f81,f164])).
% 3.84/0.87  fof(f81,plain,(
% 3.84/0.87    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 3.84/0.87    inference(cnf_transformation,[],[f54])).
% 3.84/0.87  fof(f54,plain,(
% 3.84/0.87    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.84/0.87    inference(nnf_transformation,[],[f11])).
% 3.84/0.87  fof(f11,axiom,(
% 3.84/0.87    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.84/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 3.84/0.87  fof(f162,plain,(
% 3.84/0.87    spl2_16),
% 3.84/0.87    inference(avatar_split_clause,[],[f80,f160])).
% 3.84/0.87  fof(f80,plain,(
% 3.84/0.87    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.84/0.87    inference(cnf_transformation,[],[f54])).
% 3.84/0.87  fof(f158,plain,(
% 3.84/0.87    spl2_15),
% 3.84/0.87    inference(avatar_split_clause,[],[f75,f156])).
% 3.84/0.87  fof(f75,plain,(
% 3.84/0.87    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.84/0.87    inference(cnf_transformation,[],[f38])).
% 3.84/0.87  fof(f38,plain,(
% 3.84/0.87    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.84/0.87    inference(ennf_transformation,[],[f5])).
% 3.84/0.87  fof(f5,axiom,(
% 3.84/0.87    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.84/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 3.84/0.87  fof(f154,plain,(
% 3.84/0.87    spl2_14),
% 3.84/0.87    inference(avatar_split_clause,[],[f73,f152])).
% 3.84/0.87  fof(f73,plain,(
% 3.84/0.87    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.84/0.87    inference(cnf_transformation,[],[f19])).
% 3.84/0.87  fof(f19,axiom,(
% 3.84/0.87    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.84/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 3.84/0.87  fof(f150,plain,(
% 3.84/0.87    spl2_13),
% 3.84/0.87    inference(avatar_split_clause,[],[f83,f148])).
% 3.84/0.87  fof(f83,plain,(
% 3.84/0.87    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.84/0.87    inference(cnf_transformation,[],[f55])).
% 3.84/0.87  fof(f55,plain,(
% 3.84/0.87    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.84/0.87    inference(nnf_transformation,[],[f20])).
% 3.84/0.87  fof(f20,axiom,(
% 3.84/0.87    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.84/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 3.84/0.87  fof(f146,plain,(
% 3.84/0.87    spl2_12),
% 3.84/0.87    inference(avatar_split_clause,[],[f82,f144])).
% 3.84/0.87  fof(f82,plain,(
% 3.84/0.87    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.84/0.87    inference(cnf_transformation,[],[f55])).
% 3.84/0.87  fof(f142,plain,(
% 3.84/0.87    spl2_11 | ~spl2_7 | ~spl2_9),
% 3.84/0.87    inference(avatar_split_clause,[],[f134,f131,f123,f140])).
% 3.84/0.87  fof(f123,plain,(
% 3.84/0.87    spl2_7 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.84/0.87    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 3.84/0.87  fof(f134,plain,(
% 3.84/0.87    ( ! [X0] : (r1_tarski(X0,X0)) ) | (~spl2_7 | ~spl2_9)),
% 3.84/0.87    inference(superposition,[],[f132,f124])).
% 3.84/0.87  fof(f124,plain,(
% 3.84/0.87    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_7),
% 3.84/0.87    inference(avatar_component_clause,[],[f123])).
% 3.84/0.87  fof(f138,plain,(
% 3.84/0.87    spl2_10),
% 3.84/0.87    inference(avatar_split_clause,[],[f72,f136])).
% 3.84/0.87  fof(f72,plain,(
% 3.84/0.87    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.84/0.87    inference(cnf_transformation,[],[f12])).
% 3.84/0.87  fof(f12,axiom,(
% 3.84/0.87    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.84/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 3.84/0.87  fof(f133,plain,(
% 3.84/0.87    spl2_9),
% 3.84/0.87    inference(avatar_split_clause,[],[f71,f131])).
% 3.84/0.87  fof(f71,plain,(
% 3.84/0.87    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.84/0.87    inference(cnf_transformation,[],[f7])).
% 3.84/0.87  fof(f7,axiom,(
% 3.84/0.87    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.84/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 3.84/0.87  fof(f129,plain,(
% 3.84/0.87    spl2_8),
% 3.84/0.87    inference(avatar_split_clause,[],[f70,f127])).
% 3.84/0.87  fof(f70,plain,(
% 3.84/0.87    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.84/0.87    inference(cnf_transformation,[],[f29])).
% 3.84/0.87  fof(f29,plain,(
% 3.84/0.87    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.84/0.87    inference(rectify,[],[f1])).
% 3.84/0.87  fof(f1,axiom,(
% 3.84/0.87    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.84/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 3.84/0.87  fof(f125,plain,(
% 3.84/0.87    spl2_7),
% 3.84/0.87    inference(avatar_split_clause,[],[f63,f123])).
% 3.84/0.87  fof(f63,plain,(
% 3.84/0.87    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.84/0.87    inference(cnf_transformation,[],[f8])).
% 3.84/0.87  fof(f8,axiom,(
% 3.84/0.87    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.84/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 3.84/0.87  fof(f121,plain,(
% 3.84/0.87    spl2_6),
% 3.84/0.87    inference(avatar_split_clause,[],[f62,f119])).
% 3.84/0.87  fof(f62,plain,(
% 3.84/0.87    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 3.84/0.87    inference(cnf_transformation,[],[f6])).
% 3.84/0.87  fof(f6,axiom,(
% 3.84/0.87    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 3.84/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 3.84/0.87  fof(f117,plain,(
% 3.84/0.87    ~spl2_4 | ~spl2_5),
% 3.84/0.87    inference(avatar_split_clause,[],[f116,f112,f108])).
% 3.84/0.87  fof(f116,plain,(
% 3.84/0.87    ~v3_pre_topc(sK1,sK0) | ~spl2_5),
% 3.84/0.87    inference(subsumption_resolution,[],[f61,f114])).
% 3.84/0.87  fof(f61,plain,(
% 3.84/0.87    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 3.84/0.87    inference(cnf_transformation,[],[f53])).
% 3.84/0.87  fof(f53,plain,(
% 3.84/0.87    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.84/0.87    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f50,f52,f51])).
% 3.84/0.87  fof(f51,plain,(
% 3.84/0.87    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.84/0.87    introduced(choice_axiom,[])).
% 3.84/0.87  fof(f52,plain,(
% 3.84/0.87    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.84/0.87    introduced(choice_axiom,[])).
% 3.84/0.87  fof(f50,plain,(
% 3.84/0.87    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.84/0.87    inference(flattening,[],[f49])).
% 3.84/0.87  fof(f49,plain,(
% 3.84/0.87    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.84/0.87    inference(nnf_transformation,[],[f31])).
% 3.84/0.87  fof(f31,plain,(
% 3.84/0.87    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.84/0.87    inference(flattening,[],[f30])).
% 3.84/0.87  fof(f30,plain,(
% 3.84/0.87    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.84/0.87    inference(ennf_transformation,[],[f28])).
% 3.84/0.87  fof(f28,negated_conjecture,(
% 3.84/0.87    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 3.84/0.87    inference(negated_conjecture,[],[f27])).
% 3.84/0.87  fof(f27,conjecture,(
% 3.84/0.87    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 3.84/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 3.84/0.87  fof(f115,plain,(
% 3.84/0.87    spl2_4 | spl2_5),
% 3.84/0.87    inference(avatar_split_clause,[],[f60,f112,f108])).
% 3.84/0.87  fof(f60,plain,(
% 3.84/0.87    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 3.84/0.87    inference(cnf_transformation,[],[f53])).
% 3.84/0.87  fof(f106,plain,(
% 3.84/0.87    spl2_3),
% 3.84/0.87    inference(avatar_split_clause,[],[f59,f103])).
% 3.84/0.87  fof(f59,plain,(
% 3.84/0.87    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.84/0.87    inference(cnf_transformation,[],[f53])).
% 3.84/0.87  fof(f101,plain,(
% 3.84/0.87    spl2_2),
% 3.84/0.87    inference(avatar_split_clause,[],[f58,f98])).
% 3.84/0.87  fof(f58,plain,(
% 3.84/0.87    l1_pre_topc(sK0)),
% 3.84/0.87    inference(cnf_transformation,[],[f53])).
% 3.84/0.87  fof(f96,plain,(
% 3.84/0.87    spl2_1),
% 3.84/0.87    inference(avatar_split_clause,[],[f57,f93])).
% 3.84/0.87  fof(f57,plain,(
% 3.84/0.87    v2_pre_topc(sK0)),
% 3.84/0.87    inference(cnf_transformation,[],[f53])).
% 3.84/0.87  % SZS output end Proof for theBenchmark
% 3.84/0.87  % (17331)------------------------------
% 3.84/0.87  % (17331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.84/0.87  % (17331)Termination reason: Refutation
% 3.84/0.87  
% 3.84/0.87  % (17331)Memory used [KB]: 13048
% 3.84/0.87  % (17331)Time elapsed: 0.437 s
% 3.84/0.87  % (17331)------------------------------
% 3.84/0.87  % (17331)------------------------------
% 3.84/0.87  % (17325)Success in time 0.507 s
%------------------------------------------------------------------------------
