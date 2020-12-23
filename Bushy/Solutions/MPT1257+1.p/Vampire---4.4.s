%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_1__t73_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:31 EDT 2019

% Result     : Theorem 1.75s
% Output     : Refutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :  518 (3191 expanded)
%              Number of leaves         :  136 (1192 expanded)
%              Depth                    :   13
%              Number of atoms          : 1259 (6189 expanded)
%              Number of equality atoms :  199 (1255 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f66537,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f133,f140,f147,f154,f167,f185,f204,f218,f239,f249,f258,f272,f296,f304,f336,f426,f634,f654,f674,f702,f723,f782,f804,f826,f868,f936,f2451,f2461,f2468,f2583,f2610,f2665,f2943,f3673,f3832,f4166,f4173,f4515,f4697,f5064,f5071,f5078,f7389,f8675,f8747,f9803,f10084,f10091,f10098,f10658,f10665,f10672,f11244,f11251,f11345,f11352,f11359,f14635,f14848,f14855,f14862,f15093,f15100,f15107,f15231,f19698,f19705,f19712,f19719,f19726,f19733,f19740,f19747,f21822,f23419,f28304,f28760,f28772,f28779,f28786,f30149,f31988,f31995,f32002,f32009,f32016,f32032,f32039,f32070,f32077,f32084,f32091,f32098,f34540,f34547,f34554,f34561,f34568,f34575,f34582,f34589,f34596,f34603,f66517,f66524,f66534,f66536])).

fof(f66536,plain,
    ( spl4_13
    | ~ spl4_208 ),
    inference(avatar_contradiction_clause,[],[f66535])).

fof(f66535,plain,
    ( $false
    | ~ spl4_13
    | ~ spl4_208 ),
    inference(subsumption_resolution,[],[f66532,f203])).

fof(f203,plain,
    ( ~ r1_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl4_13
  <=> ~ r1_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f66532,plain,
    ( r1_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl4_208 ),
    inference(superposition,[],[f102,f66523])).

fof(f66523,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl4_208 ),
    inference(avatar_component_clause,[],[f66522])).

fof(f66522,plain,
    ( spl4_208
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_208])])).

fof(f102,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t73_tops_1.p',t79_xboole_1)).

fof(f66534,plain,
    ( spl4_11
    | ~ spl4_208 ),
    inference(avatar_contradiction_clause,[],[f66533])).

fof(f66533,plain,
    ( $false
    | ~ spl4_11
    | ~ spl4_208 ),
    inference(subsumption_resolution,[],[f66531,f184])).

fof(f184,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl4_11
  <=> ~ r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f66531,plain,
    ( r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl4_208 ),
    inference(superposition,[],[f173,f66523])).

fof(f173,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(unit_resulting_resolution,[],[f102,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t73_tops_1.p',symmetry_r1_xboole_0)).

fof(f66524,plain,
    ( spl4_208
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_32
    | ~ spl4_38
    | ~ spl4_134
    | ~ spl4_140 ),
    inference(avatar_split_clause,[],[f21798,f19731,f19710,f700,f632,f152,f131,f66522])).

fof(f131,plain,
    ( spl4_0
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f152,plain,
    ( spl4_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f632,plain,
    ( spl4_32
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f700,plain,
    ( spl4_38
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f19710,plain,
    ( spl4_134
  <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_134])])).

fof(f19731,plain,
    ( spl4_140
  <=> k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_140])])).

fof(f21798,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_32
    | ~ spl4_38
    | ~ spl4_134
    | ~ spl4_140 ),
    inference(backward_demodulation,[],[f21623,f2422])).

fof(f2422,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl4_32
    | ~ spl4_38 ),
    inference(forward_demodulation,[],[f1085,f710])).

fof(f710,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X0) = k4_xboole_0(k2_pre_topc(sK0,sK1),X0)
    | ~ spl4_38 ),
    inference(unit_resulting_resolution,[],[f701,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t73_tops_1.p',redefinition_k7_subset_1)).

fof(f701,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f700])).

fof(f1085,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl4_32
    | ~ spl4_38 ),
    inference(unit_resulting_resolution,[],[f701,f633,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k9_subset_1(X0,X1,k3_subset_1(X0,X2)) = k7_subset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t73_tops_1.p',t32_subset_1)).

fof(f633,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f632])).

fof(f21623,plain,
    ( k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)))
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_134
    | ~ spl4_140 ),
    inference(backward_demodulation,[],[f21621,f2643])).

fof(f2643,plain,
    ( k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_0
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f132,f153,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t73_tops_1.p',d2_tops_1)).

fof(f153,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f152])).

fof(f132,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f131])).

fof(f21621,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_134
    | ~ spl4_140 ),
    inference(forward_demodulation,[],[f21025,f19732])).

fof(f19732,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_140 ),
    inference(avatar_component_clause,[],[f19731])).

fof(f21025,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_134 ),
    inference(unit_resulting_resolution,[],[f19711,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t73_tops_1.p',involutiveness_k3_subset_1)).

fof(f19711,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_134 ),
    inference(avatar_component_clause,[],[f19710])).

fof(f66517,plain,
    ( spl4_206
    | ~ spl4_6
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f1696,f302,f152,f66515])).

fof(f66515,plain,
    ( spl4_206
  <=> k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_206])])).

fof(f302,plain,
    ( spl4_26
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f1696,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK1)
    | ~ spl4_6
    | ~ spl4_26 ),
    inference(forward_demodulation,[],[f1695,f265])).

fof(f265,plain,(
    ! [X0,X1] : k9_subset_1(X0,X1,X1) = X1 ),
    inference(unit_resulting_resolution,[],[f100,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t73_tops_1.p',idempotence_k9_subset_1)).

fof(f100,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f86])).

fof(f86,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f25,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t73_tops_1.p',existence_m1_subset_1)).

fof(f1695,plain,
    ( k9_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k4_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK1)
    | ~ spl4_6
    | ~ spl4_26 ),
    inference(forward_demodulation,[],[f1608,f449])).

fof(f449,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0) = k4_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),X0)
    | ~ spl4_26 ),
    inference(unit_resulting_resolution,[],[f303,f122])).

fof(f303,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f302])).

fof(f1608,plain,
    ( k9_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),sK1)
    | ~ spl4_6
    | ~ spl4_26 ),
    inference(unit_resulting_resolution,[],[f303,f153,f110])).

fof(f34603,plain,
    ( spl4_204
    | ~ spl4_2
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f2014,f672,f138,f34601])).

fof(f34601,plain,
    ( spl4_204
  <=> o_0_0_xboole_0 = k4_xboole_0(k1_tops_1(sK3,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK3),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_204])])).

fof(f138,plain,
    ( spl4_2
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f672,plain,
    ( spl4_36
  <=> m1_subset_1(k1_tops_1(sK3,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f2014,plain,
    ( o_0_0_xboole_0 = k4_xboole_0(k1_tops_1(sK3,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK3),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f2013,f514])).

fof(f514,plain,
    ( ! [X0,X1] : k9_subset_1(X1,X0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f510,f158])).

fof(f158,plain,
    ( ! [X0] : k3_xboole_0(X0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f155,f96])).

fof(f96,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t73_tops_1.p',t2_boole)).

fof(f155,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f139,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t73_tops_1.p',t6_boole)).

fof(f139,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f138])).

fof(f510,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,o_0_0_xboole_0) = k9_subset_1(X1,X0,o_0_0_xboole_0)
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f500,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t73_tops_1.p',redefinition_k9_subset_1)).

fof(f500,plain,
    ( ! [X5] : m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X5))
    | ~ spl4_2 ),
    inference(superposition,[],[f404,f188])).

fof(f188,plain,
    ( ! [X1] : k3_xboole_0(o_0_0_xboole_0,X1) = o_0_0_xboole_0
    | ~ spl4_2 ),
    inference(superposition,[],[f103,f158])).

fof(f103,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t73_tops_1.p',commutativity_k3_xboole_0)).

fof(f404,plain,(
    ! [X0,X1] : m1_subset_1(k3_xboole_0(X1,sK2(k1_zfmisc_1(X0))),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f397,f363])).

fof(f363,plain,(
    ! [X0,X1] : m1_subset_1(k9_subset_1(X0,X1,sK2(k1_zfmisc_1(X0))),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f100,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t73_tops_1.p',dt_k9_subset_1)).

fof(f397,plain,(
    ! [X0,X1] : k3_xboole_0(X0,sK2(k1_zfmisc_1(X1))) = k9_subset_1(X1,X0,sK2(k1_zfmisc_1(X1))) ),
    inference(unit_resulting_resolution,[],[f100,f121])).

fof(f2013,plain,
    ( k9_subset_1(u1_struct_0(sK3),k1_tops_1(sK3,o_0_0_xboole_0),o_0_0_xboole_0) = k4_xboole_0(k1_tops_1(sK3,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK3),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f2012,f507])).

fof(f507,plain,
    ( ! [X0] : k3_subset_1(X0,k3_subset_1(X0,o_0_0_xboole_0)) = o_0_0_xboole_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f500,f109])).

fof(f2012,plain,
    ( k9_subset_1(u1_struct_0(sK3),k1_tops_1(sK3,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),o_0_0_xboole_0))) = k4_xboole_0(k1_tops_1(sK3,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK3),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f1384,f745])).

fof(f745,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK3),k1_tops_1(sK3,o_0_0_xboole_0),X0) = k4_xboole_0(k1_tops_1(sK3,o_0_0_xboole_0),X0)
    | ~ spl4_36 ),
    inference(unit_resulting_resolution,[],[f673,f122])).

fof(f673,plain,
    ( m1_subset_1(k1_tops_1(sK3,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f672])).

fof(f1384,plain,
    ( k9_subset_1(u1_struct_0(sK3),k1_tops_1(sK3,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),o_0_0_xboole_0))) = k7_subset_1(u1_struct_0(sK3),k1_tops_1(sK3,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK3),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_36 ),
    inference(unit_resulting_resolution,[],[f673,f506,f110])).

fof(f506,plain,
    ( ! [X0] : m1_subset_1(k3_subset_1(X0,o_0_0_xboole_0),k1_zfmisc_1(X0))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f500,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t73_tops_1.p',dt_k3_subset_1)).

fof(f34596,plain,
    ( spl4_202
    | ~ spl4_2
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f2005,f866,f138,f34594])).

fof(f34594,plain,
    ( spl4_202
  <=> o_0_0_xboole_0 = k4_xboole_0(k2_tops_1(sK3,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK3),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_202])])).

fof(f866,plain,
    ( spl4_48
  <=> m1_subset_1(k2_tops_1(sK3,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f2005,plain,
    ( o_0_0_xboole_0 = k4_xboole_0(k2_tops_1(sK3,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK3),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_48 ),
    inference(forward_demodulation,[],[f2004,f514])).

fof(f2004,plain,
    ( k9_subset_1(u1_struct_0(sK3),k2_tops_1(sK3,o_0_0_xboole_0),o_0_0_xboole_0) = k4_xboole_0(k2_tops_1(sK3,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK3),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_48 ),
    inference(forward_demodulation,[],[f2003,f507])).

fof(f2003,plain,
    ( k9_subset_1(u1_struct_0(sK3),k2_tops_1(sK3,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),o_0_0_xboole_0))) = k4_xboole_0(k2_tops_1(sK3,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK3),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_48 ),
    inference(forward_demodulation,[],[f1387,f894])).

fof(f894,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK3),k2_tops_1(sK3,o_0_0_xboole_0),X0) = k4_xboole_0(k2_tops_1(sK3,o_0_0_xboole_0),X0)
    | ~ spl4_48 ),
    inference(unit_resulting_resolution,[],[f867,f122])).

fof(f867,plain,
    ( m1_subset_1(k2_tops_1(sK3,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f866])).

fof(f1387,plain,
    ( k9_subset_1(u1_struct_0(sK3),k2_tops_1(sK3,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),o_0_0_xboole_0))) = k7_subset_1(u1_struct_0(sK3),k2_tops_1(sK3,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK3),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_48 ),
    inference(unit_resulting_resolution,[],[f867,f506,f110])).

fof(f34589,plain,
    ( spl4_200
    | ~ spl4_2
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f1969,f824,f138,f34587])).

fof(f34587,plain,
    ( spl4_200
  <=> o_0_0_xboole_0 = k4_xboole_0(k2_pre_topc(sK3,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK3),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_200])])).

fof(f824,plain,
    ( spl4_46
  <=> m1_subset_1(k2_pre_topc(sK3,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f1969,plain,
    ( o_0_0_xboole_0 = k4_xboole_0(k2_pre_topc(sK3,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK3),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_46 ),
    inference(forward_demodulation,[],[f1968,f514])).

fof(f1968,plain,
    ( k9_subset_1(u1_struct_0(sK3),k2_pre_topc(sK3,o_0_0_xboole_0),o_0_0_xboole_0) = k4_xboole_0(k2_pre_topc(sK3,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK3),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_46 ),
    inference(forward_demodulation,[],[f1967,f507])).

fof(f1967,plain,
    ( k9_subset_1(u1_struct_0(sK3),k2_pre_topc(sK3,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),o_0_0_xboole_0))) = k4_xboole_0(k2_pre_topc(sK3,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK3),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_46 ),
    inference(forward_demodulation,[],[f1399,f878])).

fof(f878,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK3),k2_pre_topc(sK3,o_0_0_xboole_0),X0) = k4_xboole_0(k2_pre_topc(sK3,o_0_0_xboole_0),X0)
    | ~ spl4_46 ),
    inference(unit_resulting_resolution,[],[f825,f122])).

fof(f825,plain,
    ( m1_subset_1(k2_pre_topc(sK3,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f824])).

fof(f1399,plain,
    ( k9_subset_1(u1_struct_0(sK3),k2_pre_topc(sK3,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),o_0_0_xboole_0))) = k7_subset_1(u1_struct_0(sK3),k2_pre_topc(sK3,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK3),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_46 ),
    inference(unit_resulting_resolution,[],[f825,f506,f110])).

fof(f34582,plain,
    ( spl4_198
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f1684,f152,f34580])).

fof(f34580,plain,
    ( spl4_198
  <=> k9_subset_1(u1_struct_0(sK0),sK2(k1_zfmisc_1(u1_struct_0(sK0))),k3_subset_1(u1_struct_0(sK0),sK1)) = k4_xboole_0(sK2(k1_zfmisc_1(u1_struct_0(sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_198])])).

fof(f1684,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK2(k1_zfmisc_1(u1_struct_0(sK0))),k3_subset_1(u1_struct_0(sK0),sK1)) = k4_xboole_0(sK2(k1_zfmisc_1(u1_struct_0(sK0))),sK1)
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f1619,f455])).

fof(f455,plain,(
    ! [X0,X1] : k7_subset_1(X0,sK2(k1_zfmisc_1(X0)),X1) = k4_xboole_0(sK2(k1_zfmisc_1(X0)),X1) ),
    inference(unit_resulting_resolution,[],[f100,f122])).

fof(f1619,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK2(k1_zfmisc_1(u1_struct_0(sK0))),k3_subset_1(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),sK2(k1_zfmisc_1(u1_struct_0(sK0))),sK1)
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f100,f153,f110])).

fof(f34575,plain,
    ( spl4_196
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f889,f866,f34573])).

fof(f34573,plain,
    ( spl4_196
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK3),k2_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_196])])).

fof(f889,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),k2_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_48 ),
    inference(unit_resulting_resolution,[],[f867,f108])).

fof(f34568,plain,
    ( spl4_194
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f763,f145,f138,f34566])).

fof(f34566,plain,
    ( spl4_194
  <=> m1_subset_1(k2_tops_1(sK3,k3_subset_1(u1_struct_0(sK3),o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_194])])).

fof(f145,plain,
    ( spl4_4
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f763,plain,
    ( m1_subset_1(k2_tops_1(sK3,k3_subset_1(u1_struct_0(sK3),o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f146,f506,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t73_tops_1.p',dt_k2_tops_1)).

fof(f146,plain,
    ( l1_pre_topc(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f145])).

fof(f34561,plain,
    ( spl4_192
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f740,f672,f34559])).

fof(f34559,plain,
    ( spl4_192
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK3),k1_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_192])])).

fof(f740,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),k1_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_36 ),
    inference(unit_resulting_resolution,[],[f673,f108])).

fof(f34554,plain,
    ( spl4_190
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f685,f145,f138,f34552])).

fof(f34552,plain,
    ( spl4_190
  <=> m1_subset_1(k2_pre_topc(sK3,k3_subset_1(u1_struct_0(sK3),o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_190])])).

fof(f685,plain,
    ( m1_subset_1(k2_pre_topc(sK3,k3_subset_1(u1_struct_0(sK3),o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f146,f506,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t73_tops_1.p',dt_k2_pre_topc)).

fof(f34547,plain,
    ( spl4_188
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f617,f145,f138,f34545])).

fof(f34545,plain,
    ( spl4_188
  <=> m1_subset_1(k1_tops_1(sK3,k3_subset_1(u1_struct_0(sK3),o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_188])])).

fof(f617,plain,
    ( m1_subset_1(k1_tops_1(sK3,k3_subset_1(u1_struct_0(sK3),o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f146,f506,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t73_tops_1.p',dt_k1_tops_1)).

fof(f34540,plain,
    ( spl4_186
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f1658,f152,f34538])).

fof(f34538,plain,
    ( spl4_186
  <=> k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2(k1_zfmisc_1(u1_struct_0(sK0))))) = k4_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_186])])).

fof(f1658,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2(k1_zfmisc_1(u1_struct_0(sK0))))) = k4_xboole_0(sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f1644,f454])).

fof(f454,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f153,f122])).

fof(f1644,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2(k1_zfmisc_1(u1_struct_0(sK0))))) = k7_subset_1(u1_struct_0(sK0),sK1,sK2(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f153,f100,f110])).

fof(f32098,plain,
    ( spl4_184
    | ~ spl4_2
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f2020,f632,f138,f32096])).

fof(f32096,plain,
    ( spl4_184
  <=> o_0_0_xboole_0 = k4_xboole_0(k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_184])])).

fof(f2020,plain,
    ( o_0_0_xboole_0 = k4_xboole_0(k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f2019,f514])).

fof(f2019,plain,
    ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),o_0_0_xboole_0) = k4_xboole_0(k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f2018,f507])).

fof(f2018,plain,
    ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))) = k4_xboole_0(k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_32 ),
    inference(forward_demodulation,[],[f1382,f641])).

fof(f641,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X0) = k4_xboole_0(k1_tops_1(sK0,sK1),X0)
    | ~ spl4_32 ),
    inference(unit_resulting_resolution,[],[f633,f122])).

fof(f1382,plain,
    ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))) = k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_32 ),
    inference(unit_resulting_resolution,[],[f633,f506,f110])).

fof(f32091,plain,
    ( spl4_182
    | ~ spl4_2
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f2017,f652,f138,f32089])).

fof(f32089,plain,
    ( spl4_182
  <=> o_0_0_xboole_0 = k4_xboole_0(k1_tops_1(sK0,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_182])])).

fof(f652,plain,
    ( spl4_34
  <=> m1_subset_1(k1_tops_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f2017,plain,
    ( o_0_0_xboole_0 = k4_xboole_0(k1_tops_1(sK0,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_34 ),
    inference(forward_demodulation,[],[f2016,f514])).

fof(f2016,plain,
    ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0) = k4_xboole_0(k1_tops_1(sK0,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_34 ),
    inference(forward_demodulation,[],[f2015,f507])).

fof(f2015,plain,
    ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))) = k4_xboole_0(k1_tops_1(sK0,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_34 ),
    inference(forward_demodulation,[],[f1383,f661])).

fof(f661,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,o_0_0_xboole_0),X0) = k4_xboole_0(k1_tops_1(sK0,o_0_0_xboole_0),X0)
    | ~ spl4_34 ),
    inference(unit_resulting_resolution,[],[f653,f122])).

fof(f653,plain,
    ( m1_subset_1(k1_tops_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f652])).

fof(f1383,plain,
    ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))) = k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_34 ),
    inference(unit_resulting_resolution,[],[f653,f506,f110])).

fof(f32084,plain,
    ( spl4_180
    | ~ spl4_2
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f2011,f780,f138,f32082])).

fof(f32082,plain,
    ( spl4_180
  <=> o_0_0_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_180])])).

fof(f780,plain,
    ( spl4_42
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f2011,plain,
    ( o_0_0_xboole_0 = k4_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f2010,f514])).

fof(f2010,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),o_0_0_xboole_0) = k4_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f2009,f507])).

fof(f2009,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))) = k4_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f1385,f791])).

fof(f791,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),X0) = k4_xboole_0(k2_tops_1(sK0,sK1),X0)
    | ~ spl4_42 ),
    inference(unit_resulting_resolution,[],[f781,f122])).

fof(f781,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f780])).

fof(f1385,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_42 ),
    inference(unit_resulting_resolution,[],[f781,f506,f110])).

fof(f32077,plain,
    ( spl4_178
    | ~ spl4_2
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f2008,f802,f138,f32075])).

fof(f32075,plain,
    ( spl4_178
  <=> o_0_0_xboole_0 = k4_xboole_0(k2_tops_1(sK0,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_178])])).

fof(f802,plain,
    ( spl4_44
  <=> m1_subset_1(k2_tops_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f2008,plain,
    ( o_0_0_xboole_0 = k4_xboole_0(k2_tops_1(sK0,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_44 ),
    inference(forward_demodulation,[],[f2007,f514])).

fof(f2007,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,o_0_0_xboole_0),o_0_0_xboole_0) = k4_xboole_0(k2_tops_1(sK0,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_44 ),
    inference(forward_demodulation,[],[f2006,f507])).

fof(f2006,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))) = k4_xboole_0(k2_tops_1(sK0,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_44 ),
    inference(forward_demodulation,[],[f1386,f813])).

fof(f813,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,o_0_0_xboole_0),X0) = k4_xboole_0(k2_tops_1(sK0,o_0_0_xboole_0),X0)
    | ~ spl4_44 ),
    inference(unit_resulting_resolution,[],[f803,f122])).

fof(f803,plain,
    ( m1_subset_1(k2_tops_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f802])).

fof(f1386,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))) = k7_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_44 ),
    inference(unit_resulting_resolution,[],[f803,f506,f110])).

fof(f32070,plain,
    ( spl4_176
    | ~ spl4_0
    | ~ spl4_6
    | ~ spl4_134
    | ~ spl4_140 ),
    inference(avatar_split_clause,[],[f21623,f19731,f19710,f152,f131,f32068])).

fof(f32068,plain,
    ( spl4_176
  <=> k2_tops_1(sK0,sK1) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_176])])).

fof(f32039,plain,
    ( spl4_174
    | ~ spl4_2
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f1975,f700,f138,f32037])).

fof(f32037,plain,
    ( spl4_174
  <=> o_0_0_xboole_0 = k4_xboole_0(k2_pre_topc(sK0,sK1),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_174])])).

fof(f1975,plain,
    ( o_0_0_xboole_0 = k4_xboole_0(k2_pre_topc(sK0,sK1),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_38 ),
    inference(forward_demodulation,[],[f1974,f514])).

fof(f1974,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),o_0_0_xboole_0) = k4_xboole_0(k2_pre_topc(sK0,sK1),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_38 ),
    inference(forward_demodulation,[],[f1973,f507])).

fof(f1973,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))) = k4_xboole_0(k2_pre_topc(sK0,sK1),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_38 ),
    inference(forward_demodulation,[],[f1397,f710])).

fof(f1397,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_38 ),
    inference(unit_resulting_resolution,[],[f701,f506,f110])).

fof(f32032,plain,
    ( spl4_172
    | ~ spl4_2
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f1972,f721,f138,f32030])).

fof(f32030,plain,
    ( spl4_172
  <=> o_0_0_xboole_0 = k4_xboole_0(k2_pre_topc(sK0,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_172])])).

fof(f721,plain,
    ( spl4_40
  <=> m1_subset_1(k2_pre_topc(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f1972,plain,
    ( o_0_0_xboole_0 = k4_xboole_0(k2_pre_topc(sK0,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_40 ),
    inference(forward_demodulation,[],[f1971,f514])).

fof(f1971,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,o_0_0_xboole_0),o_0_0_xboole_0) = k4_xboole_0(k2_pre_topc(sK0,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_40 ),
    inference(forward_demodulation,[],[f1970,f507])).

fof(f1970,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))) = k4_xboole_0(k2_pre_topc(sK0,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_40 ),
    inference(forward_demodulation,[],[f1398,f731])).

fof(f731,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,o_0_0_xboole_0),X0) = k4_xboole_0(k2_pre_topc(sK0,o_0_0_xboole_0),X0)
    | ~ spl4_40 ),
    inference(unit_resulting_resolution,[],[f722,f122])).

fof(f722,plain,
    ( m1_subset_1(k2_pre_topc(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f721])).

fof(f1398,plain,
    ( k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,o_0_0_xboole_0),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_40 ),
    inference(unit_resulting_resolution,[],[f722,f506,f110])).

fof(f32016,plain,
    ( spl4_170
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f808,f802,f32014])).

fof(f32014,plain,
    ( spl4_170
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_170])])).

fof(f808,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_44 ),
    inference(unit_resulting_resolution,[],[f803,f108])).

fof(f32009,plain,
    ( spl4_168
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f762,f138,f131,f32007])).

fof(f32007,plain,
    ( spl4_168
  <=> m1_subset_1(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_168])])).

fof(f762,plain,
    ( m1_subset_1(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f132,f506,f113])).

fof(f32002,plain,
    ( spl4_166
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f684,f138,f131,f32000])).

fof(f32000,plain,
    ( spl4_166
  <=> m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_166])])).

fof(f684,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f132,f506,f112])).

fof(f31995,plain,
    ( spl4_164
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f656,f652,f31993])).

fof(f31993,plain,
    ( spl4_164
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_164])])).

fof(f656,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_34 ),
    inference(unit_resulting_resolution,[],[f653,f108])).

fof(f31988,plain,
    ( spl4_162
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f616,f138,f131,f31986])).

fof(f31986,plain,
    ( spl4_162
  <=> m1_subset_1(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_162])])).

fof(f616,plain,
    ( m1_subset_1(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f132,f506,f111])).

fof(f30149,plain,
    ( spl4_160
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f965,f145,f30147])).

fof(f30147,plain,
    ( spl4_160
  <=> k2_pre_topc(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))) = k2_pre_topc(sK3,k2_pre_topc(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_160])])).

fof(f965,plain,
    ( k2_pre_topc(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))) = k2_pre_topc(sK3,k2_pre_topc(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f146,f100,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t73_tops_1.p',projectivity_k2_pre_topc)).

fof(f28786,plain,
    ( spl4_158
    | ~ spl4_2
    | ~ spl4_150 ),
    inference(avatar_split_clause,[],[f28752,f28302,f138,f28784])).

fof(f28784,plain,
    ( spl4_158
  <=> k3_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_158])])).

fof(f28302,plain,
    ( spl4_150
  <=> k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_150])])).

fof(f28752,plain,
    ( k3_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)) = sK1
    | ~ spl4_2
    | ~ spl4_150 ),
    inference(subsumption_resolution,[],[f28745,f506])).

fof(f28745,plain,
    ( k3_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)) = sK1
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_150 ),
    inference(superposition,[],[f28303,f121])).

fof(f28303,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)) = sK1
    | ~ spl4_150 ),
    inference(avatar_component_clause,[],[f28302])).

fof(f28779,plain,
    ( spl4_156
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f851,f145,f28777])).

fof(f28777,plain,
    ( spl4_156
  <=> k1_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))) = k1_tops_1(sK3,k1_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_156])])).

fof(f851,plain,
    ( k1_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))) = k1_tops_1(sK3,k1_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f146,f100,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t73_tops_1.p',projectivity_k1_tops_1)).

fof(f28772,plain,
    ( spl4_154
    | ~ spl4_6
    | ~ spl4_150 ),
    inference(avatar_split_clause,[],[f28743,f28302,f152,f28770])).

fof(f28770,plain,
    ( spl4_154
  <=> k3_xboole_0(k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0),sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_154])])).

fof(f28743,plain,
    ( k3_xboole_0(k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0),sK1) = sK1
    | ~ spl4_6
    | ~ spl4_150 ),
    inference(superposition,[],[f28303,f557])).

fof(f557,plain,
    ( ! [X0] : k3_xboole_0(X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f539,f396])).

fof(f396,plain,
    ( ! [X0] : k3_xboole_0(X0,sK1) = k9_subset_1(u1_struct_0(sK0),X0,sK1)
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f153,f121])).

fof(f539,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f153,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t73_tops_1.p',commutativity_k9_subset_1)).

fof(f28760,plain,
    ( spl4_152
    | ~ spl4_6
    | ~ spl4_30
    | ~ spl4_150 ),
    inference(avatar_split_clause,[],[f28751,f28302,f424,f152,f28758])).

fof(f28758,plain,
    ( spl4_152
  <=> k7_subset_1(u1_struct_0(sK0),sK1,o_0_0_xboole_0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_152])])).

fof(f424,plain,
    ( spl4_30
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f28751,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,o_0_0_xboole_0) = sK1
    | ~ spl4_6
    | ~ spl4_30
    | ~ spl4_150 ),
    inference(subsumption_resolution,[],[f28750,f153])).

fof(f28750,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,o_0_0_xboole_0) = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_30
    | ~ spl4_150 ),
    inference(subsumption_resolution,[],[f28744,f425])).

fof(f425,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f424])).

fof(f28744,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,o_0_0_xboole_0) = sK1
    | ~ m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_150 ),
    inference(superposition,[],[f28303,f110])).

fof(f28304,plain,
    ( spl4_150
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f1784,f152,f138,f28302])).

fof(f1784,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)) = sK1
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f1783,f160])).

fof(f160,plain,
    ( ! [X0] : k4_xboole_0(X0,o_0_0_xboole_0) = X0
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f155,f94])).

fof(f94,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t73_tops_1.p',t3_boole)).

fof(f1783,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)) = k4_xboole_0(sK1,o_0_0_xboole_0)
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f1522,f454])).

fof(f1522,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)) = k7_subset_1(u1_struct_0(sK0),sK1,o_0_0_xboole_0)
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f153,f500,f110])).

fof(f23419,plain,
    ( spl4_148
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f964,f131,f23417])).

fof(f23417,plain,
    ( spl4_148
  <=> k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_148])])).

fof(f964,plain,
    ( k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f132,f100,f115])).

fof(f21822,plain,
    ( spl4_146
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f850,f131,f21820])).

fof(f21820,plain,
    ( spl4_146
  <=> k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))) = k1_tops_1(sK0,k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_146])])).

fof(f850,plain,
    ( k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))) = k1_tops_1(sK0,k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f132,f100,f114])).

fof(f19747,plain,
    ( spl4_144
    | ~ spl4_26
    | ~ spl4_128 ),
    inference(avatar_split_clause,[],[f15620,f15229,f302,f19745])).

fof(f19745,plain,
    ( spl4_144
  <=> k3_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_144])])).

fof(f15229,plain,
    ( spl4_128
  <=> k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_128])])).

fof(f15620,plain,
    ( k3_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_xboole_0(sK1,sK1)
    | ~ spl4_26
    | ~ spl4_128 ),
    inference(subsumption_resolution,[],[f15613,f303])).

fof(f15613,plain,
    ( k3_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_xboole_0(sK1,sK1)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_128 ),
    inference(superposition,[],[f15230,f121])).

fof(f15230,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_xboole_0(sK1,sK1)
    | ~ spl4_128 ),
    inference(avatar_component_clause,[],[f15229])).

fof(f19740,plain,
    ( spl4_142
    | ~ spl4_6
    | ~ spl4_128 ),
    inference(avatar_split_clause,[],[f15611,f15229,f152,f19738])).

fof(f19738,plain,
    ( spl4_142
  <=> k3_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK1) = k4_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_142])])).

fof(f15611,plain,
    ( k3_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK1) = k4_xboole_0(sK1,sK1)
    | ~ spl4_6
    | ~ spl4_128 ),
    inference(superposition,[],[f15230,f557])).

fof(f19733,plain,
    ( spl4_140
    | ~ spl4_0
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f2502,f152,f131,f19731])).

fof(f2502,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_0
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f132,f153,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t73_tops_1.p',d1_tops_1)).

fof(f19726,plain,
    ( spl4_138
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f786,f780,f19724])).

fof(f19724,plain,
    ( spl4_138
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_138])])).

fof(f786,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_42 ),
    inference(unit_resulting_resolution,[],[f781,f108])).

fof(f19719,plain,
    ( spl4_136
    | ~ spl4_0
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f759,f302,f131,f19717])).

fof(f19717,plain,
    ( spl4_136
  <=> m1_subset_1(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_136])])).

fof(f759,plain,
    ( m1_subset_1(k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_26 ),
    inference(unit_resulting_resolution,[],[f132,f303,f113])).

fof(f19712,plain,
    ( spl4_134
    | ~ spl4_0
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f681,f302,f131,f19710])).

fof(f681,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_26 ),
    inference(unit_resulting_resolution,[],[f132,f303,f112])).

fof(f19705,plain,
    ( spl4_132
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f636,f632,f19703])).

fof(f19703,plain,
    ( spl4_132
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_132])])).

fof(f636,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_32 ),
    inference(unit_resulting_resolution,[],[f633,f108])).

fof(f19698,plain,
    ( spl4_130
    | ~ spl4_0
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f613,f302,f131,f19696])).

fof(f19696,plain,
    ( spl4_130
  <=> m1_subset_1(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_130])])).

fof(f613,plain,
    ( m1_subset_1(k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_26 ),
    inference(unit_resulting_resolution,[],[f132,f303,f111])).

fof(f15231,plain,
    ( spl4_128
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f1685,f152,f15229])).

fof(f1685,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_xboole_0(sK1,sK1)
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f1618,f454])).

fof(f1618,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) = k7_subset_1(u1_struct_0(sK0),sK1,sK1)
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f153,f153,f110])).

fof(f15107,plain,
    ( spl4_126
    | ~ spl4_4
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f888,f866,f145,f15105])).

fof(f15105,plain,
    ( spl4_126
  <=> m1_subset_1(k1_tops_1(sK3,k2_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_126])])).

fof(f888,plain,
    ( m1_subset_1(k1_tops_1(sK3,k2_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4
    | ~ spl4_48 ),
    inference(unit_resulting_resolution,[],[f146,f867,f111])).

fof(f15100,plain,
    ( spl4_124
    | ~ spl4_4
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f887,f866,f145,f15098])).

fof(f15098,plain,
    ( spl4_124
  <=> m1_subset_1(k2_pre_topc(sK3,k2_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_124])])).

fof(f887,plain,
    ( m1_subset_1(k2_pre_topc(sK3,k2_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4
    | ~ spl4_48 ),
    inference(unit_resulting_resolution,[],[f146,f867,f112])).

fof(f15093,plain,
    ( spl4_122
    | ~ spl4_4
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f886,f866,f145,f15091])).

fof(f15091,plain,
    ( spl4_122
  <=> m1_subset_1(k2_tops_1(sK3,k2_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_122])])).

fof(f886,plain,
    ( m1_subset_1(k2_tops_1(sK3,k2_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4
    | ~ spl4_48 ),
    inference(unit_resulting_resolution,[],[f146,f867,f113])).

fof(f14862,plain,
    ( spl4_120
    | ~ spl4_4
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f872,f824,f145,f14860])).

fof(f14860,plain,
    ( spl4_120
  <=> m1_subset_1(k1_tops_1(sK3,k2_pre_topc(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_120])])).

fof(f872,plain,
    ( m1_subset_1(k1_tops_1(sK3,k2_pre_topc(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4
    | ~ spl4_46 ),
    inference(unit_resulting_resolution,[],[f146,f825,f111])).

fof(f14855,plain,
    ( spl4_118
    | ~ spl4_4
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f870,f824,f145,f14853])).

fof(f14853,plain,
    ( spl4_118
  <=> m1_subset_1(k2_tops_1(sK3,k2_pre_topc(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_118])])).

fof(f870,plain,
    ( m1_subset_1(k2_tops_1(sK3,k2_pre_topc(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4
    | ~ spl4_46 ),
    inference(unit_resulting_resolution,[],[f146,f825,f113])).

fof(f14848,plain,
    ( spl4_116
    | ~ spl4_4
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f754,f672,f145,f14846])).

fof(f14846,plain,
    ( spl4_116
  <=> m1_subset_1(k2_tops_1(sK3,k1_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_116])])).

fof(f754,plain,
    ( m1_subset_1(k2_tops_1(sK3,k1_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4
    | ~ spl4_36 ),
    inference(unit_resulting_resolution,[],[f146,f673,f113])).

fof(f14635,plain,
    ( spl4_114
    | ~ spl4_4
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f738,f672,f145,f14633])).

fof(f14633,plain,
    ( spl4_114
  <=> m1_subset_1(k2_pre_topc(sK3,k1_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_114])])).

fof(f738,plain,
    ( m1_subset_1(k2_pre_topc(sK3,k1_tops_1(sK3,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4
    | ~ spl4_36 ),
    inference(unit_resulting_resolution,[],[f146,f673,f112])).

fof(f11359,plain,
    ( spl4_112
    | ~ spl4_0
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f807,f802,f131,f11357])).

fof(f11357,plain,
    ( spl4_112
  <=> m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_112])])).

fof(f807,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_44 ),
    inference(unit_resulting_resolution,[],[f132,f803,f111])).

fof(f11352,plain,
    ( spl4_110
    | ~ spl4_0
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f806,f802,f131,f11350])).

fof(f11350,plain,
    ( spl4_110
  <=> m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_110])])).

fof(f806,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_44 ),
    inference(unit_resulting_resolution,[],[f132,f803,f112])).

fof(f11345,plain,
    ( spl4_108
    | ~ spl4_0
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f805,f802,f131,f11343])).

fof(f11343,plain,
    ( spl4_108
  <=> m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_108])])).

fof(f805,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_44 ),
    inference(unit_resulting_resolution,[],[f132,f803,f113])).

fof(f11251,plain,
    ( spl4_106
    | ~ spl4_0
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f765,f721,f131,f11249])).

fof(f11249,plain,
    ( spl4_106
  <=> m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_106])])).

fof(f765,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_40 ),
    inference(unit_resulting_resolution,[],[f132,f722,f113])).

fof(f11244,plain,
    ( spl4_104
    | ~ spl4_0
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f753,f652,f131,f11242])).

fof(f11242,plain,
    ( spl4_104
  <=> m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_104])])).

fof(f753,plain,
    ( m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_34 ),
    inference(unit_resulting_resolution,[],[f132,f653,f113])).

fof(f10672,plain,
    ( spl4_102
    | ~ spl4_0
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f725,f721,f131,f10670])).

fof(f10670,plain,
    ( spl4_102
  <=> m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_102])])).

fof(f725,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_40 ),
    inference(unit_resulting_resolution,[],[f132,f722,f111])).

fof(f10665,plain,
    ( spl4_100
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f774,f145,f10663])).

fof(f10663,plain,
    ( spl4_100
  <=> m1_subset_1(k2_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_100])])).

fof(f774,plain,
    ( m1_subset_1(k2_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f146,f100,f113])).

fof(f10658,plain,
    ( spl4_98
    | ~ spl4_0
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f676,f652,f131,f10656])).

fof(f10656,plain,
    ( spl4_98
  <=> m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_98])])).

fof(f676,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,o_0_0_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_34 ),
    inference(unit_resulting_resolution,[],[f132,f653,f112])).

fof(f10098,plain,
    ( spl4_96
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f694,f145,f10096])).

fof(f10096,plain,
    ( spl4_96
  <=> m1_subset_1(k2_pre_topc(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_96])])).

fof(f694,plain,
    ( m1_subset_1(k2_pre_topc(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f146,f100,f112])).

fof(f10091,plain,
    ( spl4_94
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f959,f145,f138,f10089])).

fof(f10089,plain,
    ( spl4_94
  <=> k2_pre_topc(sK3,o_0_0_xboole_0) = k2_pre_topc(sK3,k2_pre_topc(sK3,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_94])])).

fof(f959,plain,
    ( k2_pre_topc(sK3,o_0_0_xboole_0) = k2_pre_topc(sK3,k2_pre_topc(sK3,o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f146,f500,f115])).

fof(f10084,plain,
    ( spl4_92
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f845,f145,f138,f10082])).

fof(f10082,plain,
    ( spl4_92
  <=> k1_tops_1(sK3,o_0_0_xboole_0) = k1_tops_1(sK3,k1_tops_1(sK3,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_92])])).

fof(f845,plain,
    ( k1_tops_1(sK3,o_0_0_xboole_0) = k1_tops_1(sK3,k1_tops_1(sK3,o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f146,f500,f114])).

fof(f9803,plain,
    ( spl4_90
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f626,f145,f9801])).

fof(f9801,plain,
    ( spl4_90
  <=> m1_subset_1(k1_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).

fof(f626,plain,
    ( m1_subset_1(k1_tops_1(sK3,sK2(k1_zfmisc_1(u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f146,f100,f111])).

fof(f8747,plain,
    ( spl4_88
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f958,f138,f131,f8745])).

fof(f8745,plain,
    ( spl4_88
  <=> k2_pre_topc(sK0,o_0_0_xboole_0) = k2_pre_topc(sK0,k2_pre_topc(sK0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_88])])).

fof(f958,plain,
    ( k2_pre_topc(sK0,o_0_0_xboole_0) = k2_pre_topc(sK0,k2_pre_topc(sK0,o_0_0_xboole_0))
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f132,f500,f115])).

fof(f8675,plain,
    ( spl4_86
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f844,f138,f131,f8673])).

fof(f8673,plain,
    ( spl4_86
  <=> k1_tops_1(sK0,o_0_0_xboole_0) = k1_tops_1(sK0,k1_tops_1(sK0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_86])])).

fof(f844,plain,
    ( k1_tops_1(sK0,o_0_0_xboole_0) = k1_tops_1(sK0,k1_tops_1(sK0,o_0_0_xboole_0))
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f132,f500,f114])).

fof(f7389,plain,
    ( spl4_84
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f428,f424,f7387])).

fof(f7387,plain,
    ( spl4_84
  <=> k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).

fof(f428,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)) = o_0_0_xboole_0
    | ~ spl4_30 ),
    inference(unit_resulting_resolution,[],[f425,f109])).

fof(f5078,plain,
    ( spl4_82
    | ~ spl4_0
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f785,f780,f131,f5076])).

fof(f5076,plain,
    ( spl4_82
  <=> m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).

fof(f785,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_42 ),
    inference(unit_resulting_resolution,[],[f132,f781,f111])).

fof(f5071,plain,
    ( spl4_80
    | ~ spl4_0
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f784,f780,f131,f5069])).

fof(f5069,plain,
    ( spl4_80
  <=> m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).

fof(f784,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_42 ),
    inference(unit_resulting_resolution,[],[f132,f781,f112])).

fof(f5064,plain,
    ( spl4_78
    | ~ spl4_0
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f783,f780,f131,f5062])).

fof(f5062,plain,
    ( spl4_78
  <=> m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).

fof(f783,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_42 ),
    inference(unit_resulting_resolution,[],[f132,f781,f113])).

fof(f4697,plain,
    ( spl4_76
    | ~ spl4_0
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f764,f700,f131,f4695])).

fof(f4695,plain,
    ( spl4_76
  <=> m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).

fof(f764,plain,
    ( m1_subset_1(k2_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_38 ),
    inference(unit_resulting_resolution,[],[f132,f701,f113])).

fof(f4515,plain,
    ( spl4_74
    | ~ spl4_0
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f752,f632,f131,f4513])).

fof(f4513,plain,
    ( spl4_74
  <=> m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).

fof(f752,plain,
    ( m1_subset_1(k2_tops_1(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_32 ),
    inference(unit_resulting_resolution,[],[f132,f633,f113])).

fof(f4173,plain,
    ( spl4_72
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f773,f131,f4171])).

fof(f4171,plain,
    ( spl4_72
  <=> m1_subset_1(k2_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f773,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f132,f100,f113])).

fof(f4166,plain,
    ( spl4_70
    | ~ spl4_0
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f704,f700,f131,f4164])).

fof(f4164,plain,
    ( spl4_70
  <=> m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f704,plain,
    ( m1_subset_1(k1_tops_1(sK0,k2_pre_topc(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_38 ),
    inference(unit_resulting_resolution,[],[f132,f701,f111])).

fof(f3832,plain,
    ( spl4_68
    | ~ spl4_0
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f675,f632,f131,f3830])).

fof(f3830,plain,
    ( spl4_68
  <=> m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f675,plain,
    ( m1_subset_1(k2_pre_topc(sK0,k1_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_32 ),
    inference(unit_resulting_resolution,[],[f132,f633,f112])).

fof(f3673,plain,
    ( spl4_66
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f693,f131,f3671])).

fof(f3671,plain,
    ( spl4_66
  <=> m1_subset_1(k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_66])])).

fof(f693,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f132,f100,f112])).

fof(f2943,plain,
    ( spl4_64
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f625,f131,f2941])).

fof(f2941,plain,
    ( spl4_64
  <=> m1_subset_1(k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f625,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2(k1_zfmisc_1(u1_struct_0(sK0)))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f132,f100,f111])).

fof(f2665,plain,
    ( spl4_62
    | ~ spl4_0
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f963,f152,f131,f2663])).

fof(f2663,plain,
    ( spl4_62
  <=> k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f963,plain,
    ( k2_pre_topc(sK0,sK1) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl4_0
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f132,f153,f115])).

fof(f2610,plain,
    ( spl4_60
    | ~ spl4_0
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f849,f152,f131,f2608])).

fof(f2608,plain,
    ( spl4_60
  <=> k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f849,plain,
    ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1))
    | ~ spl4_0
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f132,f153,f114])).

fof(f2583,plain,
    ( spl4_58
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f1954,f152,f138,f2581])).

fof(f2581,plain,
    ( spl4_58
  <=> o_0_0_xboole_0 = k4_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f1954,plain,
    ( o_0_0_xboole_0 = k4_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f1953,f514])).

fof(f1953,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,o_0_0_xboole_0) = k4_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f1952,f507])).

fof(f1952,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))) = k4_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f1406,f454])).

fof(f1406,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))) = k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f153,f506,f110])).

fof(f2468,plain,
    ( spl4_56
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f2454,f2449,f2466])).

fof(f2466,plain,
    ( spl4_56
  <=> r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f2449,plain,
    ( spl4_52
  <=> k4_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f2454,plain,
    ( r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_52 ),
    inference(superposition,[],[f102,f2450])).

fof(f2450,plain,
    ( k4_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) = sK1
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f2449])).

fof(f2461,plain,
    ( spl4_54
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f2453,f2449,f2459])).

fof(f2459,plain,
    ( spl4_54
  <=> r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f2453,plain,
    ( r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK1)
    | ~ spl4_52 ),
    inference(superposition,[],[f173,f2450])).

fof(f2451,plain,
    ( spl4_52
    | ~ spl4_6
    | ~ spl4_26
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f2107,f334,f302,f152,f2449])).

fof(f334,plain,
    ( spl4_28
  <=> k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f2107,plain,
    ( k4_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1)) = sK1
    | ~ spl4_6
    | ~ spl4_26
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f2106,f265])).

fof(f2106,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK1) = k4_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_6
    | ~ spl4_26
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f2105,f335])).

fof(f335,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f334])).

fof(f2105,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) = k4_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_6
    | ~ spl4_26 ),
    inference(forward_demodulation,[],[f1354,f454])).

fof(f1354,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))) = k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_6
    | ~ spl4_26 ),
    inference(unit_resulting_resolution,[],[f153,f303,f110])).

fof(f936,plain,
    ( spl4_50
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f427,f424,f934])).

fof(f934,plain,
    ( spl4_50
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f427,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_30 ),
    inference(unit_resulting_resolution,[],[f425,f108])).

fof(f868,plain,
    ( spl4_48
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f768,f145,f138,f866])).

fof(f768,plain,
    ( m1_subset_1(k2_tops_1(sK3,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f146,f500,f113])).

fof(f826,plain,
    ( spl4_46
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f688,f145,f138,f824])).

fof(f688,plain,
    ( m1_subset_1(k2_pre_topc(sK3,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f146,f500,f112])).

fof(f804,plain,
    ( spl4_44
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f767,f138,f131,f802])).

fof(f767,plain,
    ( m1_subset_1(k2_tops_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f132,f500,f113])).

fof(f782,plain,
    ( spl4_42
    | ~ spl4_0
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f772,f152,f131,f780])).

fof(f772,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f132,f153,f113])).

fof(f723,plain,
    ( spl4_40
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f687,f138,f131,f721])).

fof(f687,plain,
    ( m1_subset_1(k2_pre_topc(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f132,f500,f112])).

fof(f702,plain,
    ( spl4_38
    | ~ spl4_0
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f692,f152,f131,f700])).

fof(f692,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f132,f153,f112])).

fof(f674,plain,
    ( spl4_36
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f620,f145,f138,f672])).

fof(f620,plain,
    ( m1_subset_1(k1_tops_1(sK3,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f146,f500,f111])).

fof(f654,plain,
    ( spl4_34
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f619,f138,f131,f652])).

fof(f619,plain,
    ( m1_subset_1(k1_tops_1(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f132,f500,f111])).

fof(f634,plain,
    ( spl4_32
    | ~ spl4_0
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f624,f152,f131,f632])).

fof(f624,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f132,f153,f111])).

fof(f426,plain,
    ( spl4_30
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f418,f152,f138,f424])).

fof(f418,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(superposition,[],[f405,f188])).

fof(f405,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f396,f362])).

fof(f362,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f153,f120])).

fof(f336,plain,
    ( spl4_28
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f323,f152,f334])).

fof(f323,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f153,f109])).

fof(f304,plain,
    ( spl4_26
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f242,f152,f302])).

fof(f242,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f153,f108])).

fof(f296,plain,
    ( spl4_24
    | ~ spl4_2
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f278,f270,f138,f294])).

fof(f294,plain,
    ( spl4_24
  <=> k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f270,plain,
    ( spl4_22
  <=> v1_xboole_0(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f278,plain,
    ( k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl4_2
    | ~ spl4_22 ),
    inference(unit_resulting_resolution,[],[f271,f157])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f155,f97])).

fof(f271,plain,
    ( v1_xboole_0(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f270])).

fof(f272,plain,
    ( spl4_22
    | ~ spl4_2
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f261,f256,f138,f270])).

fof(f256,plain,
    ( spl4_20
  <=> m1_subset_1(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f261,plain,
    ( v1_xboole_0(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_20 ),
    inference(unit_resulting_resolution,[],[f100,f260,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t73_tops_1.p',t2_subset)).

fof(f260,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_20 ),
    inference(unit_resulting_resolution,[],[f139,f257,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t73_tops_1.p',t5_subset)).

fof(f257,plain,
    ( m1_subset_1(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f256])).

fof(f258,plain,
    ( spl4_20
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f250,f247,f256])).

fof(f247,plain,
    ( spl4_18
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f250,plain,
    ( m1_subset_1(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_18 ),
    inference(unit_resulting_resolution,[],[f248,f108])).

fof(f248,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f247])).

fof(f249,plain,
    ( spl4_18
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f240,f237,f247])).

fof(f237,plain,
    ( spl4_16
  <=> o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f240,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_16 ),
    inference(superposition,[],[f100,f238])).

fof(f238,plain,
    ( o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f237])).

fof(f239,plain,
    ( spl4_16
    | ~ spl4_2
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f224,f216,f138,f237])).

fof(f216,plain,
    ( spl4_14
  <=> v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f224,plain,
    ( o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_14 ),
    inference(unit_resulting_resolution,[],[f217,f157])).

fof(f217,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f216])).

fof(f218,plain,
    ( spl4_14
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f211,f138,f216])).

fof(f211,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f100,f210,f107])).

fof(f210,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f139,f100,f125])).

fof(f204,plain,
    ( ~ spl4_13
    | spl4_11 ),
    inference(avatar_split_clause,[],[f186,f183,f202])).

fof(f186,plain,
    ( ~ r1_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f184,f106])).

fof(f185,plain,(
    ~ spl4_11 ),
    inference(avatar_split_clause,[],[f92,f183])).

fof(f92,plain,(
    ~ r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f50,f84,f83])).

fof(f83,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ r1_xboole_0(k1_tops_1(sK0,X1),k2_tops_1(sK0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_xboole_0(k1_tops_1(X0,sK1),k2_tops_1(X0,sK1))
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t73_tops_1.p',t73_tops_1)).

fof(f167,plain,
    ( spl4_8
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f155,f138,f165])).

fof(f165,plain,
    ( spl4_8
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f154,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f91,f152])).

fof(f91,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f85])).

fof(f147,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f126,f145])).

fof(f126,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    l1_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f23,f88])).

fof(f88,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK3) ),
    introduced(choice_axiom,[])).

fof(f23,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t73_tops_1.p',existence_l1_pre_topc)).

fof(f140,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f93,f138])).

fof(f93,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t73_tops_1.p',dt_o_0_0_xboole_0)).

fof(f133,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f90,f131])).

fof(f90,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f85])).
%------------------------------------------------------------------------------
