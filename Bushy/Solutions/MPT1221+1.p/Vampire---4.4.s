%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_1__t29_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:27 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  191 ( 387 expanded)
%              Number of leaves         :   50 ( 158 expanded)
%              Depth                    :   12
%              Number of atoms          :  513 (1030 expanded)
%              Number of equality atoms :   42 (  95 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f601,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f106,f113,f120,f129,f136,f143,f156,f168,f177,f184,f205,f212,f219,f232,f236,f245,f266,f279,f288,f298,f322,f330,f357,f387,f409,f565,f582,f593,f600])).

fof(f600,plain,
    ( ~ spl5_0
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_24
    | ~ spl5_28
    | spl5_31
    | ~ spl5_48 ),
    inference(avatar_contradiction_clause,[],[f599])).

fof(f599,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_24
    | ~ spl5_28
    | ~ spl5_31
    | ~ spl5_48 ),
    inference(subsumption_resolution,[],[f598,f228])).

fof(f228,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl5_31
  <=> ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f598,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_24
    | ~ spl5_28
    | ~ spl5_48 ),
    inference(forward_demodulation,[],[f597,f386])).

fof(f386,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl5_48 ),
    inference(avatar_component_clause,[],[f385])).

fof(f385,plain,
    ( spl5_48
  <=> k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f597,plain,
    ( v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_24
    | ~ spl5_28 ),
    inference(forward_demodulation,[],[f596,f460])).

fof(f460,plain,
    ( ! [X0] : k4_xboole_0(u1_struct_0(sK0),X0) = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X0)
    | ~ spl5_24 ),
    inference(unit_resulting_resolution,[],[f211,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t29_tops_1.p',redefinition_k7_subset_1)).

fof(f211,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl5_24
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f596,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK0)
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_28 ),
    inference(forward_demodulation,[],[f595,f176])).

fof(f176,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl5_18
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f595,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f594,f98])).

fof(f98,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl5_0
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f594,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_12
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f588,f142])).

fof(f142,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl5_12
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f588,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_28 ),
    inference(resolution,[],[f225,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t29_tops_1.p',d6_pre_topc)).

fof(f225,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl5_28
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f593,plain,
    ( ~ spl5_0
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_24
    | ~ spl5_28
    | spl5_31
    | ~ spl5_48 ),
    inference(avatar_contradiction_clause,[],[f592])).

fof(f592,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_24
    | ~ spl5_28
    | ~ spl5_31
    | ~ spl5_48 ),
    inference(subsumption_resolution,[],[f591,f228])).

fof(f591,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_24
    | ~ spl5_28
    | ~ spl5_48 ),
    inference(forward_demodulation,[],[f590,f386])).

fof(f590,plain,
    ( v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_24
    | ~ spl5_28 ),
    inference(forward_demodulation,[],[f589,f460])).

fof(f589,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK0)
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_28 ),
    inference(forward_demodulation,[],[f587,f176])).

fof(f587,plain,
    ( v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_28 ),
    inference(unit_resulting_resolution,[],[f98,f142,f225,f75])).

fof(f582,plain,
    ( ~ spl5_0
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_24
    | spl5_29
    | ~ spl5_30
    | ~ spl5_48 ),
    inference(avatar_contradiction_clause,[],[f581])).

fof(f581,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_24
    | ~ spl5_29
    | ~ spl5_30
    | ~ spl5_48 ),
    inference(subsumption_resolution,[],[f580,f231])).

fof(f231,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl5_30
  <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f580,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_24
    | ~ spl5_29
    | ~ spl5_48 ),
    inference(forward_demodulation,[],[f579,f386])).

fof(f579,plain,
    ( ~ v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_24
    | ~ spl5_29 ),
    inference(forward_demodulation,[],[f578,f460])).

fof(f578,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK0)
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_18
    | ~ spl5_29 ),
    inference(forward_demodulation,[],[f575,f176])).

fof(f575,plain,
    ( ~ v3_pre_topc(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1),sK0)
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_29 ),
    inference(unit_resulting_resolution,[],[f98,f222,f142,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f222,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl5_29
  <=> ~ v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f565,plain,
    ( spl5_52
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f270,f203,f563])).

fof(f563,plain,
    ( spl5_52
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK4),u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f203,plain,
    ( spl5_22
  <=> m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f270,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK4),u1_struct_0(sK4)),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl5_22 ),
    inference(unit_resulting_resolution,[],[f204,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t29_tops_1.p',dt_k3_subset_1)).

fof(f204,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f203])).

fof(f409,plain,
    ( spl5_50
    | ~ spl5_44
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f380,f355,f328,f407])).

fof(f407,plain,
    ( spl5_50
  <=> k4_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f328,plain,
    ( spl5_44
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f355,plain,
    ( spl5_46
  <=> k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f380,plain,
    ( k4_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1
    | ~ spl5_44
    | ~ spl5_46 ),
    inference(forward_demodulation,[],[f369,f356])).

fof(f356,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f355])).

fof(f369,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k4_xboole_0(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl5_44 ),
    inference(unit_resulting_resolution,[],[f329,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t29_tops_1.p',d5_subset_1)).

fof(f329,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f328])).

fof(f387,plain,
    ( spl5_48
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f372,f141,f385])).

fof(f372,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f142,f84])).

fof(f357,plain,
    ( spl5_46
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f335,f141,f355])).

fof(f335,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = sK1
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f142,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t29_tops_1.p',involutiveness_k3_subset_1)).

fof(f330,plain,
    ( spl5_44
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f269,f141,f328])).

fof(f269,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f142,f82])).

fof(f322,plain,
    ( spl5_42
    | ~ spl5_2
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f304,f296,f104,f320])).

fof(f320,plain,
    ( spl5_42
  <=> k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f104,plain,
    ( spl5_2
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f296,plain,
    ( spl5_40
  <=> v1_xboole_0(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f304,plain,
    ( k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl5_2
    | ~ spl5_40 ),
    inference(unit_resulting_resolution,[],[f297,f146])).

fof(f146,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f144,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t29_tops_1.p',t6_boole)).

fof(f144,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f105,f77])).

fof(f105,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f297,plain,
    ( v1_xboole_0(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f296])).

fof(f298,plain,
    ( spl5_40
    | ~ spl5_2
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f291,f286,f104,f296])).

fof(f286,plain,
    ( spl5_38
  <=> m1_subset_1(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f291,plain,
    ( v1_xboole_0(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_2
    | ~ spl5_38 ),
    inference(unit_resulting_resolution,[],[f78,f290,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t29_tops_1.p',t2_subset)).

fof(f290,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0))
    | ~ spl5_2
    | ~ spl5_38 ),
    inference(unit_resulting_resolution,[],[f105,f287,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t29_tops_1.p',t5_subset)).

fof(f287,plain,
    ( m1_subset_1(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f286])).

fof(f78,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t29_tops_1.p',existence_m1_subset_1)).

fof(f288,plain,
    ( spl5_38
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f280,f277,f286])).

fof(f277,plain,
    ( spl5_36
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f280,plain,
    ( m1_subset_1(k3_subset_1(o_0_0_xboole_0,o_0_0_xboole_0),k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_36 ),
    inference(unit_resulting_resolution,[],[f278,f82])).

fof(f278,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f277])).

fof(f279,plain,
    ( spl5_36
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f267,f264,f277])).

fof(f264,plain,
    ( spl5_34
  <=> o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f267,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_34 ),
    inference(superposition,[],[f78,f265])).

fof(f265,plain,
    ( o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f264])).

fof(f266,plain,
    ( spl5_34
    | ~ spl5_2
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f251,f243,f104,f264])).

fof(f243,plain,
    ( spl5_32
  <=> v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f251,plain,
    ( o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_2
    | ~ spl5_32 ),
    inference(unit_resulting_resolution,[],[f244,f146])).

fof(f244,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f243])).

fof(f245,plain,
    ( spl5_32
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f238,f104,f243])).

fof(f238,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f78,f237,f81])).

fof(f237,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f105,f78,f90])).

fof(f236,plain,
    ( ~ spl5_29
    | ~ spl5_31 ),
    inference(avatar_split_clause,[],[f68,f227,f221])).

fof(f68,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,
    ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
      | ~ v4_pre_topc(sK1,sK0) )
    & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
      | v4_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f54,f56,f55])).

fof(f55,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | v4_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
            | ~ v4_pre_topc(X1,sK0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),X1),sK0)
            | v4_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v4_pre_topc(X1,X0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),sK1),X0)
          | ~ v4_pre_topc(sK1,X0) )
        & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),sK1),X0)
          | v4_pre_topc(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v4_pre_topc(X1,X0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | ~ v4_pre_topc(X1,X0) )
          & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
            | v4_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t29_tops_1.p',t29_tops_1)).

fof(f232,plain,
    ( spl5_28
    | spl5_30 ),
    inference(avatar_split_clause,[],[f67,f230,f224])).

fof(f67,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f219,plain,
    ( spl5_26
    | ~ spl5_10
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f193,f182,f134,f217])).

fof(f217,plain,
    ( spl5_26
  <=> m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f134,plain,
    ( spl5_10
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f182,plain,
    ( spl5_20
  <=> u1_struct_0(sK3) = k2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f193,plain,
    ( m1_subset_1(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl5_10
    | ~ spl5_20 ),
    inference(forward_demodulation,[],[f187,f183])).

fof(f183,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f182])).

fof(f187,plain,
    ( m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f135,f74])).

fof(f74,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t29_tops_1.p',dt_k2_struct_0)).

fof(f135,plain,
    ( l1_struct_0(sK3)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f134])).

fof(f212,plain,
    ( spl5_24
    | ~ spl5_8
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f194,f175,f127,f210])).

fof(f127,plain,
    ( spl5_8
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f194,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_8
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f186,f176])).

fof(f186,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f128,f74])).

fof(f128,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f127])).

fof(f205,plain,
    ( spl5_22
    | ~ spl5_6
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f195,f166,f118,f203])).

fof(f118,plain,
    ( spl5_6
  <=> l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f166,plain,
    ( spl5_16
  <=> u1_struct_0(sK4) = k2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f195,plain,
    ( m1_subset_1(u1_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl5_6
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f185,f167])).

fof(f167,plain,
    ( u1_struct_0(sK4) = k2_struct_0(sK4)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f166])).

fof(f185,plain,
    ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f119,f74])).

fof(f119,plain,
    ( l1_struct_0(sK4)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f118])).

fof(f184,plain,
    ( spl5_20
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f161,f134,f182])).

fof(f161,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3)
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f135,f73])).

fof(f73,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t29_tops_1.p',d3_struct_0)).

fof(f177,plain,
    ( spl5_18
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f160,f127,f175])).

fof(f160,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f128,f73])).

fof(f168,plain,
    ( spl5_16
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f159,f118,f166])).

fof(f159,plain,
    ( u1_struct_0(sK4) = k2_struct_0(sK4)
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f119,f73])).

fof(f156,plain,
    ( spl5_14
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f144,f104,f154])).

fof(f154,plain,
    ( spl5_14
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f143,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f66,f141])).

fof(f66,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f57])).

fof(f136,plain,
    ( spl5_10
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f122,f111,f134])).

fof(f111,plain,
    ( spl5_4
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f122,plain,
    ( l1_struct_0(sK3)
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f112,f72])).

fof(f72,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t29_tops_1.p',dt_l1_pre_topc)).

fof(f112,plain,
    ( l1_pre_topc(sK3)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f111])).

fof(f129,plain,
    ( spl5_8
    | ~ spl5_0 ),
    inference(avatar_split_clause,[],[f121,f97,f127])).

fof(f121,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_0 ),
    inference(unit_resulting_resolution,[],[f98,f72])).

fof(f120,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f92,f118])).

fof(f92,plain,(
    l1_struct_0(sK4) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    l1_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f63])).

fof(f63,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK4) ),
    introduced(choice_axiom,[])).

fof(f19,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t29_tops_1.p',existence_l1_struct_0)).

fof(f113,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f91,f111])).

fof(f91,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    l1_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f61])).

fof(f61,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK3) ),
    introduced(choice_axiom,[])).

fof(f18,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t29_tops_1.p',existence_l1_pre_topc)).

fof(f106,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f69,f104])).

fof(f69,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t29_tops_1.p',dt_o_0_0_xboole_0)).

fof(f99,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f65,f97])).

fof(f65,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f57])).
%------------------------------------------------------------------------------
