%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_1__t82_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:32 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  196 ( 453 expanded)
%              Number of leaves         :   54 ( 194 expanded)
%              Depth                    :   10
%              Number of atoms          :  531 (1499 expanded)
%              Number of equality atoms :   49 ( 110 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f637,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f119,f126,f133,f140,f147,f154,f161,f170,f177,f184,f191,f202,f212,f235,f242,f249,f258,f279,f292,f350,f364,f465,f472,f512,f519,f528,f607,f616,f624,f633])).

fof(f633,plain,
    ( ~ spl6_0
    | ~ spl6_2
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_20
    | ~ spl6_22
    | spl6_41
    | ~ spl6_50 ),
    inference(avatar_contradiction_clause,[],[f632])).

fof(f632,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_20
    | ~ spl6_22
    | ~ spl6_41
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f631,f530])).

fof(f530,plain,
    ( k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) != k2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_20
    | ~ spl6_41 ),
    inference(unit_resulting_resolution,[],[f118,f349,f416,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | k2_pre_topc(X0,X1) != k2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_pre_topc(X0,X1) != k2_struct_0(X0) )
            & ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t82_tops_1.p',d3_tops_1)).

fof(f416,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_20 ),
    inference(superposition,[],[f339,f90])).

fof(f90,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t82_tops_1.p',commutativity_k3_xboole_0)).

fof(f339,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_20 ),
    inference(backward_demodulation,[],[f326,f305])).

fof(f305,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_20 ),
    inference(unit_resulting_resolution,[],[f183,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t82_tops_1.p',dt_k9_subset_1)).

fof(f183,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl6_20
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f326,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1)
    | ~ spl6_20 ),
    inference(unit_resulting_resolution,[],[f183,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t82_tops_1.p',redefinition_k9_subset_1)).

fof(f349,plain,
    ( ~ v1_tops_1(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f348])).

fof(f348,plain,
    ( spl6_41
  <=> ~ v1_tops_1(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f118,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl6_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f631,plain,
    ( k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) = k2_struct_0(sK0)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_20
    | ~ spl6_22
    | ~ spl6_50 ),
    inference(forward_demodulation,[],[f630,f518])).

fof(f518,plain,
    ( k2_pre_topc(sK0,sK2) = k2_struct_0(sK0)
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f517])).

fof(f517,plain,
    ( spl6_50
  <=> k2_pre_topc(sK0,sK2) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f630,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_20
    | ~ spl6_22 ),
    inference(forward_demodulation,[],[f629,f90])).

fof(f629,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k3_xboole_0(sK2,sK1))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_20
    | ~ spl6_22 ),
    inference(forward_demodulation,[],[f626,f326])).

fof(f626,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_20
    | ~ spl6_22 ),
    inference(unit_resulting_resolution,[],[f111,f118,f160,f146,f183,f190,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( v3_pre_topc(X2,X0)
                 => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t82_tops_1.p',t81_tops_1)).

fof(f190,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl6_22
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f146,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl6_10
  <=> v1_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f160,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl6_14
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f111,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl6_0
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f624,plain,
    ( spl6_58
    | ~ spl6_4
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f565,f138,f124,f622])).

fof(f622,plain,
    ( spl6_58
  <=> m1_subset_1(k2_pre_topc(sK5,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f124,plain,
    ( spl6_4
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f138,plain,
    ( spl6_8
  <=> l1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f565,plain,
    ( m1_subset_1(k2_pre_topc(sK5,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ spl6_4
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f139,f553,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t82_tops_1.p',dt_k2_pre_topc)).

fof(f553,plain,
    ( ! [X5] : m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X5))
    | ~ spl6_4 ),
    inference(superposition,[],[f336,f213])).

fof(f213,plain,
    ( ! [X1] : k3_xboole_0(o_0_0_xboole_0,X1) = o_0_0_xboole_0
    | ~ spl6_4 ),
    inference(superposition,[],[f90,f195])).

fof(f195,plain,
    ( ! [X0] : k3_xboole_0(X0,o_0_0_xboole_0) = o_0_0_xboole_0
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f192,f81])).

fof(f81,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/tops_1__t82_tops_1.p',t2_boole)).

fof(f192,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f125,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t82_tops_1.p',t6_boole)).

fof(f125,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f124])).

fof(f336,plain,(
    ! [X0,X1] : m1_subset_1(k3_xboole_0(X1,sK3(k1_zfmisc_1(X0))),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f328,f307])).

fof(f307,plain,(
    ! [X0,X1] : m1_subset_1(k9_subset_1(X0,X1,sK3(k1_zfmisc_1(X0))),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f88,f99])).

fof(f88,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t82_tops_1.p',existence_m1_subset_1)).

fof(f328,plain,(
    ! [X0,X1] : k9_subset_1(X0,X1,sK3(k1_zfmisc_1(X0))) = k3_xboole_0(X1,sK3(k1_zfmisc_1(X0))) ),
    inference(unit_resulting_resolution,[],[f88,f100])).

fof(f139,plain,
    ( l1_pre_topc(sK5)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f138])).

fof(f616,plain,
    ( spl6_56
    | ~ spl6_2
    | ~ spl6_30
    | ~ spl6_54 ),
    inference(avatar_split_clause,[],[f608,f605,f240,f117,f614])).

fof(f614,plain,
    ( spl6_56
  <=> v1_tops_1(k2_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f240,plain,
    ( spl6_30
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f605,plain,
    ( spl6_54
  <=> k2_pre_topc(sK0,k2_struct_0(sK0)) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f608,plain,
    ( v1_tops_1(k2_struct_0(sK0),sK0)
    | ~ spl6_2
    | ~ spl6_30
    | ~ spl6_54 ),
    inference(unit_resulting_resolution,[],[f118,f241,f606,f86])).

fof(f606,plain,
    ( k2_pre_topc(sK0,k2_struct_0(sK0)) = k2_struct_0(sK0)
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f605])).

fof(f241,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f240])).

fof(f607,plain,
    ( spl6_54
    | ~ spl6_2
    | ~ spl6_22
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f595,f517,f189,f117,f605])).

fof(f595,plain,
    ( k2_pre_topc(sK0,k2_struct_0(sK0)) = k2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_22
    | ~ spl6_50 ),
    inference(forward_demodulation,[],[f590,f518])).

fof(f590,plain,
    ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK2))
    | ~ spl6_2
    | ~ spl6_22 ),
    inference(unit_resulting_resolution,[],[f118,f190,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t82_tops_1.p',projectivity_k2_pre_topc)).

fof(f528,plain,
    ( spl6_52
    | ~ spl6_2
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f453,f362,f117,f526])).

fof(f526,plain,
    ( spl6_52
  <=> m1_subset_1(k2_pre_topc(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f362,plain,
    ( spl6_42
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f453,plain,
    ( m1_subset_1(k2_pre_topc(sK0,o_0_0_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_2
    | ~ spl6_42 ),
    inference(unit_resulting_resolution,[],[f118,f363,f94])).

fof(f363,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f362])).

fof(f519,plain,
    ( spl6_50
    | ~ spl6_2
    | ~ spl6_12
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f493,f189,f152,f117,f517])).

fof(f152,plain,
    ( spl6_12
  <=> v1_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f493,plain,
    ( k2_pre_topc(sK0,sK2) = k2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_12
    | ~ spl6_22 ),
    inference(unit_resulting_resolution,[],[f118,f153,f190,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f153,plain,
    ( v1_tops_1(sK2,sK0)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f152])).

fof(f512,plain,
    ( spl6_48
    | ~ spl6_2
    | ~ spl6_10
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f492,f182,f145,f117,f510])).

fof(f510,plain,
    ( spl6_48
  <=> k2_pre_topc(sK0,sK1) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f492,plain,
    ( k2_pre_topc(sK0,sK1) = k2_struct_0(sK0)
    | ~ spl6_2
    | ~ spl6_10
    | ~ spl6_20 ),
    inference(unit_resulting_resolution,[],[f118,f146,f183,f85])).

fof(f472,plain,
    ( spl6_46
    | ~ spl6_2
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f455,f189,f117,f470])).

fof(f470,plain,
    ( spl6_46
  <=> m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f455,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_2
    | ~ spl6_22 ),
    inference(unit_resulting_resolution,[],[f118,f190,f94])).

fof(f465,plain,
    ( spl6_44
    | ~ spl6_2
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f454,f182,f117,f463])).

fof(f463,plain,
    ( spl6_44
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f454,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_2
    | ~ spl6_20 ),
    inference(unit_resulting_resolution,[],[f118,f183,f94])).

fof(f364,plain,
    ( spl6_42
    | ~ spl6_4
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f356,f189,f124,f362])).

fof(f356,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_4
    | ~ spl6_22 ),
    inference(superposition,[],[f338,f213])).

fof(f338,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_22 ),
    inference(backward_demodulation,[],[f327,f306])).

fof(f306,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_22 ),
    inference(unit_resulting_resolution,[],[f190,f99])).

fof(f327,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k3_xboole_0(X0,sK2)
    | ~ spl6_22 ),
    inference(unit_resulting_resolution,[],[f190,f100])).

fof(f350,plain,
    ( ~ spl6_41
    | ~ spl6_22
    | spl6_27 ),
    inference(avatar_split_clause,[],[f337,f210,f189,f348])).

fof(f210,plain,
    ( spl6_27
  <=> ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f337,plain,
    ( ~ v1_tops_1(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl6_22
    | ~ spl6_27 ),
    inference(backward_demodulation,[],[f327,f211])).

fof(f211,plain,
    ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f210])).

fof(f292,plain,
    ( spl6_38
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f280,f277,f290])).

fof(f290,plain,
    ( spl6_38
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f277,plain,
    ( spl6_36
  <=> o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f280,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_36 ),
    inference(superposition,[],[f88,f278])).

fof(f278,plain,
    ( o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f277])).

fof(f279,plain,
    ( spl6_36
    | ~ spl6_4
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f264,f256,f124,f277])).

fof(f256,plain,
    ( spl6_34
  <=> v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f264,plain,
    ( o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl6_4
    | ~ spl6_34 ),
    inference(unit_resulting_resolution,[],[f257,f194])).

fof(f194,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f192,f84])).

fof(f257,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f256])).

fof(f258,plain,
    ( spl6_34
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f251,f124,f256])).

fof(f251,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f88,f250,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t82_tops_1.p',t2_subset)).

fof(f250,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f125,f88,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t82_tops_1.p',t5_subset)).

fof(f249,plain,
    ( spl6_32
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f225,f175,f247])).

fof(f247,plain,
    ( spl6_32
  <=> m1_subset_1(k2_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f175,plain,
    ( spl6_18
  <=> l1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f225,plain,
    ( m1_subset_1(k2_struct_0(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ spl6_18 ),
    inference(unit_resulting_resolution,[],[f176,f82])).

fof(f82,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t82_tops_1.p',dt_k2_struct_0)).

fof(f176,plain,
    ( l1_struct_0(sK5)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f175])).

fof(f242,plain,
    ( spl6_30
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f224,f168,f240])).

fof(f168,plain,
    ( spl6_16
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f224,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_16 ),
    inference(unit_resulting_resolution,[],[f169,f82])).

fof(f169,plain,
    ( l1_struct_0(sK0)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f168])).

fof(f235,plain,
    ( spl6_28
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f223,f131,f233])).

fof(f233,plain,
    ( spl6_28
  <=> m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f131,plain,
    ( spl6_6
  <=> l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f223,plain,
    ( m1_subset_1(k2_struct_0(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f132,f82])).

fof(f132,plain,
    ( l1_struct_0(sK4)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f131])).

fof(f212,plain,(
    ~ spl6_27 ),
    inference(avatar_split_clause,[],[f79,f210])).

fof(f79,plain,(
    ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,
    ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v3_pre_topc(sK2,sK0)
    & v1_tops_1(sK2,sK0)
    & v1_tops_1(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f63,f62,f61])).

fof(f61,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v3_pre_topc(X2,X0)
                & v1_tops_1(X2,X0)
                & v1_tops_1(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v3_pre_topc(X2,sK0)
              & v1_tops_1(X2,sK0)
              & v1_tops_1(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_pre_topc(X2,X0)
              & v1_tops_1(X2,X0)
              & v1_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),sK1,X2),X0)
            & v3_pre_topc(X2,X0)
            & v1_tops_1(X2,X0)
            & v1_tops_1(sK1,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
          & v3_pre_topc(X2,X0)
          & v1_tops_1(X2,X0)
          & v1_tops_1(X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,sK2),X0)
        & v3_pre_topc(sK2,X0)
        & v1_tops_1(sK2,X0)
        & v1_tops_1(X1,X0)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_pre_topc(X2,X0)
              & v1_tops_1(X2,X0)
              & v1_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_pre_topc(X2,X0)
              & v1_tops_1(X2,X0)
              & v1_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & v1_tops_1(X2,X0)
                    & v1_tops_1(X1,X0) )
                 => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v3_pre_topc(X2,X0)
                  & v1_tops_1(X2,X0)
                  & v1_tops_1(X1,X0) )
               => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t82_tops_1.p',t82_tops_1)).

fof(f202,plain,
    ( spl6_24
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f192,f124,f200])).

fof(f200,plain,
    ( spl6_24
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f191,plain,(
    spl6_22 ),
    inference(avatar_split_clause,[],[f75,f189])).

fof(f75,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f64])).

fof(f184,plain,(
    spl6_20 ),
    inference(avatar_split_clause,[],[f74,f182])).

fof(f74,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f64])).

fof(f177,plain,
    ( spl6_18
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f163,f138,f175])).

fof(f163,plain,
    ( l1_struct_0(sK5)
    | ~ spl6_8 ),
    inference(unit_resulting_resolution,[],[f139,f83])).

fof(f83,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t82_tops_1.p',dt_l1_pre_topc)).

fof(f170,plain,
    ( spl6_16
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f162,f117,f168])).

fof(f162,plain,
    ( l1_struct_0(sK0)
    | ~ spl6_2 ),
    inference(unit_resulting_resolution,[],[f118,f83])).

fof(f161,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f78,f159])).

fof(f78,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f64])).

fof(f154,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f77,f152])).

fof(f77,plain,(
    v1_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f64])).

fof(f147,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f76,f145])).

fof(f76,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f64])).

fof(f140,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f105,f138])).

fof(f105,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    l1_pre_topc(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f18,f70])).

fof(f70,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK5) ),
    introduced(choice_axiom,[])).

fof(f18,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t82_tops_1.p',existence_l1_pre_topc)).

fof(f133,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f104,f131])).

fof(f104,plain,(
    l1_struct_0(sK4) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    l1_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f68])).

fof(f68,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK4) ),
    introduced(choice_axiom,[])).

fof(f19,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t82_tops_1.p',existence_l1_struct_0)).

fof(f126,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f80,f124])).

fof(f80,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t82_tops_1.p',dt_o_0_0_xboole_0)).

fof(f119,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f73,f117])).

fof(f73,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f64])).

fof(f112,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f72,f110])).

fof(f72,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f64])).
%------------------------------------------------------------------------------
