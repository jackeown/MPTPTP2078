%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 272 expanded)
%              Number of leaves         :   35 ( 124 expanded)
%              Depth                    :   13
%              Number of atoms          :  447 (1074 expanded)
%              Number of equality atoms :   62 ( 172 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f657,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f94,f99,f104,f109,f115,f121,f126,f132,f139,f144,f149,f157,f169,f206,f211,f303,f501,f533,f644,f654])).

fof(f654,plain,
    ( ~ spl5_3
    | spl5_6
    | ~ spl5_11
    | ~ spl5_17
    | ~ spl5_39
    | ~ spl5_42 ),
    inference(avatar_contradiction_clause,[],[f653])).

fof(f653,plain,
    ( $false
    | ~ spl5_3
    | spl5_6
    | ~ spl5_11
    | ~ spl5_17
    | ~ spl5_39
    | ~ spl5_42 ),
    inference(subsumption_resolution,[],[f652,f98])).

fof(f98,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl5_3
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f652,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl5_6
    | ~ spl5_11
    | ~ spl5_17
    | ~ spl5_39
    | ~ spl5_42 ),
    inference(subsumption_resolution,[],[f651,f143])).

fof(f143,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl5_11
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f651,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ v4_pre_topc(sK1,sK0)
    | spl5_6
    | ~ spl5_17
    | ~ spl5_39
    | ~ spl5_42 ),
    inference(subsumption_resolution,[],[f650,f114])).

fof(f114,plain,
    ( ~ v4_pre_topc(sK1,sK2)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl5_6
  <=> v4_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f650,plain,
    ( v4_pre_topc(sK1,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl5_17
    | ~ spl5_39
    | ~ spl5_42 ),
    inference(subsumption_resolution,[],[f648,f210])).

fof(f210,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl5_17
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f648,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK2)))
    | v4_pre_topc(sK1,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ v4_pre_topc(sK1,sK0)
    | ~ spl5_39
    | ~ spl5_42 ),
    inference(superposition,[],[f643,f532])).

fof(f532,plain,
    ( sK1 = k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2))
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f530])).

fof(f530,plain,
    ( spl5_39
  <=> sK1 = k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f643,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))
        | v4_pre_topc(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0) )
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f642])).

fof(f642,plain,
    ( spl5_42
  <=> ! [X0] :
        ( v4_pre_topc(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)
        | ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f644,plain,
    ( spl5_42
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f249,f203,f136,f91,f86,f642])).

fof(f86,plain,
    ( spl5_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f91,plain,
    ( spl5_2
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f136,plain,
    ( spl5_10
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f203,plain,
    ( spl5_16
  <=> u1_struct_0(sK2) = k2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f249,plain,
    ( ! [X0] :
        ( v4_pre_topc(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)
        | ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f248,f205])).

fof(f205,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f203])).

fof(f248,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f247,f205])).

fof(f247,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
        | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f246,f138])).

fof(f138,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f136])).

fof(f246,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
        | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) )
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f245,f88])).

fof(f88,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f245,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
        | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f84,f93])).

fof(f93,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(X2,X1)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ( k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2
                    & v4_pre_topc(sK4(X0,X1,X2),X0)
                    & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f49,f50])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
          & v4_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2
        & v4_pre_topc(sK4(X0,X1,X2),X0)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X4] :
                      ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                      & v4_pre_topc(X4,X0)
                      & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v4_pre_topc(X2,X1)
                  | ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                & ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ v4_pre_topc(X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_pre_topc)).

fof(f533,plain,
    ( spl5_39
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f513,f499,f530])).

fof(f499,plain,
    ( spl5_36
  <=> ! [X8] :
        ( k9_subset_1(k2_struct_0(sK2),sK1,k3_subset_1(k2_struct_0(sK2),X8)) = k4_xboole_0(sK1,X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f513,plain,
    ( sK1 = k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2))
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f512,f64])).

fof(f64,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f512,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2))
    | ~ spl5_36 ),
    inference(forward_demodulation,[],[f506,f164])).

fof(f164,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f160,f64])).

fof(f160,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(resolution,[],[f75,f62])).

fof(f62,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f506,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = k9_subset_1(k2_struct_0(sK2),sK1,k3_subset_1(k2_struct_0(sK2),k1_xboole_0))
    | ~ spl5_36 ),
    inference(resolution,[],[f500,f62])).

fof(f500,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK2)))
        | k9_subset_1(k2_struct_0(sK2),sK1,k3_subset_1(k2_struct_0(sK2),X8)) = k4_xboole_0(sK1,X8) )
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f499])).

fof(f501,plain,
    ( spl5_36
    | ~ spl5_17
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f492,f283,f208,f499])).

fof(f283,plain,
    ( spl5_23
  <=> ! [X1] : k7_subset_1(k2_struct_0(sK2),sK1,X1) = k4_xboole_0(sK1,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f492,plain,
    ( ! [X8] :
        ( k9_subset_1(k2_struct_0(sK2),sK1,k3_subset_1(k2_struct_0(sK2),X8)) = k4_xboole_0(sK1,X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK2))) )
    | ~ spl5_17
    | ~ spl5_23 ),
    inference(forward_demodulation,[],[f219,f284])).

fof(f284,plain,
    ( ! [X1] : k7_subset_1(k2_struct_0(sK2),sK1,X1) = k4_xboole_0(sK1,X1)
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f283])).

fof(f219,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK2)))
        | k7_subset_1(k2_struct_0(sK2),sK1,X8) = k9_subset_1(k2_struct_0(sK2),sK1,k3_subset_1(k2_struct_0(sK2),X8)) )
    | ~ spl5_17 ),
    inference(resolution,[],[f76,f210])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(f303,plain,
    ( spl5_23
    | ~ spl5_9
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f267,f203,f129,f283])).

fof(f129,plain,
    ( spl5_9
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f267,plain,
    ( ! [X2] : k4_xboole_0(sK1,X2) = k7_subset_1(k2_struct_0(sK2),sK1,X2)
    | ~ spl5_9
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f171,f205])).

fof(f171,plain,
    ( ! [X2] : k7_subset_1(u1_struct_0(sK2),sK1,X2) = k4_xboole_0(sK1,X2)
    | ~ spl5_9 ),
    inference(resolution,[],[f80,f131])).

fof(f131,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f129])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f211,plain,
    ( spl5_17
    | ~ spl5_9
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f201,f166,f129,f208])).

fof(f166,plain,
    ( spl5_14
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f201,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ spl5_9
    | ~ spl5_14 ),
    inference(backward_demodulation,[],[f131,f174])).

fof(f174,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ spl5_14 ),
    inference(resolution,[],[f168,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f168,plain,
    ( l1_struct_0(sK2)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f166])).

fof(f206,plain,
    ( spl5_16
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f174,f166,f203])).

fof(f169,plain,
    ( spl5_14
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f159,f154,f166])).

fof(f154,plain,
    ( spl5_13
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f159,plain,
    ( l1_struct_0(sK2)
    | ~ spl5_13 ),
    inference(resolution,[],[f156,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f156,plain,
    ( l1_pre_topc(sK2)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f154])).

fof(f157,plain,
    ( spl5_13
    | ~ spl5_2
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f152,f147,f91,f154])).

fof(f147,plain,
    ( spl5_12
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f152,plain,
    ( l1_pre_topc(sK2)
    | ~ spl5_2
    | ~ spl5_12 ),
    inference(resolution,[],[f148,f93])).

fof(f148,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f147])).

fof(f149,plain,
    ( spl5_12
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f145,f86,f147])).

fof(f145,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | l1_pre_topc(X0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f68,f88])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f144,plain,
    ( spl5_11
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f134,f123,f118,f141])).

fof(f118,plain,
    ( spl5_7
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f123,plain,
    ( spl5_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f134,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(backward_demodulation,[],[f125,f133])).

fof(f133,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl5_7 ),
    inference(resolution,[],[f65,f120])).

fof(f120,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f118])).

fof(f125,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f139,plain,
    ( spl5_10
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f133,f118,f136])).

fof(f132,plain,
    ( spl5_9
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f127,f101,f129])).

fof(f101,plain,
    ( spl5_4
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f127,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f57,f103])).

fof(f103,plain,
    ( sK1 = sK3
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ~ v4_pre_topc(sK3,sK2)
    & sK1 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & v4_pre_topc(sK1,sK0)
    & m1_pre_topc(sK2,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f46,f45,f44,f43])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v4_pre_topc(X3,X2)
                    & X1 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
                & v4_pre_topc(X1,X0)
                & m1_pre_topc(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,sK0)
              & m1_pre_topc(X2,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ v4_pre_topc(X3,X2)
                & X1 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
            & v4_pre_topc(X1,sK0)
            & m1_pre_topc(X2,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ v4_pre_topc(X3,X2)
              & sK1 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
          & v4_pre_topc(sK1,sK0)
          & m1_pre_topc(X2,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ v4_pre_topc(X3,X2)
            & sK1 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
        & v4_pre_topc(sK1,sK0)
        & m1_pre_topc(X2,sK0) )
   => ( ? [X3] :
          ( ~ v4_pre_topc(X3,sK2)
          & sK1 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
      & v4_pre_topc(sK1,sK0)
      & m1_pre_topc(sK2,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X3] :
        ( ~ v4_pre_topc(X3,sK2)
        & sK1 = X3
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
   => ( ~ v4_pre_topc(sK3,sK2)
      & sK1 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( v4_pre_topc(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( X1 = X3
                       => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v4_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_2)).

fof(f126,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f54,f123])).

fof(f54,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f47])).

fof(f121,plain,
    ( spl5_7
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f116,f86,f118])).

fof(f116,plain,
    ( l1_struct_0(sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f67,f88])).

fof(f115,plain,
    ( ~ spl5_6
    | ~ spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f110,f106,f101,f112])).

fof(f106,plain,
    ( spl5_5
  <=> v4_pre_topc(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f110,plain,
    ( ~ v4_pre_topc(sK1,sK2)
    | ~ spl5_4
    | spl5_5 ),
    inference(forward_demodulation,[],[f108,f103])).

fof(f108,plain,
    ( ~ v4_pre_topc(sK3,sK2)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f106])).

fof(f109,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f59,f106])).

fof(f59,plain,(
    ~ v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f104,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f58,f101])).

fof(f58,plain,(
    sK1 = sK3 ),
    inference(cnf_transformation,[],[f47])).

fof(f99,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f56,f96])).

fof(f56,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f94,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f55,f91])).

fof(f55,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f89,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f53,f86])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:41:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (8199)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.50  % (8189)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (8198)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (8208)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (8204)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (8190)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (8191)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (8205)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (8202)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (8196)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (8211)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (8188)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (8195)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (8194)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.53  % (8203)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.53  % (8197)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.53  % (8187)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.53  % (8192)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.53  % (8210)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.53  % (8209)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.54  % (8193)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.54  % (8201)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.54  % (8207)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.55  % (8189)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f657,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f89,f94,f99,f104,f109,f115,f121,f126,f132,f139,f144,f149,f157,f169,f206,f211,f303,f501,f533,f644,f654])).
% 0.21/0.55  fof(f654,plain,(
% 0.21/0.55    ~spl5_3 | spl5_6 | ~spl5_11 | ~spl5_17 | ~spl5_39 | ~spl5_42),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f653])).
% 0.21/0.55  fof(f653,plain,(
% 0.21/0.55    $false | (~spl5_3 | spl5_6 | ~spl5_11 | ~spl5_17 | ~spl5_39 | ~spl5_42)),
% 0.21/0.55    inference(subsumption_resolution,[],[f652,f98])).
% 0.21/0.55  fof(f98,plain,(
% 0.21/0.55    v4_pre_topc(sK1,sK0) | ~spl5_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f96])).
% 0.21/0.55  fof(f96,plain,(
% 0.21/0.55    spl5_3 <=> v4_pre_topc(sK1,sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.55  fof(f652,plain,(
% 0.21/0.55    ~v4_pre_topc(sK1,sK0) | (spl5_6 | ~spl5_11 | ~spl5_17 | ~spl5_39 | ~spl5_42)),
% 0.21/0.55    inference(subsumption_resolution,[],[f651,f143])).
% 0.21/0.55  fof(f143,plain,(
% 0.21/0.55    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl5_11),
% 0.21/0.55    inference(avatar_component_clause,[],[f141])).
% 0.21/0.55  fof(f141,plain,(
% 0.21/0.55    spl5_11 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.55  fof(f651,plain,(
% 0.21/0.55    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_pre_topc(sK1,sK0) | (spl5_6 | ~spl5_17 | ~spl5_39 | ~spl5_42)),
% 0.21/0.55    inference(subsumption_resolution,[],[f650,f114])).
% 0.21/0.55  fof(f114,plain,(
% 0.21/0.55    ~v4_pre_topc(sK1,sK2) | spl5_6),
% 0.21/0.55    inference(avatar_component_clause,[],[f112])).
% 0.21/0.55  fof(f112,plain,(
% 0.21/0.55    spl5_6 <=> v4_pre_topc(sK1,sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.55  fof(f650,plain,(
% 0.21/0.55    v4_pre_topc(sK1,sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_pre_topc(sK1,sK0) | (~spl5_17 | ~spl5_39 | ~spl5_42)),
% 0.21/0.55    inference(subsumption_resolution,[],[f648,f210])).
% 0.21/0.55  fof(f210,plain,(
% 0.21/0.55    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK2))) | ~spl5_17),
% 0.21/0.55    inference(avatar_component_clause,[],[f208])).
% 0.21/0.55  fof(f208,plain,(
% 0.21/0.55    spl5_17 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK2)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.55  fof(f648,plain,(
% 0.21/0.55    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK2))) | v4_pre_topc(sK1,sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_pre_topc(sK1,sK0) | (~spl5_39 | ~spl5_42)),
% 0.21/0.55    inference(superposition,[],[f643,f532])).
% 0.21/0.55  fof(f532,plain,(
% 0.21/0.55    sK1 = k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)) | ~spl5_39),
% 0.21/0.55    inference(avatar_component_clause,[],[f530])).
% 0.21/0.55  fof(f530,plain,(
% 0.21/0.55    spl5_39 <=> sK1 = k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 0.21/0.55  fof(f643,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) | v4_pre_topc(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_pre_topc(X0,sK0)) ) | ~spl5_42),
% 0.21/0.55    inference(avatar_component_clause,[],[f642])).
% 0.21/0.55  fof(f642,plain,(
% 0.21/0.55    spl5_42 <=> ! [X0] : (v4_pre_topc(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) | ~m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_pre_topc(X0,sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 0.21/0.55  fof(f644,plain,(
% 0.21/0.55    spl5_42 | ~spl5_1 | ~spl5_2 | ~spl5_10 | ~spl5_16),
% 0.21/0.55    inference(avatar_split_clause,[],[f249,f203,f136,f91,f86,f642])).
% 0.21/0.55  fof(f86,plain,(
% 0.21/0.55    spl5_1 <=> l1_pre_topc(sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.55  fof(f91,plain,(
% 0.21/0.55    spl5_2 <=> m1_pre_topc(sK2,sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.55  fof(f136,plain,(
% 0.21/0.55    spl5_10 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.55  fof(f203,plain,(
% 0.21/0.55    spl5_16 <=> u1_struct_0(sK2) = k2_struct_0(sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.55  fof(f249,plain,(
% 0.21/0.55    ( ! [X0] : (v4_pre_topc(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) | ~m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_pre_topc(X0,sK0)) ) | (~spl5_1 | ~spl5_2 | ~spl5_10 | ~spl5_16)),
% 0.21/0.55    inference(forward_demodulation,[],[f248,f205])).
% 0.21/0.55  fof(f205,plain,(
% 0.21/0.55    u1_struct_0(sK2) = k2_struct_0(sK2) | ~spl5_16),
% 0.21/0.55    inference(avatar_component_clause,[],[f203])).
% 0.21/0.55  fof(f248,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(k9_subset_1(k2_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)) ) | (~spl5_1 | ~spl5_2 | ~spl5_10 | ~spl5_16)),
% 0.21/0.55    inference(forward_demodulation,[],[f247,f205])).
% 0.21/0.55  fof(f247,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)) ) | (~spl5_1 | ~spl5_2 | ~spl5_10)),
% 0.21/0.55    inference(forward_demodulation,[],[f246,f138])).
% 0.21/0.55  fof(f138,plain,(
% 0.21/0.55    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl5_10),
% 0.21/0.55    inference(avatar_component_clause,[],[f136])).
% 0.21/0.55  fof(f246,plain,(
% 0.21/0.55    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)) ) | (~spl5_1 | ~spl5_2)),
% 0.21/0.55    inference(subsumption_resolution,[],[f245,f88])).
% 0.21/0.55  fof(f88,plain,(
% 0.21/0.55    l1_pre_topc(sK0) | ~spl5_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f86])).
% 0.21/0.55  fof(f245,plain,(
% 0.21/0.55    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) | ~l1_pre_topc(sK0)) ) | ~spl5_2),
% 0.21/0.55    inference(resolution,[],[f84,f93])).
% 0.21/0.55  fof(f93,plain,(
% 0.21/0.55    m1_pre_topc(sK2,sK0) | ~spl5_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f91])).
% 0.21/0.55  fof(f84,plain,(
% 0.21/0.55    ( ! [X0,X3,X1] : (~m1_pre_topc(X1,X0) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(equality_resolution,[],[f72])).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (v4_pre_topc(X2,X1) | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f51])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (((v4_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2 & v4_pre_topc(sK4(X0,X1,X2),X0) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f49,f50])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ! [X2,X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v4_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X1),sK4(X0,X1,X2),k2_struct_0(X1)) = X2 & v4_pre_topc(sK4(X0,X1,X2),X0) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (((v4_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & v4_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(rectify,[],[f48])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (((v4_pre_topc(X2,X1) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v4_pre_topc(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(nnf_transformation,[],[f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : ((v4_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f20])).
% 0.21/0.55  fof(f20,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_pre_topc)).
% 0.21/0.55  fof(f533,plain,(
% 0.21/0.55    spl5_39 | ~spl5_36),
% 0.21/0.55    inference(avatar_split_clause,[],[f513,f499,f530])).
% 0.21/0.55  fof(f499,plain,(
% 0.21/0.55    spl5_36 <=> ! [X8] : (k9_subset_1(k2_struct_0(sK2),sK1,k3_subset_1(k2_struct_0(sK2),X8)) = k4_xboole_0(sK1,X8) | ~m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK2))))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 0.21/0.55  fof(f513,plain,(
% 0.21/0.55    sK1 = k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)) | ~spl5_36),
% 0.21/0.55    inference(forward_demodulation,[],[f512,f64])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.55  fof(f512,plain,(
% 0.21/0.55    k4_xboole_0(sK1,k1_xboole_0) = k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)) | ~spl5_36),
% 0.21/0.55    inference(forward_demodulation,[],[f506,f164])).
% 0.21/0.55  fof(f164,plain,(
% 0.21/0.55    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.21/0.55    inference(forward_demodulation,[],[f160,f64])).
% 0.21/0.55  fof(f160,plain,(
% 0.21/0.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.21/0.55    inference(resolution,[],[f75,f62])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,axiom,(
% 0.21/0.55    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.55  fof(f75,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.55  fof(f506,plain,(
% 0.21/0.55    k4_xboole_0(sK1,k1_xboole_0) = k9_subset_1(k2_struct_0(sK2),sK1,k3_subset_1(k2_struct_0(sK2),k1_xboole_0)) | ~spl5_36),
% 0.21/0.55    inference(resolution,[],[f500,f62])).
% 0.21/0.55  fof(f500,plain,(
% 0.21/0.55    ( ! [X8] : (~m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK2))) | k9_subset_1(k2_struct_0(sK2),sK1,k3_subset_1(k2_struct_0(sK2),X8)) = k4_xboole_0(sK1,X8)) ) | ~spl5_36),
% 0.21/0.55    inference(avatar_component_clause,[],[f499])).
% 0.21/0.55  fof(f501,plain,(
% 0.21/0.55    spl5_36 | ~spl5_17 | ~spl5_23),
% 0.21/0.55    inference(avatar_split_clause,[],[f492,f283,f208,f499])).
% 0.21/0.55  fof(f283,plain,(
% 0.21/0.55    spl5_23 <=> ! [X1] : k7_subset_1(k2_struct_0(sK2),sK1,X1) = k4_xboole_0(sK1,X1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.21/0.55  fof(f492,plain,(
% 0.21/0.55    ( ! [X8] : (k9_subset_1(k2_struct_0(sK2),sK1,k3_subset_1(k2_struct_0(sK2),X8)) = k4_xboole_0(sK1,X8) | ~m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK2)))) ) | (~spl5_17 | ~spl5_23)),
% 0.21/0.55    inference(forward_demodulation,[],[f219,f284])).
% 0.21/0.55  fof(f284,plain,(
% 0.21/0.55    ( ! [X1] : (k7_subset_1(k2_struct_0(sK2),sK1,X1) = k4_xboole_0(sK1,X1)) ) | ~spl5_23),
% 0.21/0.55    inference(avatar_component_clause,[],[f283])).
% 0.21/0.55  fof(f219,plain,(
% 0.21/0.55    ( ! [X8] : (~m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK2))) | k7_subset_1(k2_struct_0(sK2),sK1,X8) = k9_subset_1(k2_struct_0(sK2),sK1,k3_subset_1(k2_struct_0(sK2),X8))) ) | ~spl5_17),
% 0.21/0.55    inference(resolution,[],[f76,f210])).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).
% 0.21/0.55  fof(f303,plain,(
% 0.21/0.55    spl5_23 | ~spl5_9 | ~spl5_16),
% 0.21/0.55    inference(avatar_split_clause,[],[f267,f203,f129,f283])).
% 0.21/0.55  fof(f129,plain,(
% 0.21/0.55    spl5_9 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.55  fof(f267,plain,(
% 0.21/0.55    ( ! [X2] : (k4_xboole_0(sK1,X2) = k7_subset_1(k2_struct_0(sK2),sK1,X2)) ) | (~spl5_9 | ~spl5_16)),
% 0.21/0.55    inference(forward_demodulation,[],[f171,f205])).
% 0.21/0.55  fof(f171,plain,(
% 0.21/0.55    ( ! [X2] : (k7_subset_1(u1_struct_0(sK2),sK1,X2) = k4_xboole_0(sK1,X2)) ) | ~spl5_9),
% 0.21/0.55    inference(resolution,[],[f80,f131])).
% 0.21/0.55  fof(f131,plain,(
% 0.21/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2))) | ~spl5_9),
% 0.21/0.55    inference(avatar_component_clause,[],[f129])).
% 0.21/0.55  fof(f80,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.55  fof(f211,plain,(
% 0.21/0.55    spl5_17 | ~spl5_9 | ~spl5_14),
% 0.21/0.55    inference(avatar_split_clause,[],[f201,f166,f129,f208])).
% 0.21/0.55  fof(f166,plain,(
% 0.21/0.55    spl5_14 <=> l1_struct_0(sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.55  fof(f201,plain,(
% 0.21/0.55    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK2))) | (~spl5_9 | ~spl5_14)),
% 0.21/0.55    inference(backward_demodulation,[],[f131,f174])).
% 0.21/0.55  fof(f174,plain,(
% 0.21/0.55    u1_struct_0(sK2) = k2_struct_0(sK2) | ~spl5_14),
% 0.21/0.55    inference(resolution,[],[f168,f65])).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,axiom,(
% 0.21/0.55    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.55  fof(f168,plain,(
% 0.21/0.55    l1_struct_0(sK2) | ~spl5_14),
% 0.21/0.55    inference(avatar_component_clause,[],[f166])).
% 0.21/0.55  fof(f206,plain,(
% 0.21/0.55    spl5_16 | ~spl5_14),
% 0.21/0.55    inference(avatar_split_clause,[],[f174,f166,f203])).
% 0.21/0.55  fof(f169,plain,(
% 0.21/0.55    spl5_14 | ~spl5_13),
% 0.21/0.55    inference(avatar_split_clause,[],[f159,f154,f166])).
% 0.21/0.55  fof(f154,plain,(
% 0.21/0.55    spl5_13 <=> l1_pre_topc(sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.55  fof(f159,plain,(
% 0.21/0.55    l1_struct_0(sK2) | ~spl5_13),
% 0.21/0.55    inference(resolution,[],[f156,f67])).
% 0.21/0.55  fof(f67,plain,(
% 0.21/0.55    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f17])).
% 0.21/0.55  fof(f17,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.55  fof(f156,plain,(
% 0.21/0.55    l1_pre_topc(sK2) | ~spl5_13),
% 0.21/0.55    inference(avatar_component_clause,[],[f154])).
% 0.21/0.55  fof(f157,plain,(
% 0.21/0.55    spl5_13 | ~spl5_2 | ~spl5_12),
% 0.21/0.55    inference(avatar_split_clause,[],[f152,f147,f91,f154])).
% 0.21/0.55  fof(f147,plain,(
% 0.21/0.55    spl5_12 <=> ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.55  fof(f152,plain,(
% 0.21/0.55    l1_pre_topc(sK2) | (~spl5_2 | ~spl5_12)),
% 0.21/0.55    inference(resolution,[],[f148,f93])).
% 0.21/0.55  fof(f148,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) ) | ~spl5_12),
% 0.21/0.55    inference(avatar_component_clause,[],[f147])).
% 0.21/0.55  fof(f149,plain,(
% 0.21/0.55    spl5_12 | ~spl5_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f145,f86,f147])).
% 0.21/0.55  fof(f145,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) ) | ~spl5_1),
% 0.21/0.55    inference(resolution,[],[f68,f88])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.55  fof(f144,plain,(
% 0.21/0.55    spl5_11 | ~spl5_7 | ~spl5_8),
% 0.21/0.55    inference(avatar_split_clause,[],[f134,f123,f118,f141])).
% 0.21/0.55  fof(f118,plain,(
% 0.21/0.55    spl5_7 <=> l1_struct_0(sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.55  fof(f123,plain,(
% 0.21/0.55    spl5_8 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.55  fof(f134,plain,(
% 0.21/0.55    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl5_7 | ~spl5_8)),
% 0.21/0.55    inference(backward_demodulation,[],[f125,f133])).
% 0.21/0.55  fof(f133,plain,(
% 0.21/0.55    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl5_7),
% 0.21/0.55    inference(resolution,[],[f65,f120])).
% 0.21/0.55  fof(f120,plain,(
% 0.21/0.55    l1_struct_0(sK0) | ~spl5_7),
% 0.21/0.55    inference(avatar_component_clause,[],[f118])).
% 0.21/0.55  fof(f125,plain,(
% 0.21/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_8),
% 0.21/0.55    inference(avatar_component_clause,[],[f123])).
% 0.21/0.55  fof(f139,plain,(
% 0.21/0.55    spl5_10 | ~spl5_7),
% 0.21/0.55    inference(avatar_split_clause,[],[f133,f118,f136])).
% 0.21/0.55  fof(f132,plain,(
% 0.21/0.55    spl5_9 | ~spl5_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f127,f101,f129])).
% 0.21/0.55  fof(f101,plain,(
% 0.21/0.55    spl5_4 <=> sK1 = sK3),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.55  fof(f127,plain,(
% 0.21/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2))) | ~spl5_4),
% 0.21/0.55    inference(forward_demodulation,[],[f57,f103])).
% 0.21/0.55  fof(f103,plain,(
% 0.21/0.55    sK1 = sK3 | ~spl5_4),
% 0.21/0.55    inference(avatar_component_clause,[],[f101])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.55    inference(cnf_transformation,[],[f47])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    (((~v4_pre_topc(sK3,sK2) & sK1 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & v4_pre_topc(sK1,sK0) & m1_pre_topc(sK2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f46,f45,f44,f43])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,sK0) & m1_pre_topc(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    ? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,sK0) & m1_pre_topc(X2,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & sK1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(sK1,sK0) & m1_pre_topc(X2,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    ? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & sK1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(sK1,sK0) & m1_pre_topc(X2,sK0)) => (? [X3] : (~v4_pre_topc(X3,sK2) & sK1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & v4_pre_topc(sK1,sK0) & m1_pre_topc(sK2,sK0))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ? [X3] : (~v4_pre_topc(X3,sK2) & sK1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) => (~v4_pre_topc(sK3,sK2) & sK1 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.55    inference(flattening,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~v4_pre_topc(X3,X2) & X1 = X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0)) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f22])).
% 0.21/0.55  fof(f22,negated_conjecture,(
% 0.21/0.55    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 0.21/0.55    inference(negated_conjecture,[],[f21])).
% 0.21/0.55  fof(f21,conjecture,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_2)).
% 0.21/0.55  fof(f126,plain,(
% 0.21/0.55    spl5_8),
% 0.21/0.55    inference(avatar_split_clause,[],[f54,f123])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.55    inference(cnf_transformation,[],[f47])).
% 0.21/0.55  fof(f121,plain,(
% 0.21/0.55    spl5_7 | ~spl5_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f116,f86,f118])).
% 0.21/0.55  fof(f116,plain,(
% 0.21/0.55    l1_struct_0(sK0) | ~spl5_1),
% 0.21/0.55    inference(resolution,[],[f67,f88])).
% 0.21/0.55  fof(f115,plain,(
% 0.21/0.55    ~spl5_6 | ~spl5_4 | spl5_5),
% 0.21/0.55    inference(avatar_split_clause,[],[f110,f106,f101,f112])).
% 0.21/0.55  fof(f106,plain,(
% 0.21/0.55    spl5_5 <=> v4_pre_topc(sK3,sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.55  fof(f110,plain,(
% 0.21/0.55    ~v4_pre_topc(sK1,sK2) | (~spl5_4 | spl5_5)),
% 0.21/0.55    inference(forward_demodulation,[],[f108,f103])).
% 0.21/0.55  fof(f108,plain,(
% 0.21/0.55    ~v4_pre_topc(sK3,sK2) | spl5_5),
% 0.21/0.55    inference(avatar_component_clause,[],[f106])).
% 0.21/0.55  fof(f109,plain,(
% 0.21/0.55    ~spl5_5),
% 0.21/0.55    inference(avatar_split_clause,[],[f59,f106])).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    ~v4_pre_topc(sK3,sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f47])).
% 0.21/0.55  fof(f104,plain,(
% 0.21/0.55    spl5_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f58,f101])).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    sK1 = sK3),
% 0.21/0.55    inference(cnf_transformation,[],[f47])).
% 0.21/0.55  fof(f99,plain,(
% 0.21/0.55    spl5_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f56,f96])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    v4_pre_topc(sK1,sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f47])).
% 0.21/0.55  fof(f94,plain,(
% 0.21/0.55    spl5_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f55,f91])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    m1_pre_topc(sK2,sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f47])).
% 0.21/0.55  fof(f89,plain,(
% 0.21/0.55    spl5_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f53,f86])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    l1_pre_topc(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f47])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (8189)------------------------------
% 0.21/0.55  % (8189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (8189)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (8189)Memory used [KB]: 6652
% 0.21/0.55  % (8189)Time elapsed: 0.117 s
% 0.21/0.55  % (8189)------------------------------
% 0.21/0.55  % (8189)------------------------------
% 0.21/0.55  % (8186)Success in time 0.181 s
%------------------------------------------------------------------------------
