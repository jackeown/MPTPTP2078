%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t27_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:29 EDT 2019

% Result     : Theorem 7.60s
% Output     : Refutation 7.60s
% Verified   : 
% Statistics : Number of formulae       :  242 (1730 expanded)
%              Number of leaves         :   37 ( 446 expanded)
%              Depth                    :   21
%              Number of atoms          :  742 (5544 expanded)
%              Number of equality atoms :   79 (1188 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8249,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f185,f218,f466,f470,f689,f1144,f1270,f1433,f1737,f1744,f3301,f3316,f4056,f8247])).

fof(f8247,plain,
    ( ~ spl8_0
    | spl8_11
    | ~ spl8_18
    | ~ spl8_26 ),
    inference(avatar_contradiction_clause,[],[f8242])).

fof(f8242,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_11
    | ~ spl8_18
    | ~ spl8_26 ),
    inference(unit_resulting_resolution,[],[f6362,f6352,f8157])).

fof(f8157,plain,
    ( ! [X2] :
        ( v3_pre_topc(X2,sK0)
        | ~ r1_tarski(X2,sK1) )
    | ~ spl8_0
    | ~ spl8_18
    | ~ spl8_26 ),
    inference(superposition,[],[f8092,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t27_tex_2.p',t28_xboole_1)).

fof(f8092,plain,
    ( ! [X0] : v3_pre_topc(k3_xboole_0(X0,sK1),sK0)
    | ~ spl8_0
    | ~ spl8_18
    | ~ spl8_26 ),
    inference(backward_demodulation,[],[f8090,f4386])).

fof(f4386,plain,
    ( ! [X0] : v3_pre_topc(sK4(sK0,sK1,k3_xboole_0(X0,sK1)),sK0)
    | ~ spl8_0 ),
    inference(forward_demodulation,[],[f4376,f3866])).

fof(f3866,plain,(
    ! [X1] : k3_xboole_0(X1,sK1) = k3_xboole_0(sK1,k3_xboole_0(X1,sK1)) ),
    inference(superposition,[],[f652,f112])).

fof(f112,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t27_tex_2.p',commutativity_k3_xboole_0)).

fof(f652,plain,(
    ! [X0] : k3_xboole_0(X0,sK1) = k3_xboole_0(k3_xboole_0(X0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f639,f107])).

fof(f639,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(X0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f171,f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k9_setfam_1(X1)) ) ),
    inference(definition_unfolding,[],[f100,f94])).

fof(f94,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t27_tex_2.p',redefinition_k9_setfam_1)).

fof(f100,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t27_tex_2.p',t3_subset)).

fof(f171,plain,(
    ! [X0] : m1_subset_1(k3_xboole_0(X0,sK1),k9_setfam_1(sK1)) ),
    inference(backward_demodulation,[],[f166,f167])).

fof(f167,plain,(
    ! [X0] : m1_subset_1(k9_subset_1(sK1,X0,sK1),k9_setfam_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f138,f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k9_setfam_1(X0))
      | ~ m1_subset_1(X2,k9_setfam_1(X0)) ) ),
    inference(definition_unfolding,[],[f97,f94,f94])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t27_tex_2.p',dt_k9_subset_1)).

fof(f138,plain,(
    m1_subset_1(sK1,k9_setfam_1(sK1)) ),
    inference(forward_demodulation,[],[f115,f71])).

fof(f71,plain,(
    u1_struct_0(sK0) = sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_tdlat_3(X0) )
          & u1_struct_0(X0) = X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_tdlat_3(X0) )
          & u1_struct_0(X0) = X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( u1_struct_0(X0) = X1
             => ( v2_tex_2(X1,X0)
              <=> v1_tdlat_3(X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( u1_struct_0(X0) = X1
           => ( v2_tex_2(X1,X0)
            <=> v1_tdlat_3(X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t27_tex_2.p',t27_tex_2)).

fof(f115,plain,(
    m1_subset_1(sK1,k9_setfam_1(u1_struct_0(sK0))) ),
    inference(definition_unfolding,[],[f70,f94])).

fof(f70,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f166,plain,(
    ! [X0] : k3_xboole_0(X0,sK1) = k9_subset_1(sK1,X0,sK1) ),
    inference(unit_resulting_resolution,[],[f138,f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k9_setfam_1(X0)) ) ),
    inference(definition_unfolding,[],[f96,f94])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t27_tex_2.p',redefinition_k9_subset_1)).

fof(f4376,plain,
    ( ! [X0] : v3_pre_topc(sK4(sK0,sK1,k3_xboole_0(sK1,k3_xboole_0(X0,sK1))),sK0)
    | ~ spl8_0 ),
    inference(unit_resulting_resolution,[],[f178,f730,f641,f138,f149])).

fof(f149,plain,(
    ! [X2,X3] :
      ( v3_pre_topc(sK4(sK0,X2,X3),sK0)
      | ~ m1_subset_1(X2,k9_setfam_1(sK1))
      | ~ r1_tarski(X3,X2)
      | ~ m1_subset_1(X3,k9_setfam_1(sK1))
      | ~ v2_tex_2(X2,sK0) ) ),
    inference(forward_demodulation,[],[f148,f71])).

fof(f148,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k9_setfam_1(sK1))
      | ~ m1_subset_1(X3,k9_setfam_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X3,X2)
      | v3_pre_topc(sK4(sK0,X2,X3),sK0)
      | ~ v2_tex_2(X2,sK0) ) ),
    inference(forward_demodulation,[],[f142,f71])).

fof(f142,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,k9_setfam_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X3,X2)
      | v3_pre_topc(sK4(sK0,X2,X3),sK0)
      | ~ v2_tex_2(X2,sK0) ) ),
    inference(resolution,[],[f73,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | v3_pre_topc(sK4(X0,X1,X2),X0)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(definition_unfolding,[],[f82,f94,f94])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | v3_pre_topc(sK4(X0,X1,X2),X0)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v3_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t27_tex_2.p',d5_tex_2)).

fof(f73,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f641,plain,(
    ! [X0] : m1_subset_1(k3_xboole_0(sK1,X0),k9_setfam_1(sK1)) ),
    inference(superposition,[],[f171,f112])).

fof(f730,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,k3_xboole_0(X1,sK1)),sK1) ),
    inference(unit_resulting_resolution,[],[f645,f133])).

fof(f645,plain,(
    ! [X0,X1] : m1_subset_1(k3_xboole_0(X0,k3_xboole_0(X1,sK1)),k9_setfam_1(sK1)) ),
    inference(backward_demodulation,[],[f636,f637])).

fof(f637,plain,(
    ! [X0,X1] : m1_subset_1(k9_subset_1(sK1,X0,k3_xboole_0(X1,sK1)),k9_setfam_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f171,f131])).

fof(f636,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,sK1)) = k9_subset_1(sK1,X0,k3_xboole_0(X1,sK1)) ),
    inference(unit_resulting_resolution,[],[f171,f130])).

fof(f178,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl8_0
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f8090,plain,
    ( ! [X0] : k3_xboole_0(X0,sK1) = sK4(sK0,sK1,k3_xboole_0(X0,sK1))
    | ~ spl8_0
    | ~ spl8_18
    | ~ spl8_26 ),
    inference(forward_demodulation,[],[f8024,f5122])).

fof(f5122,plain,
    ( ! [X0] : k3_xboole_0(X0,sK1) = k3_xboole_0(sK1,sK4(sK0,sK1,k3_xboole_0(X0,sK1)))
    | ~ spl8_26 ),
    inference(forward_demodulation,[],[f5084,f3866])).

fof(f5084,plain,
    ( ! [X0] : k3_xboole_0(sK1,k3_xboole_0(X0,sK1)) = k3_xboole_0(sK1,sK4(sK0,sK1,k3_xboole_0(sK1,k3_xboole_0(X0,sK1))))
    | ~ spl8_26 ),
    inference(unit_resulting_resolution,[],[f730,f641,f1736])).

fof(f1736,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k9_setfam_1(sK1))
        | ~ r1_tarski(X0,sK1)
        | k3_xboole_0(sK1,sK4(sK0,sK1,X0)) = X0 )
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f1735])).

fof(f1735,plain,
    ( spl8_26
  <=> ! [X0] :
        ( k3_xboole_0(sK1,sK4(sK0,sK1,X0)) = X0
        | ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k9_setfam_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f8024,plain,
    ( ! [X0] : k3_xboole_0(sK1,sK4(sK0,sK1,k3_xboole_0(X0,sK1))) = sK4(sK0,sK1,k3_xboole_0(X0,sK1))
    | ~ spl8_0
    | ~ spl8_18 ),
    inference(unit_resulting_resolution,[],[f7796,f7953])).

fof(f7953,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,sK1)
      | k3_xboole_0(sK1,X2) = X2 ) ),
    inference(superposition,[],[f3866,f107])).

fof(f7796,plain,
    ( ! [X0] : r1_tarski(sK4(sK0,sK1,k3_xboole_0(X0,sK1)),sK1)
    | ~ spl8_0
    | ~ spl8_18 ),
    inference(unit_resulting_resolution,[],[f1223,f133])).

fof(f1223,plain,
    ( ! [X0] : m1_subset_1(sK4(sK0,sK1,k3_xboole_0(X0,sK1)),k9_setfam_1(sK1))
    | ~ spl8_0
    | ~ spl8_18 ),
    inference(forward_demodulation,[],[f1205,f113])).

fof(f113,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/tex_2__t27_tex_2.p',idempotence_k3_xboole_0)).

fof(f1205,plain,
    ( ! [X0] : m1_subset_1(sK4(sK0,sK1,k3_xboole_0(X0,k3_xboole_0(sK1,sK1))),k9_setfam_1(sK1))
    | ~ spl8_0
    | ~ spl8_18 ),
    inference(unit_resulting_resolution,[],[f730,f681,f178,f138,f1143])).

fof(f1143,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(sK4(sK0,X2,X3),k9_setfam_1(sK1))
        | ~ v2_tex_2(X2,sK0)
        | ~ r1_tarski(X3,X2)
        | ~ m1_subset_1(X2,k9_setfam_1(sK1))
        | ~ m1_subset_1(X3,k9_setfam_1(sK1)) )
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f1142])).

fof(f1142,plain,
    ( spl8_18
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(X3,k9_setfam_1(sK1))
        | ~ v2_tex_2(X2,sK0)
        | ~ r1_tarski(X3,X2)
        | ~ m1_subset_1(X2,k9_setfam_1(sK1))
        | m1_subset_1(sK4(sK0,X2,X3),k9_setfam_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f681,plain,(
    ! [X0,X1] : m1_subset_1(k3_xboole_0(X0,k3_xboole_0(sK1,X1)),k9_setfam_1(sK1)) ),
    inference(backward_demodulation,[],[f672,f673])).

fof(f673,plain,(
    ! [X0,X1] : m1_subset_1(k9_subset_1(sK1,X0,k3_xboole_0(sK1,X1)),k9_setfam_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f641,f131])).

fof(f672,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k3_xboole_0(sK1,X1)) = k9_subset_1(sK1,X0,k3_xboole_0(sK1,X1)) ),
    inference(unit_resulting_resolution,[],[f641,f130])).

fof(f6352,plain,
    ( ~ v3_pre_topc(sK7(k9_setfam_1(sK1),u1_pre_topc(sK0)),sK0)
    | ~ spl8_11 ),
    inference(unit_resulting_resolution,[],[f4182,f6171,f147])).

fof(f147,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(X1,sK0)
      | r2_hidden(X1,u1_pre_topc(sK0))
      | ~ m1_subset_1(X1,k9_setfam_1(sK1)) ) ),
    inference(forward_demodulation,[],[f141,f71])).

fof(f141,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(sK0)))
      | r2_hidden(X1,u1_pre_topc(sK0))
      | ~ v3_pre_topc(X1,sK0) ) ),
    inference(resolution,[],[f73,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(definition_unfolding,[],[f90,f94])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t27_tex_2.p',d5_pre_topc)).

fof(f6171,plain,
    ( m1_subset_1(sK7(k9_setfam_1(sK1),u1_pre_topc(sK0)),k9_setfam_1(sK1))
    | ~ spl8_11 ),
    inference(unit_resulting_resolution,[],[f128,f4181,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k9_setfam_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(definition_unfolding,[],[f86,f94])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
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
    file('/export/starexec/sandbox/benchmark/tex_2__t27_tex_2.p',t4_subset)).

fof(f4181,plain,
    ( r2_hidden(sK7(k9_setfam_1(sK1),u1_pre_topc(sK0)),k9_setfam_1(sK1))
    | ~ spl8_11 ),
    inference(unit_resulting_resolution,[],[f1887,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t27_tex_2.p',d3_tarski)).

fof(f1887,plain,
    ( ~ r1_tarski(k9_setfam_1(sK1),u1_pre_topc(sK0))
    | ~ spl8_11 ),
    inference(unit_resulting_resolution,[],[f688,f631,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t27_tex_2.p',d10_xboole_0)).

fof(f631,plain,(
    r1_tarski(u1_pre_topc(sK0),k9_setfam_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f145,f133])).

fof(f145,plain,(
    m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(k9_setfam_1(sK1))) ),
    inference(forward_demodulation,[],[f139,f71])).

fof(f139,plain,(
    m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(k9_setfam_1(u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f73,f127])).

fof(f127,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k9_setfam_1(k9_setfam_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f91,f94,f94])).

fof(f91,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t27_tex_2.p',dt_u1_pre_topc)).

fof(f688,plain,
    ( u1_pre_topc(sK0) != k9_setfam_1(sK1)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f687])).

fof(f687,plain,
    ( spl8_11
  <=> u1_pre_topc(sK0) != k9_setfam_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f128,plain,(
    ! [X0] : m1_subset_1(k9_setfam_1(X0),k9_setfam_1(k9_setfam_1(X0))) ),
    inference(definition_unfolding,[],[f93,f94,f94])).

fof(f93,plain,(
    ! [X0] : m1_subset_1(k9_setfam_1(X0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k9_setfam_1(X0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t27_tex_2.p',dt_k9_setfam_1)).

fof(f4182,plain,
    ( ~ r2_hidden(sK7(k9_setfam_1(sK1),u1_pre_topc(sK0)),u1_pre_topc(sK0))
    | ~ spl8_11 ),
    inference(unit_resulting_resolution,[],[f1887,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f6362,plain,
    ( r1_tarski(sK7(k9_setfam_1(sK1),u1_pre_topc(sK0)),sK1)
    | ~ spl8_11 ),
    inference(unit_resulting_resolution,[],[f6171,f133])).

fof(f4056,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_12
    | ~ spl8_32 ),
    inference(avatar_contradiction_clause,[],[f4017])).

fof(f4017,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_12
    | ~ spl8_32 ),
    inference(unit_resulting_resolution,[],[f2831,f2681,f2772,f3300])).

fof(f3300,plain,
    ( ! [X0] :
        ( k3_xboole_0(X0,sK1) != sK3(sK0,sK1)
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,u1_pre_topc(sK0)) )
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f3299])).

fof(f3299,plain,
    ( spl8_32
  <=> ! [X0] :
        ( k3_xboole_0(X0,sK1) != sK3(sK0,sK1)
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,u1_pre_topc(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f2772,plain,
    ( k3_xboole_0(sK3(sK0,sK1),sK1) = sK3(sK0,sK1)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f2767,f107])).

fof(f2767,plain,
    ( r1_tarski(sK3(sK0,sK1),sK1)
    | ~ spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f175,f2607,f2613])).

fof(f2613,plain,
    ( ! [X6] :
        ( r1_tarski(sK3(sK0,X6),X6)
        | v2_tex_2(X6,sK0)
        | ~ m1_subset_1(X6,u1_pre_topc(sK0)) )
    | ~ spl8_2 ),
    inference(backward_demodulation,[],[f2606,f153])).

fof(f153,plain,(
    ! [X6] :
      ( v2_tex_2(X6,sK0)
      | r1_tarski(sK3(sK0,X6),X6)
      | ~ m1_subset_1(X6,k9_setfam_1(sK1)) ) ),
    inference(forward_demodulation,[],[f144,f71])).

fof(f144,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k9_setfam_1(u1_struct_0(sK0)))
      | r1_tarski(sK3(sK0,X6),X6)
      | v2_tex_2(X6,sK0) ) ),
    inference(resolution,[],[f73,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | r1_tarski(sK3(X0,X1),X1)
      | v2_tex_2(X1,X0) ) ),
    inference(definition_unfolding,[],[f85,f94])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(sK3(X0,X1),X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f2606,plain,
    ( u1_pre_topc(sK0) = k9_setfam_1(sK1)
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f2603,f71])).

fof(f2603,plain,
    ( u1_pre_topc(sK0) = k9_setfam_1(u1_struct_0(sK0))
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f73,f184,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(X0)
      | u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
      <=> u1_pre_topc(X0) = k9_setfam_1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t27_tex_2.p',d1_tdlat_3)).

fof(f184,plain,
    ( v1_tdlat_3(sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl8_2
  <=> v1_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f2607,plain,
    ( m1_subset_1(sK1,u1_pre_topc(sK0))
    | ~ spl8_2 ),
    inference(backward_demodulation,[],[f2606,f138])).

fof(f175,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl8_1
  <=> ~ v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f2681,plain,
    ( m1_subset_1(sK3(sK0,sK1),u1_pre_topc(sK0))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f175,f2607,f465])).

fof(f465,plain,
    ( ! [X4] :
        ( m1_subset_1(sK3(sK0,X4),u1_pre_topc(sK0))
        | v2_tex_2(X4,sK0)
        | ~ m1_subset_1(X4,u1_pre_topc(sK0)) )
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f464])).

fof(f464,plain,
    ( spl8_6
  <=> ! [X4] :
        ( ~ m1_subset_1(X4,u1_pre_topc(sK0))
        | v2_tex_2(X4,sK0)
        | m1_subset_1(sK3(sK0,X4),u1_pre_topc(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f2831,plain,
    ( v3_pre_topc(sK3(sK0,sK1),sK0)
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_12 ),
    inference(unit_resulting_resolution,[],[f2681,f2740,f2609])).

fof(f2609,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,u1_pre_topc(sK0))
        | v3_pre_topc(X0,sK0) )
    | ~ spl8_2 ),
    inference(backward_demodulation,[],[f2606,f146])).

fof(f146,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_pre_topc(sK0))
      | ~ m1_subset_1(X0,k9_setfam_1(sK1))
      | v3_pre_topc(X0,sK0) ) ),
    inference(forward_demodulation,[],[f140,f71])).

fof(f140,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,u1_pre_topc(sK0))
      | v3_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f73,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0) ) ),
    inference(definition_unfolding,[],[f89,f94])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f2740,plain,
    ( r2_hidden(sK3(sK0,sK1),u1_pre_topc(sK0))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | ~ spl8_12 ),
    inference(unit_resulting_resolution,[],[f2681,f2731,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
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
    file('/export/starexec/sandbox/benchmark/tex_2__t27_tex_2.p',t2_subset)).

fof(f2731,plain,
    ( ~ v1_xboole_0(u1_pre_topc(sK0))
    | ~ spl8_2
    | ~ spl8_12 ),
    inference(unit_resulting_resolution,[],[f2608,f2721,f135])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k9_setfam_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f108,f94])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
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
    file('/export/starexec/sandbox/benchmark/tex_2__t27_tex_2.p',t5_subset)).

fof(f2721,plain,
    ( r2_hidden(sK5(u1_pre_topc(sK0)),u1_pre_topc(sK0))
    | ~ spl8_2
    | ~ spl8_12 ),
    inference(unit_resulting_resolution,[],[f2678,f88,f2610])).

fof(f2610,plain,
    ( ! [X1] :
        ( ~ v3_pre_topc(X1,sK0)
        | ~ m1_subset_1(X1,u1_pre_topc(sK0))
        | r2_hidden(X1,u1_pre_topc(sK0)) )
    | ~ spl8_2 ),
    inference(backward_demodulation,[],[f2606,f147])).

fof(f88,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t27_tex_2.p',existence_m1_subset_1)).

fof(f2678,plain,
    ( v3_pre_topc(sK5(u1_pre_topc(sK0)),sK0)
    | ~ spl8_2
    | ~ spl8_12 ),
    inference(forward_demodulation,[],[f2677,f2606])).

fof(f2677,plain,
    ( v3_pre_topc(sK5(k9_setfam_1(sK1)),sK0)
    | ~ spl8_2
    | ~ spl8_12 ),
    inference(forward_demodulation,[],[f2675,f71])).

fof(f2675,plain,
    ( v3_pre_topc(sK5(k9_setfam_1(u1_struct_0(sK0))),sK0)
    | ~ spl8_2
    | ~ spl8_12 ),
    inference(unit_resulting_resolution,[],[f184,f73,f88,f834,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | v3_pre_topc(X1,X0)
      | ~ v1_tdlat_3(X0) ) ),
    inference(definition_unfolding,[],[f74,f94])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X1,X0)
      | ~ v1_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t27_tex_2.p',t17_tdlat_3)).

fof(f834,plain,
    ( v2_pre_topc(sK0)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f833])).

fof(f833,plain,
    ( spl8_12
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f2608,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k9_setfam_1(u1_pre_topc(sK0)))
    | ~ spl8_2 ),
    inference(backward_demodulation,[],[f2606,f145])).

fof(f3316,plain,
    ( ~ spl8_2
    | spl8_31 ),
    inference(avatar_contradiction_clause,[],[f3304])).

fof(f3304,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_31 ),
    inference(unit_resulting_resolution,[],[f137,f3297,f2682])).

fof(f2682,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,u1_pre_topc(sK0))
        | ~ r1_tarski(X0,sK1) )
    | ~ spl8_2 ),
    inference(superposition,[],[f134,f2606])).

fof(f134,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k9_setfam_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f99,f94])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f3297,plain,
    ( ~ m1_subset_1(sK1,u1_pre_topc(sK0))
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f3296])).

fof(f3296,plain,
    ( spl8_31
  <=> ~ m1_subset_1(sK1,u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f137,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f3301,plain,
    ( ~ spl8_31
    | spl8_32
    | spl8_1
    | ~ spl8_2
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f2872,f1268,f183,f174,f3299,f3296])).

fof(f1268,plain,
    ( spl8_20
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k9_setfam_1(sK1))
        | v2_tex_2(X0,sK0)
        | ~ v3_pre_topc(X1,sK0)
        | k9_subset_1(sK1,X0,X1) != sK3(sK0,X0)
        | ~ m1_subset_1(X0,k9_setfam_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f2872,plain,
    ( ! [X0] :
        ( k3_xboole_0(X0,sK1) != sK3(sK0,sK1)
        | ~ m1_subset_1(sK1,u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,u1_pre_topc(sK0))
        | ~ v3_pre_topc(X0,sK0) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f2866,f172])).

fof(f172,plain,(
    ! [X0] : k3_xboole_0(X0,sK1) = k9_subset_1(sK1,sK1,X0) ),
    inference(forward_demodulation,[],[f165,f166])).

fof(f165,plain,(
    ! [X0] : k9_subset_1(sK1,X0,sK1) = k9_subset_1(sK1,sK1,X0) ),
    inference(unit_resulting_resolution,[],[f138,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k9_setfam_1(X0)) ) ),
    inference(definition_unfolding,[],[f95,f94])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t27_tex_2.p',commutativity_k9_subset_1)).

fof(f2866,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,u1_pre_topc(sK0))
        | ~ m1_subset_1(X0,u1_pre_topc(sK0))
        | ~ v3_pre_topc(X0,sK0)
        | k9_subset_1(sK1,sK1,X0) != sK3(sK0,sK1) )
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_20 ),
    inference(resolution,[],[f1810,f175])).

fof(f1810,plain,
    ( ! [X0,X1] :
        ( v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,u1_pre_topc(sK0))
        | ~ m1_subset_1(X1,u1_pre_topc(sK0))
        | ~ v3_pre_topc(X1,sK0)
        | k9_subset_1(sK1,X0,X1) != sK3(sK0,X0) )
    | ~ spl8_2
    | ~ spl8_20 ),
    inference(forward_demodulation,[],[f1795,f1745])).

fof(f1745,plain,
    ( u1_pre_topc(sK0) = k9_setfam_1(sK1)
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f1741,f71])).

fof(f1741,plain,
    ( u1_pre_topc(sK0) = k9_setfam_1(u1_struct_0(sK0))
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f73,f184,f78])).

fof(f1795,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_pre_topc(sK0))
        | v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X1,k9_setfam_1(sK1))
        | ~ v3_pre_topc(X1,sK0)
        | k9_subset_1(sK1,X0,X1) != sK3(sK0,X0) )
    | ~ spl8_2
    | ~ spl8_20 ),
    inference(backward_demodulation,[],[f1745,f1269])).

fof(f1269,plain,
    ( ! [X0,X1] :
        ( v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X1,k9_setfam_1(sK1))
        | ~ v3_pre_topc(X1,sK0)
        | k9_subset_1(sK1,X0,X1) != sK3(sK0,X0)
        | ~ m1_subset_1(X0,k9_setfam_1(sK1)) )
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f1268])).

fof(f1744,plain,
    ( ~ spl8_2
    | spl8_13 ),
    inference(avatar_contradiction_clause,[],[f1740])).

fof(f1740,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_13 ),
    inference(unit_resulting_resolution,[],[f837,f73,f184,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t27_tex_2.p',cc1_tdlat_3)).

fof(f837,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f836])).

fof(f836,plain,
    ( spl8_13
  <=> ~ v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f1737,plain,
    ( ~ spl8_23
    | spl8_26
    | ~ spl8_0 ),
    inference(avatar_split_clause,[],[f1100,f177,f1735,f1409])).

fof(f1409,plain,
    ( spl8_23
  <=> ~ m1_subset_1(sK1,k9_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f1100,plain,
    ( ! [X0] :
        ( k3_xboole_0(sK1,sK4(sK0,sK1,X0)) = X0
        | ~ m1_subset_1(X0,k9_setfam_1(sK1))
        | ~ m1_subset_1(sK1,k9_setfam_1(sK1))
        | ~ r1_tarski(X0,sK1) )
    | ~ spl8_0 ),
    inference(forward_demodulation,[],[f1099,f112])).

fof(f1099,plain,
    ( ! [X0] :
        ( k3_xboole_0(sK4(sK0,sK1,X0),sK1) = X0
        | ~ m1_subset_1(X0,k9_setfam_1(sK1))
        | ~ m1_subset_1(sK1,k9_setfam_1(sK1))
        | ~ r1_tarski(X0,sK1) )
    | ~ spl8_0 ),
    inference(forward_demodulation,[],[f1091,f172])).

fof(f1091,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k9_setfam_1(sK1))
        | ~ m1_subset_1(sK1,k9_setfam_1(sK1))
        | ~ r1_tarski(X0,sK1)
        | k9_subset_1(sK1,sK1,sK4(sK0,sK1,X0)) = X0 )
    | ~ spl8_0 ),
    inference(resolution,[],[f152,f178])).

fof(f152,plain,(
    ! [X4,X5] :
      ( ~ v2_tex_2(X4,sK0)
      | ~ m1_subset_1(X5,k9_setfam_1(sK1))
      | ~ m1_subset_1(X4,k9_setfam_1(sK1))
      | ~ r1_tarski(X5,X4)
      | k9_subset_1(sK1,X4,sK4(sK0,X4,X5)) = X5 ) ),
    inference(forward_demodulation,[],[f151,f71])).

fof(f151,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,k9_setfam_1(sK1))
      | ~ m1_subset_1(X4,k9_setfam_1(sK1))
      | ~ r1_tarski(X5,X4)
      | k9_subset_1(u1_struct_0(sK0),X4,sK4(sK0,X4,X5)) = X5
      | ~ v2_tex_2(X4,sK0) ) ),
    inference(forward_demodulation,[],[f150,f71])).

fof(f150,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k9_setfam_1(sK1))
      | ~ m1_subset_1(X5,k9_setfam_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X5,X4)
      | k9_subset_1(u1_struct_0(sK0),X4,sK4(sK0,X4,X5)) = X5
      | ~ v2_tex_2(X4,sK0) ) ),
    inference(forward_demodulation,[],[f143,f71])).

fof(f143,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k9_setfam_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X5,k9_setfam_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X5,X4)
      | k9_subset_1(u1_struct_0(sK0),X4,sK4(sK0,X4,X5)) = X5
      | ~ v2_tex_2(X4,sK0) ) ),
    inference(resolution,[],[f73,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X2)) = X2
      | ~ v2_tex_2(X1,X0) ) ),
    inference(definition_unfolding,[],[f83,f94,f94])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | k9_subset_1(u1_struct_0(X0),X1,sK4(X0,X1,X2)) = X2
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f1433,plain,(
    spl8_23 ),
    inference(avatar_contradiction_clause,[],[f1417])).

fof(f1417,plain,
    ( $false
    | ~ spl8_23 ),
    inference(unit_resulting_resolution,[],[f137,f1410,f134])).

fof(f1410,plain,
    ( ~ m1_subset_1(sK1,k9_setfam_1(sK1))
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f1409])).

fof(f1270,plain,
    ( ~ spl8_5
    | spl8_20 ),
    inference(avatar_split_clause,[],[f161,f1268,f461])).

fof(f461,plain,
    ( spl8_5
  <=> ~ l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f161,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k9_setfam_1(sK1))
      | ~ m1_subset_1(X0,k9_setfam_1(sK1))
      | k9_subset_1(sK1,X0,X1) != sK3(sK0,X0)
      | ~ v3_pre_topc(X1,sK0)
      | ~ l1_pre_topc(sK0)
      | v2_tex_2(X0,sK0) ) ),
    inference(forward_demodulation,[],[f160,f71])).

fof(f160,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k9_setfam_1(sK1))
      | k9_subset_1(sK1,X0,X1) != sK3(sK0,X0)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0)
      | ~ l1_pre_topc(sK0)
      | v2_tex_2(X0,sK0) ) ),
    inference(forward_demodulation,[],[f155,f71])).

fof(f155,plain,(
    ! [X0,X1] :
      ( k9_subset_1(sK1,X0,X1) != sK3(sK0,X0)
      | ~ m1_subset_1(X0,k9_setfam_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0)
      | ~ l1_pre_topc(sK0)
      | v2_tex_2(X0,sK0) ) ),
    inference(superposition,[],[f123,f71])).

fof(f123,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK3(X0,X1)
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k9_setfam_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | ~ l1_pre_topc(X0)
      | v2_tex_2(X1,X0) ) ),
    inference(definition_unfolding,[],[f80,f94,f94])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK3(X0,X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f1144,plain,
    ( ~ spl8_5
    | spl8_18 ),
    inference(avatar_split_clause,[],[f163,f1142,f461])).

fof(f163,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k9_setfam_1(sK1))
      | ~ m1_subset_1(X2,k9_setfam_1(sK1))
      | m1_subset_1(sK4(sK0,X2,X3),k9_setfam_1(sK1))
      | ~ r1_tarski(X3,X2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_tex_2(X2,sK0) ) ),
    inference(forward_demodulation,[],[f162,f71])).

fof(f162,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,k9_setfam_1(sK1))
      | m1_subset_1(sK4(sK0,X2,X3),k9_setfam_1(sK1))
      | ~ m1_subset_1(X3,k9_setfam_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X3,X2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_tex_2(X2,sK0) ) ),
    inference(forward_demodulation,[],[f156,f71])).

fof(f156,plain,(
    ! [X2,X3] :
      ( m1_subset_1(sK4(sK0,X2,X3),k9_setfam_1(sK1))
      | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,k9_setfam_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X3,X2)
      | ~ l1_pre_topc(sK0)
      | ~ v2_tex_2(X2,sK0) ) ),
    inference(superposition,[],[f122,f71])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k9_setfam_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k9_setfam_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(definition_unfolding,[],[f81,f94,f94,f94])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f689,plain,
    ( spl8_2
    | ~ spl8_5
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f158,f687,f461,f183])).

fof(f158,plain,
    ( u1_pre_topc(sK0) != k9_setfam_1(sK1)
    | ~ l1_pre_topc(sK0)
    | v1_tdlat_3(sK0) ),
    inference(superposition,[],[f77,f71])).

fof(f77,plain,(
    ! [X0] :
      ( u1_pre_topc(X0) != k9_setfam_1(u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v1_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f470,plain,(
    spl8_5 ),
    inference(avatar_contradiction_clause,[],[f467])).

fof(f467,plain,
    ( $false
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f73,f462])).

fof(f462,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f461])).

fof(f466,plain,
    ( ~ spl8_5
    | spl8_6
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f210,f183,f464,f461])).

fof(f210,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_pre_topc(sK0))
        | m1_subset_1(sK3(sK0,X4),u1_pre_topc(sK0))
        | ~ l1_pre_topc(sK0)
        | v2_tex_2(X4,sK0) )
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f202,f190])).

fof(f190,plain,
    ( u1_pre_topc(sK0) = k9_setfam_1(sK1)
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f187,f71])).

fof(f187,plain,
    ( u1_pre_topc(sK0) = k9_setfam_1(u1_struct_0(sK0))
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f73,f184,f78])).

fof(f202,plain,
    ( ! [X4] :
        ( m1_subset_1(sK3(sK0,X4),u1_pre_topc(sK0))
        | ~ m1_subset_1(X4,k9_setfam_1(sK1))
        | ~ l1_pre_topc(sK0)
        | v2_tex_2(X4,sK0) )
    | ~ spl8_2 ),
    inference(backward_demodulation,[],[f190,f164])).

fof(f164,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k9_setfam_1(sK1))
      | m1_subset_1(sK3(sK0,X4),k9_setfam_1(sK1))
      | ~ l1_pre_topc(sK0)
      | v2_tex_2(X4,sK0) ) ),
    inference(forward_demodulation,[],[f157,f71])).

fof(f157,plain,(
    ! [X4] :
      ( m1_subset_1(sK3(sK0,X4),k9_setfam_1(sK1))
      | ~ m1_subset_1(X4,k9_setfam_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | v2_tex_2(X4,sK0) ) ),
    inference(superposition,[],[f119,f71])).

fof(f119,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),k9_setfam_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k9_setfam_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_tex_2(X1,X0) ) ),
    inference(definition_unfolding,[],[f84,f94,f94])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f218,plain,
    ( ~ spl8_1
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f69,f180,f174])).

fof(f180,plain,
    ( spl8_3
  <=> ~ v1_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f69,plain,
    ( ~ v1_tdlat_3(sK0)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f185,plain,
    ( spl8_0
    | spl8_2 ),
    inference(avatar_split_clause,[],[f68,f183,f177])).

fof(f68,plain,
    ( v1_tdlat_3(sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
