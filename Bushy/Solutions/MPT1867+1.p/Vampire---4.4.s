%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t35_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:31 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 172 expanded)
%              Number of leaves         :   19 (  63 expanded)
%              Depth                    :   12
%              Number of atoms          :  288 ( 542 expanded)
%              Number of equality atoms :   26 (  39 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f277,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f101,f105,f109,f119,f129,f158,f170,f241,f250,f268,f276])).

fof(f276,plain,
    ( ~ spl8_0
    | spl8_25
    | ~ spl8_32 ),
    inference(avatar_contradiction_clause,[],[f275])).

fof(f275,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_25
    | ~ spl8_32 ),
    inference(subsumption_resolution,[],[f273,f240])).

fof(f240,plain,
    ( sK1 != sK2(sK0,sK1)
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl8_25
  <=> sK1 != sK2(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f273,plain,
    ( sK1 = sK2(sK0,sK1)
    | ~ spl8_0
    | ~ spl8_32 ),
    inference(resolution,[],[f267,f110])).

fof(f110,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK1 = X0 )
    | ~ spl8_0 ),
    inference(resolution,[],[f100,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t35_tex_2.p',t8_boole)).

fof(f100,plain,
    ( v1_xboole_0(sK1)
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl8_0
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f267,plain,
    ( v1_xboole_0(sK2(sK0,sK1))
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f266])).

fof(f266,plain,
    ( spl8_32
  <=> v1_xboole_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f268,plain,
    ( spl8_32
    | ~ spl8_0
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f262,f248,f99,f266])).

fof(f248,plain,
    ( spl8_28
  <=> m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f262,plain,
    ( v1_xboole_0(sK2(sK0,sK1))
    | ~ spl8_0
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f259,f100])).

fof(f259,plain,
    ( ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK2(sK0,sK1))
    | ~ spl8_28 ),
    inference(resolution,[],[f249,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t35_tex_2.p',cc1_subset_1)).

fof(f249,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f248])).

fof(f250,plain,
    ( spl8_28
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f173,f168,f248])).

fof(f168,plain,
    ( spl8_18
  <=> r1_tarski(sK2(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f173,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl8_18 ),
    inference(resolution,[],[f169,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t35_tex_2.p',t3_subset)).

fof(f169,plain,
    ( r1_tarski(sK2(sK0,sK1),sK1)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f168])).

fof(f241,plain,
    ( ~ spl8_25
    | ~ spl8_0
    | ~ spl8_4
    | spl8_9
    | ~ spl8_12
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f228,f156,f127,f117,f107,f99,f239])).

fof(f107,plain,
    ( spl8_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f117,plain,
    ( spl8_9
  <=> ~ v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f127,plain,
    ( spl8_12
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f156,plain,
    ( spl8_14
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f228,plain,
    ( sK1 != sK2(sK0,sK1)
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_14 ),
    inference(forward_demodulation,[],[f227,f96])).

fof(f96,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t35_tex_2.p',idempotence_k3_xboole_0)).

fof(f227,plain,
    ( k3_xboole_0(sK1,sK1) != sK2(sK0,sK1)
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_14 ),
    inference(forward_demodulation,[],[f226,f187])).

fof(f187,plain,
    ( ! [X14,X15] : k3_xboole_0(X14,sK1) = k9_subset_1(X15,X14,sK1)
    | ~ spl8_0 ),
    inference(resolution,[],[f171,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t35_tex_2.p',redefinition_k9_subset_1)).

fof(f171,plain,
    ( ! [X0] : m1_subset_1(sK1,k1_zfmisc_1(X0))
    | ~ spl8_0 ),
    inference(superposition,[],[f72,f164])).

fof(f164,plain,
    ( ! [X0] : sK1 = sK4(X0)
    | ~ spl8_0 ),
    inference(resolution,[],[f110,f73])).

fof(f73,plain,(
    ! [X0] : v1_xboole_0(sK4(X0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t35_tex_2.p',rc2_subset_1)).

fof(f72,plain,(
    ! [X0] : m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f226,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK1) != sK2(sK0,sK1)
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_9
    | ~ spl8_12
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f222,f157])).

fof(f157,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f156])).

fof(f222,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | k9_subset_1(u1_struct_0(sK0),sK1,sK1) != sK2(sK0,sK1)
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_9
    | ~ spl8_12 ),
    inference(resolution,[],[f146,f171])).

fof(f146,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | k9_subset_1(u1_struct_0(sK0),sK1,X0) != sK2(sK0,sK1) )
    | ~ spl8_4
    | ~ spl8_9
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f145,f118])).

fof(f118,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f117])).

fof(f145,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | k9_subset_1(u1_struct_0(sK0),sK1,X0) != sK2(sK0,sK1)
        | v2_tex_2(sK1,sK0) )
    | ~ spl8_4
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f131,f108])).

fof(f108,plain,
    ( l1_pre_topc(sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | k9_subset_1(u1_struct_0(sK0),sK1,X0) != sK2(sK0,sK1)
        | v2_tex_2(sK1,sK0) )
    | ~ spl8_12 ),
    inference(resolution,[],[f128,f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/tex_2__t35_tex_2.p',d5_tex_2)).

fof(f128,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f127])).

fof(f170,plain,
    ( spl8_18
    | ~ spl8_4
    | spl8_9
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f150,f127,f117,f107,f168])).

fof(f150,plain,
    ( r1_tarski(sK2(sK0,sK1),sK1)
    | ~ spl8_4
    | ~ spl8_9
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f149,f118])).

fof(f149,plain,
    ( r1_tarski(sK2(sK0,sK1),sK1)
    | v2_tex_2(sK1,sK0)
    | ~ spl8_4
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f136,f108])).

fof(f136,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(sK2(sK0,sK1),sK1)
    | v2_tex_2(sK1,sK0)
    | ~ spl8_12 ),
    inference(resolution,[],[f128,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(sK2(X0,X1),X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f158,plain,
    ( spl8_14
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f153,f127,f107,f103,f99,f156])).

fof(f103,plain,
    ( spl8_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f153,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl8_0
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f152,f100])).

fof(f152,plain,
    ( ~ v1_xboole_0(sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f151,f104])).

fof(f104,plain,
    ( v2_pre_topc(sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f151,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v1_xboole_0(sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ spl8_4
    | ~ spl8_12 ),
    inference(subsumption_resolution,[],[f137,f108])).

fof(f137,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v1_xboole_0(sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ spl8_12 ),
    inference(resolution,[],[f128,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t35_tex_2.p',cc1_tops_1)).

fof(f129,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f62,f127])).

fof(f62,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tex_2__t35_tex_2.p',t35_tex_2)).

fof(f119,plain,(
    ~ spl8_9 ),
    inference(avatar_split_clause,[],[f63,f117])).

fof(f63,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f109,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f65,f107])).

fof(f65,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f105,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f64,f103])).

fof(f64,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f101,plain,(
    spl8_0 ),
    inference(avatar_split_clause,[],[f61,f99])).

fof(f61,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
