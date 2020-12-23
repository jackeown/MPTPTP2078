%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:03 EST 2020

% Result     : Theorem 1.82s
% Output     : Refutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 496 expanded)
%              Number of leaves         :   39 ( 194 expanded)
%              Depth                    :   13
%              Number of atoms          :  661 (2354 expanded)
%              Number of equality atoms :   68 ( 143 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f564,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f109,f114,f119,f124,f129,f138,f197,f268,f285,f286,f306,f344,f345,f357,f400,f484,f555])).

fof(f555,plain,
    ( ~ spl4_6
    | spl4_12
    | ~ spl4_13
    | ~ spl4_18 ),
    inference(avatar_contradiction_clause,[],[f554])).

fof(f554,plain,
    ( $false
    | ~ spl4_6
    | spl4_12
    | ~ spl4_13
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f544,f373])).

fof(f373,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f223,f148])).

fof(f148,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK3(X0))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f72,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f72,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f223,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(k1_xboole_0,X1),X0) ),
    inference(superposition,[],[f168,f156])).

fof(f156,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f152,f87])).

fof(f87,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f59,f85])).

fof(f85,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f77,f79])).

fof(f79,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f77,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f59,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f152,plain,(
    ! [X0] : k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0)) = k6_subset_1(X0,X0) ),
    inference(superposition,[],[f90,f88])).

fof(f88,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f60,f76])).

fof(f76,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f60,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f90,plain,(
    ! [X0,X1] : k1_setfam_1(k1_enumset1(X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(definition_unfolding,[],[f80,f76,f76,f85])).

fof(f80,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f168,plain,(
    ! [X6,X8,X7] : r1_tarski(k6_subset_1(k6_subset_1(X6,X7),X8),X6) ),
    inference(superposition,[],[f89,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] : k6_subset_1(k6_subset_1(X0,X1),X2) = k6_subset_1(X0,k3_tarski(k1_enumset1(X1,X1,X2))) ),
    inference(definition_unfolding,[],[f84,f76,f76,f76,f86])).

fof(f86,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f78,f79])).

fof(f78,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f84,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f89,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(definition_unfolding,[],[f75,f76])).

fof(f75,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f544,plain,
    ( k1_xboole_0 != k6_subset_1(k1_xboole_0,sK1)
    | ~ spl4_6
    | spl4_12
    | ~ spl4_13
    | ~ spl4_18 ),
    inference(backward_demodulation,[],[f346,f535])).

fof(f535,plain,
    ( k1_xboole_0 = sK2(sK0,sK1)
    | ~ spl4_6
    | ~ spl4_18 ),
    inference(unit_resulting_resolution,[],[f123,f483,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f483,plain,
    ( v1_xboole_0(sK2(sK0,sK1))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f481])).

fof(f481,plain,
    ( spl4_18
  <=> v1_xboole_0(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f123,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl4_6
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f346,plain,
    ( k1_xboole_0 != k6_subset_1(sK2(sK0,sK1),sK1)
    | spl4_12
    | ~ spl4_13 ),
    inference(unit_resulting_resolution,[],[f196,f256,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k6_subset_1(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( k1_xboole_0 = k6_subset_1(X1,X0)
        & X0 != X1
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l48_tex_2)).

fof(f256,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f254])).

fof(f254,plain,
    ( spl4_13
  <=> r1_tarski(sK1,sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f196,plain,
    ( sK1 != sK2(sK0,sK1)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl4_12
  <=> sK1 = sK2(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f484,plain,
    ( spl4_18
    | spl4_5
    | spl4_12
    | ~ spl4_13
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f437,f397,f254,f194,f116,f481])).

fof(f116,plain,
    ( spl4_5
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f397,plain,
    ( spl4_17
  <=> v1_zfmisc_1(sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f437,plain,
    ( v1_xboole_0(sK2(sK0,sK1))
    | spl4_5
    | spl4_12
    | ~ spl4_13
    | ~ spl4_17 ),
    inference(unit_resulting_resolution,[],[f118,f196,f256,f399,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | ~ r1_tarski(X0,X1)
      | X0 = X1
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f399,plain,
    ( v1_zfmisc_1(sK2(sK0,sK1))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f397])).

fof(f118,plain,
    ( ~ v1_xboole_0(sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f116])).

fof(f400,plain,
    ( spl4_17
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_14
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f361,f354,f341,f111,f106,f96,f397])).

fof(f96,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f106,plain,
    ( spl4_3
  <=> v2_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f111,plain,
    ( spl4_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f341,plain,
    ( spl4_14
  <=> v2_tex_2(sK2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f354,plain,
    ( spl4_16
  <=> m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f361,plain,
    ( v1_zfmisc_1(sK2(sK0,sK1))
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_14
    | ~ spl4_16 ),
    inference(unit_resulting_resolution,[],[f98,f108,f113,f343,f356,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ v2_tdlat_3(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_zfmisc_1(X1)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f93,f69])).

fof(f69,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).

fof(f93,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f70,f62])).

fof(f62,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ~ v1_zfmisc_1(X1) )
            & ( v1_zfmisc_1(X1)
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

fof(f356,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f354])).

fof(f343,plain,
    ( v2_tex_2(sK2(sK0,sK1),sK0)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f341])).

fof(f113,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f111])).

fof(f108,plain,
    ( v2_tdlat_3(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f106])).

fof(f98,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f357,plain,
    ( spl4_16
    | ~ spl4_4
    | ~ spl4_7
    | spl4_8
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f311,f180,f131,f126,f111,f354])).

fof(f126,plain,
    ( spl4_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f131,plain,
    ( spl4_8
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f180,plain,
    ( spl4_11
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f311,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4
    | ~ spl4_7
    | spl4_8
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f113,f132,f128,f182,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK2(X0,X1) != X1
                & r1_tarski(X1,sK2(X0,X1))
                & v2_tex_2(sK2(X0,X1),X0)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f44,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK2(X0,X1) != X1
        & r1_tarski(X1,sK2(X0,X1))
        & v2_tex_2(sK2(X0,X1),X0)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(f182,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f180])).

fof(f128,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f126])).

fof(f132,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f131])).

fof(f345,plain,
    ( spl4_13
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f284,f180,f135,f126,f116,f111,f106,f96,f254])).

fof(f135,plain,
    ( spl4_9
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f284,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f283,f280])).

fof(f280,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f57,f189])).

fof(f189,plain,
    ( v1_zfmisc_1(sK1)
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f98,f113,f108,f128,f182,f94])).

fof(f57,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ( ~ v1_zfmisc_1(sK1)
      | ~ v3_tex_2(sK1,sK0) )
    & ( v1_zfmisc_1(sK1)
      | v3_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & ~ v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & v2_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_zfmisc_1(X1)
              | ~ v3_tex_2(X1,X0) )
            & ( v1_zfmisc_1(X1)
              | v3_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,sK0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK0)
      & v2_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X1] :
        ( ( ~ v1_zfmisc_1(X1)
          | ~ v3_tex_2(X1,sK0) )
        & ( v1_zfmisc_1(X1)
          | v3_tex_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & ~ v1_xboole_0(X1) )
   => ( ( ~ v1_zfmisc_1(sK1)
        | ~ v3_tex_2(sK1,sK0) )
      & ( v1_zfmisc_1(sK1)
        | v3_tex_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v3_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v3_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tex_2)).

fof(f283,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | v3_tex_2(sK1,sK0)
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f244,f239])).

fof(f239,plain,
    ( v2_tex_2(sK1,sK0)
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f137,f118,f128,f178])).

fof(f178,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_zfmisc_1(X0)
        | v1_xboole_0(X0)
        | v2_tex_2(X0,sK0) )
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f177,f98])).

fof(f177,plain,
    ( ! [X0] :
        ( ~ v1_zfmisc_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | v2_tex_2(X0,sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f176,f113])).

fof(f176,plain,
    ( ! [X0] :
        ( ~ v1_zfmisc_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | ~ l1_pre_topc(sK0)
        | v2_tex_2(X0,sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f92,f108])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v2_tdlat_3(X0)
      | ~ v1_zfmisc_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_tex_2(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f71,f62])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v1_zfmisc_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f137,plain,
    ( v1_zfmisc_1(sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f135])).

fof(f244,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | r1_tarski(sK1,sK2(sK0,sK1))
    | v3_tex_2(sK1,sK0)
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(resolution,[],[f173,f128])).

fof(f173,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_tex_2(X0,sK0)
        | r1_tarski(X0,sK2(sK0,X0))
        | v3_tex_2(X0,sK0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f67,f113])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | r1_tarski(X1,sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f344,plain,
    ( spl4_14
    | ~ spl4_4
    | ~ spl4_7
    | spl4_8
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f188,f180,f131,f126,f111,f341])).

fof(f188,plain,
    ( v2_tex_2(sK2(sK0,sK1),sK0)
    | ~ spl4_4
    | ~ spl4_7
    | spl4_8
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f113,f132,f128,f182,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_tex_2(sK2(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f306,plain,
    ( spl4_11
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f239,f135,f126,f116,f111,f106,f96,f180])).

fof(f286,plain,
    ( spl4_9
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f189,f180,f126,f111,f106,f96,f135])).

fof(f285,plain,
    ( ~ spl4_8
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f280,f180,f126,f111,f106,f96,f131])).

fof(f268,plain,
    ( ~ spl4_4
    | ~ spl4_7
    | ~ spl4_8
    | spl4_11 ),
    inference(avatar_contradiction_clause,[],[f267])).

fof(f267,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_8
    | spl4_11 ),
    inference(subsumption_resolution,[],[f263,f181])).

fof(f181,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f180])).

fof(f263,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl4_4
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f128,f133,f165])).

fof(f165,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_tex_2(X0,sK0)
        | v2_tex_2(X0,sK0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f63,f113])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f133,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f131])).

fof(f197,plain,
    ( ~ spl4_12
    | ~ spl4_4
    | ~ spl4_7
    | spl4_8
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f186,f180,f131,f126,f111,f194])).

fof(f186,plain,
    ( sK1 != sK2(sK0,sK1)
    | ~ spl4_4
    | ~ spl4_7
    | spl4_8
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f113,f132,f128,f182,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | sK2(X0,X1) != X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f138,plain,
    ( spl4_8
    | spl4_9 ),
    inference(avatar_split_clause,[],[f56,f135,f131])).

fof(f56,plain,
    ( v1_zfmisc_1(sK1)
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f129,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f55,f126])).

fof(f55,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f124,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f58,f121])).

fof(f58,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f119,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f54,f116])).

fof(f54,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f114,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f53,f111])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f109,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f52,f106])).

fof(f52,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f99,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f50,f96])).

fof(f50,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:25:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (25108)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.51  % (25084)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (25101)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.52  % (25090)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (25097)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (25102)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.52  % (25085)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (25093)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (25084)Refutation not found, incomplete strategy% (25084)------------------------------
% 0.21/0.53  % (25084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (25093)Refutation not found, incomplete strategy% (25093)------------------------------
% 0.21/0.54  % (25093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (25109)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (25086)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (25099)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (25105)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (25087)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (25083)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (25091)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (25106)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (25093)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (25093)Memory used [KB]: 10746
% 0.21/0.54  % (25093)Time elapsed: 0.130 s
% 0.21/0.54  % (25093)------------------------------
% 0.21/0.54  % (25093)------------------------------
% 0.21/0.55  % (25084)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (25084)Memory used [KB]: 1791
% 0.21/0.55  % (25084)Time elapsed: 0.119 s
% 0.21/0.55  % (25084)------------------------------
% 0.21/0.55  % (25084)------------------------------
% 0.21/0.55  % (25104)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (25098)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (25112)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (25112)Refutation not found, incomplete strategy% (25112)------------------------------
% 0.21/0.55  % (25112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (25112)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (25112)Memory used [KB]: 1791
% 0.21/0.55  % (25112)Time elapsed: 0.129 s
% 0.21/0.55  % (25112)------------------------------
% 0.21/0.55  % (25112)------------------------------
% 0.21/0.55  % (25094)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (25111)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (25107)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (25092)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.56  % (25099)Refutation not found, incomplete strategy% (25099)------------------------------
% 0.21/0.56  % (25099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (25099)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (25099)Memory used [KB]: 10746
% 0.21/0.56  % (25099)Time elapsed: 0.149 s
% 0.21/0.56  % (25099)------------------------------
% 0.21/0.56  % (25099)------------------------------
% 0.21/0.56  % (25097)Refutation not found, incomplete strategy% (25097)------------------------------
% 0.21/0.56  % (25097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (25097)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (25097)Memory used [KB]: 1791
% 0.21/0.56  % (25097)Time elapsed: 0.126 s
% 0.21/0.56  % (25097)------------------------------
% 0.21/0.56  % (25097)------------------------------
% 0.21/0.56  % (25109)Refutation not found, incomplete strategy% (25109)------------------------------
% 0.21/0.56  % (25109)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (25109)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (25109)Memory used [KB]: 6396
% 0.21/0.56  % (25109)Time elapsed: 0.137 s
% 0.21/0.56  % (25109)------------------------------
% 0.21/0.56  % (25109)------------------------------
% 0.21/0.56  % (25089)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.57  % (25100)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.57  % (25096)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.57  % (25095)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.57  % (25111)Refutation not found, incomplete strategy% (25111)------------------------------
% 0.21/0.57  % (25111)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (25111)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (25111)Memory used [KB]: 10746
% 0.21/0.57  % (25111)Time elapsed: 0.122 s
% 0.21/0.57  % (25111)------------------------------
% 0.21/0.57  % (25111)------------------------------
% 0.21/0.57  % (25088)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.57  % (25103)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.58  % (25110)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.82/0.63  % (25103)Refutation found. Thanks to Tanya!
% 1.82/0.63  % SZS status Theorem for theBenchmark
% 1.82/0.63  % SZS output start Proof for theBenchmark
% 1.82/0.63  fof(f564,plain,(
% 1.82/0.63    $false),
% 1.82/0.63    inference(avatar_sat_refutation,[],[f99,f109,f114,f119,f124,f129,f138,f197,f268,f285,f286,f306,f344,f345,f357,f400,f484,f555])).
% 1.82/0.63  fof(f555,plain,(
% 1.82/0.63    ~spl4_6 | spl4_12 | ~spl4_13 | ~spl4_18),
% 1.82/0.63    inference(avatar_contradiction_clause,[],[f554])).
% 1.82/0.63  fof(f554,plain,(
% 1.82/0.63    $false | (~spl4_6 | spl4_12 | ~spl4_13 | ~spl4_18)),
% 1.82/0.63    inference(subsumption_resolution,[],[f544,f373])).
% 1.82/0.63  fof(f373,plain,(
% 1.82/0.63    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k1_xboole_0,X0)) )),
% 1.82/0.63    inference(unit_resulting_resolution,[],[f223,f148])).
% 1.82/0.63  fof(f148,plain,(
% 1.82/0.63    ( ! [X0] : (~r1_tarski(X0,sK3(X0)) | k1_xboole_0 = X0) )),
% 1.82/0.63    inference(resolution,[],[f72,f82])).
% 1.82/0.63  fof(f82,plain,(
% 1.82/0.63    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.82/0.63    inference(cnf_transformation,[],[f35])).
% 1.82/0.63  fof(f35,plain,(
% 1.82/0.63    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.82/0.63    inference(ennf_transformation,[],[f13])).
% 1.82/0.63  fof(f13,axiom,(
% 1.82/0.63    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.82/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.82/0.63  fof(f72,plain,(
% 1.82/0.63    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.82/0.63    inference(cnf_transformation,[],[f49])).
% 1.82/0.63  fof(f49,plain,(
% 1.82/0.63    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)) | k1_xboole_0 = X0)),
% 1.82/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f48])).
% 1.82/0.63  fof(f48,plain,(
% 1.82/0.63    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)))),
% 1.82/0.63    introduced(choice_axiom,[])).
% 1.82/0.63  fof(f33,plain,(
% 1.82/0.63    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.82/0.63    inference(ennf_transformation,[],[f14])).
% 1.82/0.63  fof(f14,axiom,(
% 1.82/0.63    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.82/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).
% 1.82/0.63  fof(f223,plain,(
% 1.82/0.63    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k1_xboole_0,X1),X0)) )),
% 1.82/0.63    inference(superposition,[],[f168,f156])).
% 1.82/0.63  fof(f156,plain,(
% 1.82/0.63    ( ! [X0] : (k1_xboole_0 = k6_subset_1(X0,X0)) )),
% 1.82/0.63    inference(forward_demodulation,[],[f152,f87])).
% 1.82/0.63  fof(f87,plain,(
% 1.82/0.63    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0))) )),
% 1.82/0.63    inference(definition_unfolding,[],[f59,f85])).
% 1.82/0.63  fof(f85,plain,(
% 1.82/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 1.82/0.63    inference(definition_unfolding,[],[f77,f79])).
% 1.82/0.63  fof(f79,plain,(
% 1.82/0.63    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.82/0.63    inference(cnf_transformation,[],[f8])).
% 1.82/0.63  fof(f8,axiom,(
% 1.82/0.63    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.82/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.82/0.63  fof(f77,plain,(
% 1.82/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.82/0.63    inference(cnf_transformation,[],[f12])).
% 1.82/0.63  fof(f12,axiom,(
% 1.82/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.82/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.82/0.63  fof(f59,plain,(
% 1.82/0.63    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.82/0.63    inference(cnf_transformation,[],[f2])).
% 1.82/0.63  fof(f2,axiom,(
% 1.82/0.63    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.82/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.82/0.63  fof(f152,plain,(
% 1.82/0.63    ( ! [X0] : (k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0)) = k6_subset_1(X0,X0)) )),
% 1.82/0.63    inference(superposition,[],[f90,f88])).
% 1.82/0.63  fof(f88,plain,(
% 1.82/0.63    ( ! [X0] : (k6_subset_1(X0,k1_xboole_0) = X0) )),
% 1.82/0.63    inference(definition_unfolding,[],[f60,f76])).
% 1.82/0.63  fof(f76,plain,(
% 1.82/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.82/0.63    inference(cnf_transformation,[],[f11])).
% 1.82/0.63  fof(f11,axiom,(
% 1.82/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.82/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.82/0.63  fof(f60,plain,(
% 1.82/0.63    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.82/0.63    inference(cnf_transformation,[],[f4])).
% 1.82/0.63  fof(f4,axiom,(
% 1.82/0.63    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.82/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.82/0.63  fof(f90,plain,(
% 1.82/0.63    ( ! [X0,X1] : (k1_setfam_1(k1_enumset1(X0,X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1))) )),
% 1.82/0.63    inference(definition_unfolding,[],[f80,f76,f76,f85])).
% 1.82/0.63  fof(f80,plain,(
% 1.82/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.82/0.63    inference(cnf_transformation,[],[f6])).
% 1.82/0.63  fof(f6,axiom,(
% 1.82/0.63    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.82/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.82/0.63  fof(f168,plain,(
% 1.82/0.63    ( ! [X6,X8,X7] : (r1_tarski(k6_subset_1(k6_subset_1(X6,X7),X8),X6)) )),
% 1.82/0.63    inference(superposition,[],[f89,f91])).
% 1.82/0.63  fof(f91,plain,(
% 1.82/0.63    ( ! [X2,X0,X1] : (k6_subset_1(k6_subset_1(X0,X1),X2) = k6_subset_1(X0,k3_tarski(k1_enumset1(X1,X1,X2)))) )),
% 1.82/0.63    inference(definition_unfolding,[],[f84,f76,f76,f76,f86])).
% 1.82/0.63  fof(f86,plain,(
% 1.82/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 1.82/0.63    inference(definition_unfolding,[],[f78,f79])).
% 1.82/0.63  fof(f78,plain,(
% 1.82/0.63    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.82/0.63    inference(cnf_transformation,[],[f10])).
% 1.82/0.63  fof(f10,axiom,(
% 1.82/0.63    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.82/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.82/0.63  fof(f84,plain,(
% 1.82/0.63    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.82/0.63    inference(cnf_transformation,[],[f5])).
% 1.82/0.63  fof(f5,axiom,(
% 1.82/0.63    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.82/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.82/0.63  fof(f89,plain,(
% 1.82/0.63    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 1.82/0.63    inference(definition_unfolding,[],[f75,f76])).
% 1.82/0.63  fof(f75,plain,(
% 1.82/0.63    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.82/0.63    inference(cnf_transformation,[],[f3])).
% 1.82/0.63  fof(f3,axiom,(
% 1.82/0.63    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.82/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.82/0.63  fof(f544,plain,(
% 1.82/0.63    k1_xboole_0 != k6_subset_1(k1_xboole_0,sK1) | (~spl4_6 | spl4_12 | ~spl4_13 | ~spl4_18)),
% 1.82/0.63    inference(backward_demodulation,[],[f346,f535])).
% 1.82/0.63  fof(f535,plain,(
% 1.82/0.63    k1_xboole_0 = sK2(sK0,sK1) | (~spl4_6 | ~spl4_18)),
% 1.82/0.63    inference(unit_resulting_resolution,[],[f123,f483,f81])).
% 1.82/0.63  fof(f81,plain,(
% 1.82/0.63    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 1.82/0.63    inference(cnf_transformation,[],[f34])).
% 1.82/0.63  fof(f34,plain,(
% 1.82/0.63    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.82/0.63    inference(ennf_transformation,[],[f7])).
% 1.82/0.63  fof(f7,axiom,(
% 1.82/0.63    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.82/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 1.82/0.63  fof(f483,plain,(
% 1.82/0.63    v1_xboole_0(sK2(sK0,sK1)) | ~spl4_18),
% 1.82/0.63    inference(avatar_component_clause,[],[f481])).
% 1.82/0.63  fof(f481,plain,(
% 1.82/0.63    spl4_18 <=> v1_xboole_0(sK2(sK0,sK1))),
% 1.82/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.82/0.63  fof(f123,plain,(
% 1.82/0.63    v1_xboole_0(k1_xboole_0) | ~spl4_6),
% 1.82/0.63    inference(avatar_component_clause,[],[f121])).
% 1.82/0.63  fof(f121,plain,(
% 1.82/0.63    spl4_6 <=> v1_xboole_0(k1_xboole_0)),
% 1.82/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.82/0.63  fof(f346,plain,(
% 1.82/0.63    k1_xboole_0 != k6_subset_1(sK2(sK0,sK1),sK1) | (spl4_12 | ~spl4_13)),
% 1.82/0.63    inference(unit_resulting_resolution,[],[f196,f256,f83])).
% 1.82/0.63  fof(f83,plain,(
% 1.82/0.63    ( ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.82/0.63    inference(cnf_transformation,[],[f36])).
% 1.82/0.63  fof(f36,plain,(
% 1.82/0.63    ! [X0,X1] : (k1_xboole_0 != k6_subset_1(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1))),
% 1.82/0.63    inference(ennf_transformation,[],[f17])).
% 1.82/0.63  fof(f17,axiom,(
% 1.82/0.63    ! [X0,X1] : ~(k1_xboole_0 = k6_subset_1(X1,X0) & X0 != X1 & r1_tarski(X0,X1))),
% 1.82/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l48_tex_2)).
% 1.82/0.63  fof(f256,plain,(
% 1.82/0.63    r1_tarski(sK1,sK2(sK0,sK1)) | ~spl4_13),
% 1.82/0.63    inference(avatar_component_clause,[],[f254])).
% 1.82/0.63  fof(f254,plain,(
% 1.82/0.63    spl4_13 <=> r1_tarski(sK1,sK2(sK0,sK1))),
% 1.82/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.82/0.63  fof(f196,plain,(
% 1.82/0.63    sK1 != sK2(sK0,sK1) | spl4_12),
% 1.82/0.63    inference(avatar_component_clause,[],[f194])).
% 1.82/0.63  fof(f194,plain,(
% 1.82/0.63    spl4_12 <=> sK1 = sK2(sK0,sK1)),
% 1.82/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.82/0.63  fof(f484,plain,(
% 1.82/0.63    spl4_18 | spl4_5 | spl4_12 | ~spl4_13 | ~spl4_17),
% 1.82/0.63    inference(avatar_split_clause,[],[f437,f397,f254,f194,f116,f481])).
% 1.82/0.63  fof(f116,plain,(
% 1.82/0.63    spl4_5 <=> v1_xboole_0(sK1)),
% 1.82/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.82/0.63  fof(f397,plain,(
% 1.82/0.63    spl4_17 <=> v1_zfmisc_1(sK2(sK0,sK1))),
% 1.82/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.82/0.63  fof(f437,plain,(
% 1.82/0.63    v1_xboole_0(sK2(sK0,sK1)) | (spl4_5 | spl4_12 | ~spl4_13 | ~spl4_17)),
% 1.82/0.63    inference(unit_resulting_resolution,[],[f118,f196,f256,f399,f61])).
% 1.82/0.63  fof(f61,plain,(
% 1.82/0.63    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | ~r1_tarski(X0,X1) | X0 = X1 | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.82/0.63    inference(cnf_transformation,[],[f25])).
% 1.82/0.63  fof(f25,plain,(
% 1.82/0.63    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.82/0.63    inference(flattening,[],[f24])).
% 1.82/0.63  fof(f24,plain,(
% 1.82/0.63    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.82/0.63    inference(ennf_transformation,[],[f18])).
% 1.82/0.63  fof(f18,axiom,(
% 1.82/0.63    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.82/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 1.82/0.63  fof(f399,plain,(
% 1.82/0.63    v1_zfmisc_1(sK2(sK0,sK1)) | ~spl4_17),
% 1.82/0.63    inference(avatar_component_clause,[],[f397])).
% 1.82/0.63  fof(f118,plain,(
% 1.82/0.63    ~v1_xboole_0(sK1) | spl4_5),
% 1.82/0.63    inference(avatar_component_clause,[],[f116])).
% 1.82/0.63  fof(f400,plain,(
% 1.82/0.63    spl4_17 | spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_14 | ~spl4_16),
% 1.82/0.63    inference(avatar_split_clause,[],[f361,f354,f341,f111,f106,f96,f397])).
% 1.82/0.63  fof(f96,plain,(
% 1.82/0.63    spl4_1 <=> v2_struct_0(sK0)),
% 1.82/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.82/0.63  fof(f106,plain,(
% 1.82/0.63    spl4_3 <=> v2_tdlat_3(sK0)),
% 1.82/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.82/0.63  fof(f111,plain,(
% 1.82/0.63    spl4_4 <=> l1_pre_topc(sK0)),
% 1.82/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.82/0.63  fof(f341,plain,(
% 1.82/0.63    spl4_14 <=> v2_tex_2(sK2(sK0,sK1),sK0)),
% 1.82/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.82/0.63  fof(f354,plain,(
% 1.82/0.63    spl4_16 <=> m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.82/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 1.82/0.63  fof(f361,plain,(
% 1.82/0.63    v1_zfmisc_1(sK2(sK0,sK1)) | (spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_14 | ~spl4_16)),
% 1.82/0.63    inference(unit_resulting_resolution,[],[f98,f108,f113,f343,f356,f94])).
% 1.82/0.63  fof(f94,plain,(
% 1.82/0.63    ( ! [X0,X1] : (~v2_tdlat_3(X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_zfmisc_1(X1) | v2_struct_0(X0)) )),
% 1.82/0.63    inference(subsumption_resolution,[],[f93,f69])).
% 1.82/0.63  fof(f69,plain,(
% 1.82/0.63    ( ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0)) )),
% 1.82/0.63    inference(cnf_transformation,[],[f30])).
% 1.82/0.63  fof(f30,plain,(
% 1.82/0.63    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 1.82/0.63    inference(ennf_transformation,[],[f9])).
% 1.82/0.63  fof(f9,axiom,(
% 1.82/0.63    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 1.82/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).
% 1.82/0.63  fof(f93,plain,(
% 1.82/0.63    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | v2_struct_0(X0)) )),
% 1.82/0.63    inference(subsumption_resolution,[],[f70,f62])).
% 1.82/0.63  fof(f62,plain,(
% 1.82/0.63    ( ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0)) )),
% 1.82/0.63    inference(cnf_transformation,[],[f27])).
% 1.82/0.63  fof(f27,plain,(
% 1.82/0.63    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 1.82/0.63    inference(flattening,[],[f26])).
% 1.82/0.63  fof(f26,plain,(
% 1.82/0.63    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 1.82/0.63    inference(ennf_transformation,[],[f15])).
% 1.82/0.63  fof(f15,axiom,(
% 1.82/0.63    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 1.82/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tdlat_3)).
% 1.82/0.63  fof(f70,plain,(
% 1.82/0.63    ( ! [X0,X1] : (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.82/0.63    inference(cnf_transformation,[],[f47])).
% 1.82/0.63  fof(f47,plain,(
% 1.82/0.63    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1)) & (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.82/0.63    inference(nnf_transformation,[],[f32])).
% 1.82/0.63  fof(f32,plain,(
% 1.82/0.63    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.82/0.63    inference(flattening,[],[f31])).
% 1.82/0.63  fof(f31,plain,(
% 1.82/0.63    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.82/0.63    inference(ennf_transformation,[],[f19])).
% 1.82/0.63  fof(f19,axiom,(
% 1.82/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.82/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 1.82/0.63  fof(f356,plain,(
% 1.82/0.63    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_16),
% 1.82/0.63    inference(avatar_component_clause,[],[f354])).
% 1.82/0.63  fof(f343,plain,(
% 1.82/0.63    v2_tex_2(sK2(sK0,sK1),sK0) | ~spl4_14),
% 1.82/0.63    inference(avatar_component_clause,[],[f341])).
% 1.82/0.63  fof(f113,plain,(
% 1.82/0.63    l1_pre_topc(sK0) | ~spl4_4),
% 1.82/0.63    inference(avatar_component_clause,[],[f111])).
% 1.82/0.63  fof(f108,plain,(
% 1.82/0.63    v2_tdlat_3(sK0) | ~spl4_3),
% 1.82/0.63    inference(avatar_component_clause,[],[f106])).
% 1.82/0.63  fof(f98,plain,(
% 1.82/0.63    ~v2_struct_0(sK0) | spl4_1),
% 1.82/0.63    inference(avatar_component_clause,[],[f96])).
% 1.82/0.63  fof(f357,plain,(
% 1.82/0.63    spl4_16 | ~spl4_4 | ~spl4_7 | spl4_8 | ~spl4_11),
% 1.82/0.63    inference(avatar_split_clause,[],[f311,f180,f131,f126,f111,f354])).
% 1.82/0.63  fof(f126,plain,(
% 1.82/0.63    spl4_7 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.82/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.82/0.63  fof(f131,plain,(
% 1.82/0.63    spl4_8 <=> v3_tex_2(sK1,sK0)),
% 1.82/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.82/0.63  fof(f180,plain,(
% 1.82/0.63    spl4_11 <=> v2_tex_2(sK1,sK0)),
% 1.82/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.82/0.63  fof(f311,plain,(
% 1.82/0.63    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_4 | ~spl4_7 | spl4_8 | ~spl4_11)),
% 1.82/0.63    inference(unit_resulting_resolution,[],[f113,f132,f128,f182,f65])).
% 1.82/0.63  fof(f65,plain,(
% 1.82/0.63    ( ! [X0,X1] : (m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.82/0.63    inference(cnf_transformation,[],[f46])).
% 1.82/0.63  fof(f46,plain,(
% 1.82/0.63    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.82/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f44,f45])).
% 1.82/0.63  fof(f45,plain,(
% 1.82/0.63    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.82/0.63    introduced(choice_axiom,[])).
% 1.82/0.63  fof(f44,plain,(
% 1.82/0.63    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.82/0.63    inference(rectify,[],[f43])).
% 1.82/0.63  fof(f43,plain,(
% 1.82/0.63    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.82/0.63    inference(flattening,[],[f42])).
% 1.82/0.63  fof(f42,plain,(
% 1.82/0.63    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.82/0.63    inference(nnf_transformation,[],[f29])).
% 1.82/0.63  fof(f29,plain,(
% 1.82/0.63    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.82/0.63    inference(flattening,[],[f28])).
% 1.82/0.63  fof(f28,plain,(
% 1.82/0.63    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.82/0.63    inference(ennf_transformation,[],[f16])).
% 1.82/0.63  fof(f16,axiom,(
% 1.82/0.63    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 1.82/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).
% 1.82/0.63  fof(f182,plain,(
% 1.82/0.63    v2_tex_2(sK1,sK0) | ~spl4_11),
% 1.82/0.63    inference(avatar_component_clause,[],[f180])).
% 1.82/0.63  fof(f128,plain,(
% 1.82/0.63    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_7),
% 1.82/0.63    inference(avatar_component_clause,[],[f126])).
% 1.82/0.63  fof(f132,plain,(
% 1.82/0.63    ~v3_tex_2(sK1,sK0) | spl4_8),
% 1.82/0.63    inference(avatar_component_clause,[],[f131])).
% 1.82/0.63  fof(f345,plain,(
% 1.82/0.63    spl4_13 | spl4_1 | ~spl4_3 | ~spl4_4 | spl4_5 | ~spl4_7 | ~spl4_9 | ~spl4_11),
% 1.82/0.63    inference(avatar_split_clause,[],[f284,f180,f135,f126,f116,f111,f106,f96,f254])).
% 1.82/0.63  fof(f135,plain,(
% 1.82/0.63    spl4_9 <=> v1_zfmisc_1(sK1)),
% 1.82/0.63    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.82/0.63  fof(f284,plain,(
% 1.82/0.63    r1_tarski(sK1,sK2(sK0,sK1)) | (spl4_1 | ~spl4_3 | ~spl4_4 | spl4_5 | ~spl4_7 | ~spl4_9 | ~spl4_11)),
% 1.82/0.63    inference(subsumption_resolution,[],[f283,f280])).
% 1.82/0.63  fof(f280,plain,(
% 1.82/0.63    ~v3_tex_2(sK1,sK0) | (spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_7 | ~spl4_11)),
% 1.82/0.63    inference(subsumption_resolution,[],[f57,f189])).
% 1.82/0.63  fof(f189,plain,(
% 1.82/0.63    v1_zfmisc_1(sK1) | (spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_7 | ~spl4_11)),
% 1.82/0.63    inference(unit_resulting_resolution,[],[f98,f113,f108,f128,f182,f94])).
% 1.82/0.63  fof(f57,plain,(
% 1.82/0.63    ~v1_zfmisc_1(sK1) | ~v3_tex_2(sK1,sK0)),
% 1.82/0.63    inference(cnf_transformation,[],[f41])).
% 1.82/0.63  fof(f41,plain,(
% 1.82/0.63    ((~v1_zfmisc_1(sK1) | ~v3_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.82/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f40,f39])).
% 1.82/0.63  fof(f39,plain,(
% 1.82/0.63    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.82/0.63    introduced(choice_axiom,[])).
% 1.82/0.63  fof(f40,plain,(
% 1.82/0.63    ? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK1) | ~v3_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1))),
% 1.82/0.63    introduced(choice_axiom,[])).
% 1.82/0.63  fof(f38,plain,(
% 1.82/0.63    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.82/0.63    inference(flattening,[],[f37])).
% 1.82/0.63  fof(f37,plain,(
% 1.82/0.63    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.82/0.63    inference(nnf_transformation,[],[f23])).
% 1.82/0.63  fof(f23,plain,(
% 1.82/0.63    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.82/0.63    inference(flattening,[],[f22])).
% 1.82/0.63  fof(f22,plain,(
% 1.82/0.63    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.82/0.63    inference(ennf_transformation,[],[f21])).
% 1.82/0.63  fof(f21,negated_conjecture,(
% 1.82/0.63    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.82/0.63    inference(negated_conjecture,[],[f20])).
% 1.82/0.63  fof(f20,conjecture,(
% 1.82/0.63    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.82/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tex_2)).
% 1.82/0.63  fof(f283,plain,(
% 1.82/0.63    r1_tarski(sK1,sK2(sK0,sK1)) | v3_tex_2(sK1,sK0) | (spl4_1 | ~spl4_3 | ~spl4_4 | spl4_5 | ~spl4_7 | ~spl4_9)),
% 1.82/0.63    inference(subsumption_resolution,[],[f244,f239])).
% 1.82/0.63  fof(f239,plain,(
% 1.82/0.63    v2_tex_2(sK1,sK0) | (spl4_1 | ~spl4_3 | ~spl4_4 | spl4_5 | ~spl4_7 | ~spl4_9)),
% 1.82/0.63    inference(unit_resulting_resolution,[],[f137,f118,f128,f178])).
% 1.82/0.63  fof(f178,plain,(
% 1.82/0.63    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0) | v2_tex_2(X0,sK0)) ) | (spl4_1 | ~spl4_3 | ~spl4_4)),
% 1.82/0.63    inference(subsumption_resolution,[],[f177,f98])).
% 1.82/0.63  fof(f177,plain,(
% 1.82/0.63    ( ! [X0] : (~v1_zfmisc_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | v2_tex_2(X0,sK0) | v2_struct_0(sK0)) ) | (~spl4_3 | ~spl4_4)),
% 1.82/0.63    inference(subsumption_resolution,[],[f176,f113])).
% 1.82/0.63  fof(f176,plain,(
% 1.82/0.63    ( ! [X0] : (~v1_zfmisc_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | ~l1_pre_topc(sK0) | v2_tex_2(X0,sK0) | v2_struct_0(sK0)) ) | ~spl4_3),
% 1.82/0.63    inference(resolution,[],[f92,f108])).
% 1.82/0.63  fof(f92,plain,(
% 1.82/0.63    ( ! [X0,X1] : (~v2_tdlat_3(X0) | ~v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v2_tex_2(X1,X0) | v2_struct_0(X0)) )),
% 1.82/0.63    inference(subsumption_resolution,[],[f71,f62])).
% 1.82/0.63  fof(f71,plain,(
% 1.82/0.63    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.82/0.63    inference(cnf_transformation,[],[f47])).
% 1.82/0.63  fof(f137,plain,(
% 1.82/0.63    v1_zfmisc_1(sK1) | ~spl4_9),
% 1.82/0.63    inference(avatar_component_clause,[],[f135])).
% 1.82/0.63  fof(f244,plain,(
% 1.82/0.63    ~v2_tex_2(sK1,sK0) | r1_tarski(sK1,sK2(sK0,sK1)) | v3_tex_2(sK1,sK0) | (~spl4_4 | ~spl4_7)),
% 1.82/0.63    inference(resolution,[],[f173,f128])).
% 1.82/0.63  fof(f173,plain,(
% 1.82/0.63    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | r1_tarski(X0,sK2(sK0,X0)) | v3_tex_2(X0,sK0)) ) | ~spl4_4),
% 1.82/0.63    inference(resolution,[],[f67,f113])).
% 1.82/0.63  fof(f67,plain,(
% 1.82/0.63    ( ! [X0,X1] : (~l1_pre_topc(X0) | r1_tarski(X1,sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_tex_2(X1,X0)) )),
% 1.82/0.63    inference(cnf_transformation,[],[f46])).
% 1.82/0.63  fof(f344,plain,(
% 1.82/0.63    spl4_14 | ~spl4_4 | ~spl4_7 | spl4_8 | ~spl4_11),
% 1.82/0.63    inference(avatar_split_clause,[],[f188,f180,f131,f126,f111,f341])).
% 1.82/0.63  fof(f188,plain,(
% 1.82/0.63    v2_tex_2(sK2(sK0,sK1),sK0) | (~spl4_4 | ~spl4_7 | spl4_8 | ~spl4_11)),
% 1.82/0.63    inference(unit_resulting_resolution,[],[f113,f132,f128,f182,f66])).
% 1.82/0.63  fof(f66,plain,(
% 1.82/0.63    ( ! [X0,X1] : (~l1_pre_topc(X0) | v2_tex_2(sK2(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_tex_2(X1,X0)) )),
% 1.82/0.63    inference(cnf_transformation,[],[f46])).
% 1.82/0.63  fof(f306,plain,(
% 1.82/0.63    spl4_11 | spl4_1 | ~spl4_3 | ~spl4_4 | spl4_5 | ~spl4_7 | ~spl4_9),
% 1.82/0.63    inference(avatar_split_clause,[],[f239,f135,f126,f116,f111,f106,f96,f180])).
% 1.82/0.63  fof(f286,plain,(
% 1.82/0.63    spl4_9 | spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_7 | ~spl4_11),
% 1.82/0.63    inference(avatar_split_clause,[],[f189,f180,f126,f111,f106,f96,f135])).
% 1.82/0.63  fof(f285,plain,(
% 1.82/0.63    ~spl4_8 | spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_7 | ~spl4_11),
% 1.82/0.63    inference(avatar_split_clause,[],[f280,f180,f126,f111,f106,f96,f131])).
% 1.82/0.63  fof(f268,plain,(
% 1.82/0.63    ~spl4_4 | ~spl4_7 | ~spl4_8 | spl4_11),
% 1.82/0.63    inference(avatar_contradiction_clause,[],[f267])).
% 1.82/0.63  fof(f267,plain,(
% 1.82/0.63    $false | (~spl4_4 | ~spl4_7 | ~spl4_8 | spl4_11)),
% 1.82/0.63    inference(subsumption_resolution,[],[f263,f181])).
% 1.82/0.63  fof(f181,plain,(
% 1.82/0.63    ~v2_tex_2(sK1,sK0) | spl4_11),
% 1.82/0.63    inference(avatar_component_clause,[],[f180])).
% 1.82/0.63  fof(f263,plain,(
% 1.82/0.63    v2_tex_2(sK1,sK0) | (~spl4_4 | ~spl4_7 | ~spl4_8)),
% 1.82/0.63    inference(unit_resulting_resolution,[],[f128,f133,f165])).
% 1.82/0.63  fof(f165,plain,(
% 1.82/0.63    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tex_2(X0,sK0) | v2_tex_2(X0,sK0)) ) | ~spl4_4),
% 1.82/0.63    inference(resolution,[],[f63,f113])).
% 1.82/0.63  fof(f63,plain,(
% 1.82/0.63    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0)) )),
% 1.82/0.63    inference(cnf_transformation,[],[f46])).
% 1.82/0.63  fof(f133,plain,(
% 1.82/0.63    v3_tex_2(sK1,sK0) | ~spl4_8),
% 1.82/0.63    inference(avatar_component_clause,[],[f131])).
% 1.82/0.63  fof(f197,plain,(
% 1.82/0.63    ~spl4_12 | ~spl4_4 | ~spl4_7 | spl4_8 | ~spl4_11),
% 1.82/0.63    inference(avatar_split_clause,[],[f186,f180,f131,f126,f111,f194])).
% 1.82/0.63  fof(f186,plain,(
% 1.82/0.63    sK1 != sK2(sK0,sK1) | (~spl4_4 | ~spl4_7 | spl4_8 | ~spl4_11)),
% 1.82/0.63    inference(unit_resulting_resolution,[],[f113,f132,f128,f182,f68])).
% 1.82/0.63  fof(f68,plain,(
% 1.82/0.63    ( ! [X0,X1] : (~l1_pre_topc(X0) | sK2(X0,X1) != X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_tex_2(X1,X0)) )),
% 1.82/0.63    inference(cnf_transformation,[],[f46])).
% 1.82/0.63  fof(f138,plain,(
% 1.82/0.63    spl4_8 | spl4_9),
% 1.82/0.63    inference(avatar_split_clause,[],[f56,f135,f131])).
% 1.82/0.63  fof(f56,plain,(
% 1.82/0.63    v1_zfmisc_1(sK1) | v3_tex_2(sK1,sK0)),
% 1.82/0.63    inference(cnf_transformation,[],[f41])).
% 1.82/0.63  fof(f129,plain,(
% 1.82/0.63    spl4_7),
% 1.82/0.63    inference(avatar_split_clause,[],[f55,f126])).
% 1.82/0.63  fof(f55,plain,(
% 1.82/0.63    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.82/0.63    inference(cnf_transformation,[],[f41])).
% 1.82/0.63  fof(f124,plain,(
% 1.82/0.63    spl4_6),
% 1.82/0.63    inference(avatar_split_clause,[],[f58,f121])).
% 1.82/0.63  fof(f58,plain,(
% 1.82/0.63    v1_xboole_0(k1_xboole_0)),
% 1.82/0.63    inference(cnf_transformation,[],[f1])).
% 1.82/0.63  fof(f1,axiom,(
% 1.82/0.63    v1_xboole_0(k1_xboole_0)),
% 1.82/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.82/0.63  fof(f119,plain,(
% 1.82/0.63    ~spl4_5),
% 1.82/0.63    inference(avatar_split_clause,[],[f54,f116])).
% 1.82/0.63  fof(f54,plain,(
% 1.82/0.63    ~v1_xboole_0(sK1)),
% 1.82/0.63    inference(cnf_transformation,[],[f41])).
% 1.82/0.63  fof(f114,plain,(
% 1.82/0.63    spl4_4),
% 1.82/0.63    inference(avatar_split_clause,[],[f53,f111])).
% 1.82/0.63  fof(f53,plain,(
% 1.82/0.63    l1_pre_topc(sK0)),
% 1.82/0.63    inference(cnf_transformation,[],[f41])).
% 1.82/0.63  fof(f109,plain,(
% 1.82/0.63    spl4_3),
% 1.82/0.63    inference(avatar_split_clause,[],[f52,f106])).
% 1.82/0.63  fof(f52,plain,(
% 1.82/0.63    v2_tdlat_3(sK0)),
% 1.82/0.63    inference(cnf_transformation,[],[f41])).
% 1.82/0.63  fof(f99,plain,(
% 1.82/0.63    ~spl4_1),
% 1.82/0.63    inference(avatar_split_clause,[],[f50,f96])).
% 1.82/0.63  fof(f50,plain,(
% 1.82/0.63    ~v2_struct_0(sK0)),
% 1.82/0.63    inference(cnf_transformation,[],[f41])).
% 1.82/0.63  % SZS output end Proof for theBenchmark
% 1.82/0.63  % (25103)------------------------------
% 1.82/0.63  % (25103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.63  % (25103)Termination reason: Refutation
% 1.82/0.63  
% 1.82/0.63  % (25103)Memory used [KB]: 11129
% 1.82/0.63  % (25103)Time elapsed: 0.203 s
% 1.82/0.63  % (25103)------------------------------
% 1.82/0.63  % (25103)------------------------------
% 1.82/0.63  % (25082)Success in time 0.262 s
%------------------------------------------------------------------------------
