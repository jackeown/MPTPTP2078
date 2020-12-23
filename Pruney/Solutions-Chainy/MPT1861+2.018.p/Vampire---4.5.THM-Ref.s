%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 203 expanded)
%              Number of leaves         :   19 (  66 expanded)
%              Depth                    :   10
%              Number of atoms          :  228 ( 594 expanded)
%              Number of equality atoms :   13 (  45 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f348,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f95,f100,f127,f184,f189,f241,f245,f282,f296,f339,f347])).

fof(f347,plain,(
    spl3_23 ),
    inference(avatar_contradiction_clause,[],[f345])).

fof(f345,plain,
    ( $false
    | spl3_23 ),
    inference(unit_resulting_resolution,[],[f33,f338,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f338,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK2))
    | spl3_23 ),
    inference(avatar_component_clause,[],[f336])).

fof(f336,plain,
    ( spl3_23
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f33,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f339,plain,
    ( ~ spl3_23
    | ~ spl3_7
    | spl3_8
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f329,f243,f92,f88,f336])).

fof(f88,plain,
    ( spl3_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f92,plain,
    ( spl3_8
  <=> v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f243,plain,
    ( spl3_18
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | ~ r1_tarski(X0,u1_struct_0(sK0))
        | v2_tex_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f329,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK2))
    | spl3_8
    | ~ spl3_18 ),
    inference(resolution,[],[f326,f94])).

fof(f94,plain,
    ( ~ v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f92])).

fof(f326,plain,
    ( ! [X4,X3] :
        ( v2_tex_2(k1_setfam_1(k2_tarski(X3,X4)),sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(sK2)) )
    | ~ spl3_18 ),
    inference(resolution,[],[f302,f84])).

fof(f84,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(k1_setfam_1(k2_tarski(X7,X8)),X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X6)) ) ),
    inference(duplicate_literal_removal,[],[f81])).

fof(f81,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(k1_setfam_1(k2_tarski(X7,X8)),X6)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X6))
      | ~ m1_subset_1(X8,k1_zfmisc_1(X6)) ) ),
    inference(superposition,[],[f68,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f30,f23])).

fof(f23,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_subset_1(X1,X2,X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f29,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f302,plain,
    ( ! [X8,X7] :
        ( ~ r1_tarski(k1_setfam_1(k2_tarski(X7,X8)),sK2)
        | v2_tex_2(k1_setfam_1(k2_tarski(X7,X8)),sK0)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_18 ),
    inference(resolution,[],[f244,f84])).

fof(f244,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK0))
        | ~ r1_tarski(X0,sK2)
        | v2_tex_2(X0,sK0) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f243])).

fof(f296,plain,(
    spl3_21 ),
    inference(avatar_contradiction_clause,[],[f294])).

fof(f294,plain,
    ( $false
    | spl3_21 ),
    inference(unit_resulting_resolution,[],[f33,f281,f27])).

fof(f281,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | spl3_21 ),
    inference(avatar_component_clause,[],[f279])).

fof(f279,plain,
    ( spl3_21
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f282,plain,
    ( ~ spl3_21
    | ~ spl3_15
    | spl3_16
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f268,f239,f181,f177,f279])).

fof(f177,plain,
    ( spl3_15
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f181,plain,
    ( spl3_16
  <=> v2_tex_2(k1_setfam_1(k2_tarski(sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f239,plain,
    ( spl3_17
  <=> ! [X1] :
        ( ~ r1_tarski(X1,sK1)
        | ~ r1_tarski(X1,u1_struct_0(sK0))
        | v2_tex_2(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f268,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | spl3_16
    | ~ spl3_17 ),
    inference(resolution,[],[f264,f183])).

fof(f183,plain,
    ( ~ v2_tex_2(k1_setfam_1(k2_tarski(sK2,sK1)),sK0)
    | spl3_16 ),
    inference(avatar_component_clause,[],[f181])).

fof(f264,plain,
    ( ! [X4,X3] :
        ( v2_tex_2(k1_setfam_1(k2_tarski(X3,X4)),sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(sK1)) )
    | ~ spl3_17 ),
    inference(resolution,[],[f260,f84])).

fof(f260,plain,
    ( ! [X8,X7] :
        ( ~ r1_tarski(k1_setfam_1(k2_tarski(X7,X8)),sK1)
        | v2_tex_2(k1_setfam_1(k2_tarski(X7,X8)),sK0)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_17 ),
    inference(resolution,[],[f240,f84])).

fof(f240,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,u1_struct_0(sK0))
        | ~ r1_tarski(X1,sK1)
        | v2_tex_2(X1,sK0) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f239])).

fof(f245,plain,
    ( ~ spl3_1
    | spl3_18
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f232,f119,f243,f36])).

fof(f36,plain,
    ( spl3_1
  <=> v2_tex_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f119,plain,
    ( spl3_9
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f232,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ r1_tarski(X0,sK2)
      | ~ v2_tex_2(sK2,sK0)
      | v2_tex_2(X0,sK0)
      | ~ r1_tarski(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f115,f18])).

fof(f18,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & ( v2_tex_2(X2,X0)
                | v2_tex_2(X1,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v2_tex_2(X2,X0)
                    | v2_tex_2(X1,X0) )
                 => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X2,X0)
                  | v2_tex_2(X1,X0) )
               => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tex_2)).

fof(f115,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_pre_topc(X3)
      | ~ r1_tarski(X4,X2)
      | ~ v2_tex_2(X2,X3)
      | v2_tex_2(X4,X3)
      | ~ r1_tarski(X4,u1_struct_0(X3)) ) ),
    inference(resolution,[],[f22,f27])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(X2,X1)
      | ~ v2_tex_2(X1,X0)
      | v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_tex_2(X2,X0)
              | ~ v2_tex_2(X1,X0)
              | ~ r1_tarski(X2,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v2_tex_2(X1,X0)
                  & r1_tarski(X2,X1) )
               => v2_tex_2(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).

fof(f241,plain,
    ( ~ spl3_2
    | spl3_17
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f233,f119,f239,f40])).

fof(f40,plain,
    ( spl3_2
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f233,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ r1_tarski(X1,sK1)
      | ~ v2_tex_2(sK1,sK0)
      | v2_tex_2(X1,sK0)
      | ~ r1_tarski(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f115,f20])).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f189,plain,(
    spl3_15 ),
    inference(avatar_contradiction_clause,[],[f185])).

fof(f185,plain,
    ( $false
    | spl3_15 ),
    inference(subsumption_resolution,[],[f20,f179])).

fof(f179,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f177])).

fof(f184,plain,
    ( ~ spl3_15
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f164,f181,f177])).

fof(f164,plain,
    ( ~ v2_tex_2(k1_setfam_1(k2_tarski(sK2,sK1)),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f19,f85])).

fof(f85,plain,(
    ! [X4,X5,X3] :
      ( k9_subset_1(X3,X5,X4) = k1_setfam_1(k2_tarski(X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(duplicate_literal_removal,[],[f80])).

fof(f80,plain,(
    ! [X4,X5,X3] :
      ( k9_subset_1(X3,X5,X4) = k1_setfam_1(k2_tarski(X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f31,f32])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f19,plain,(
    ~ v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f127,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f126])).

fof(f126,plain,
    ( $false
    | spl3_9 ),
    inference(subsumption_resolution,[],[f21,f121])).

fof(f121,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f119])).

fof(f21,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f100,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f96])).

fof(f96,plain,
    ( $false
    | spl3_7 ),
    inference(subsumption_resolution,[],[f18,f90])).

fof(f90,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f88])).

fof(f95,plain,
    ( ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f78,f92,f88])).

fof(f78,plain,
    ( ~ v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f19,f32])).

fof(f43,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f17,f40,f36])).

fof(f17,plain,
    ( v2_tex_2(sK1,sK0)
    | v2_tex_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:47:31 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.48  % (12533)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.48  % (12542)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.50  % (12537)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.50  % (12558)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.50  % (12558)Refutation not found, incomplete strategy% (12558)------------------------------
% 0.20/0.50  % (12558)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (12558)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (12558)Memory used [KB]: 10746
% 0.20/0.50  % (12558)Time elapsed: 0.119 s
% 0.20/0.50  % (12558)------------------------------
% 0.20/0.50  % (12558)------------------------------
% 0.20/0.51  % (12534)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (12551)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.51  % (12532)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.51  % (12540)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.52  % (12550)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.52  % (12536)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (12542)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % (12557)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f348,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f43,f95,f100,f127,f184,f189,f241,f245,f282,f296,f339,f347])).
% 0.20/0.52  fof(f347,plain,(
% 0.20/0.52    spl3_23),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f345])).
% 0.20/0.52  fof(f345,plain,(
% 0.20/0.52    $false | spl3_23),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f33,f338,f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.52  fof(f338,plain,(
% 0.20/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(sK2)) | spl3_23),
% 0.20/0.52    inference(avatar_component_clause,[],[f336])).
% 0.20/0.52  fof(f336,plain,(
% 0.20/0.52    spl3_23 <=> m1_subset_1(sK2,k1_zfmisc_1(sK2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.52    inference(equality_resolution,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.52  fof(f339,plain,(
% 0.20/0.52    ~spl3_23 | ~spl3_7 | spl3_8 | ~spl3_18),
% 0.20/0.52    inference(avatar_split_clause,[],[f329,f243,f92,f88,f336])).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    spl3_7 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.52  fof(f92,plain,(
% 0.20/0.52    spl3_8 <=> v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.52  fof(f243,plain,(
% 0.20/0.52    spl3_18 <=> ! [X0] : (~r1_tarski(X0,sK2) | ~r1_tarski(X0,u1_struct_0(sK0)) | v2_tex_2(X0,sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.52  fof(f329,plain,(
% 0.20/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(sK2)) | (spl3_8 | ~spl3_18)),
% 0.20/0.52    inference(resolution,[],[f326,f94])).
% 0.20/0.52  fof(f94,plain,(
% 0.20/0.52    ~v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | spl3_8),
% 0.20/0.52    inference(avatar_component_clause,[],[f92])).
% 0.20/0.52  fof(f326,plain,(
% 0.20/0.52    ( ! [X4,X3] : (v2_tex_2(k1_setfam_1(k2_tarski(X3,X4)),sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X4,k1_zfmisc_1(sK2))) ) | ~spl3_18),
% 0.20/0.52    inference(resolution,[],[f302,f84])).
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    ( ! [X6,X8,X7] : (r1_tarski(k1_setfam_1(k2_tarski(X7,X8)),X6) | ~m1_subset_1(X8,k1_zfmisc_1(X6))) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f81])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    ( ! [X6,X8,X7] : (r1_tarski(k1_setfam_1(k2_tarski(X7,X8)),X6) | ~m1_subset_1(X8,k1_zfmisc_1(X6)) | ~m1_subset_1(X8,k1_zfmisc_1(X6))) )),
% 0.20/0.52    inference(superposition,[],[f68,f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f30,f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r1_tarski(k9_subset_1(X1,X2,X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.52    inference(resolution,[],[f29,f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.20/0.52  fof(f302,plain,(
% 0.20/0.52    ( ! [X8,X7] : (~r1_tarski(k1_setfam_1(k2_tarski(X7,X8)),sK2) | v2_tex_2(k1_setfam_1(k2_tarski(X7,X8)),sK0) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_18),
% 0.20/0.52    inference(resolution,[],[f244,f84])).
% 0.20/0.52  fof(f244,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | ~r1_tarski(X0,sK2) | v2_tex_2(X0,sK0)) ) | ~spl3_18),
% 0.20/0.52    inference(avatar_component_clause,[],[f243])).
% 0.20/0.52  fof(f296,plain,(
% 0.20/0.52    spl3_21),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f294])).
% 0.20/0.52  fof(f294,plain,(
% 0.20/0.52    $false | spl3_21),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f33,f281,f27])).
% 0.20/0.52  fof(f281,plain,(
% 0.20/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | spl3_21),
% 0.20/0.52    inference(avatar_component_clause,[],[f279])).
% 0.20/0.52  fof(f279,plain,(
% 0.20/0.52    spl3_21 <=> m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.52  fof(f282,plain,(
% 0.20/0.52    ~spl3_21 | ~spl3_15 | spl3_16 | ~spl3_17),
% 0.20/0.52    inference(avatar_split_clause,[],[f268,f239,f181,f177,f279])).
% 0.20/0.52  fof(f177,plain,(
% 0.20/0.52    spl3_15 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.52  fof(f181,plain,(
% 0.20/0.52    spl3_16 <=> v2_tex_2(k1_setfam_1(k2_tarski(sK2,sK1)),sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.52  fof(f239,plain,(
% 0.20/0.52    spl3_17 <=> ! [X1] : (~r1_tarski(X1,sK1) | ~r1_tarski(X1,u1_struct_0(sK0)) | v2_tex_2(X1,sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.52  fof(f268,plain,(
% 0.20/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | (spl3_16 | ~spl3_17)),
% 0.20/0.52    inference(resolution,[],[f264,f183])).
% 0.20/0.52  fof(f183,plain,(
% 0.20/0.52    ~v2_tex_2(k1_setfam_1(k2_tarski(sK2,sK1)),sK0) | spl3_16),
% 0.20/0.52    inference(avatar_component_clause,[],[f181])).
% 0.20/0.52  fof(f264,plain,(
% 0.20/0.52    ( ! [X4,X3] : (v2_tex_2(k1_setfam_1(k2_tarski(X3,X4)),sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X4,k1_zfmisc_1(sK1))) ) | ~spl3_17),
% 0.20/0.52    inference(resolution,[],[f260,f84])).
% 0.20/0.52  fof(f260,plain,(
% 0.20/0.52    ( ! [X8,X7] : (~r1_tarski(k1_setfam_1(k2_tarski(X7,X8)),sK1) | v2_tex_2(k1_setfam_1(k2_tarski(X7,X8)),sK0) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_17),
% 0.20/0.52    inference(resolution,[],[f240,f84])).
% 0.20/0.52  fof(f240,plain,(
% 0.20/0.52    ( ! [X1] : (~r1_tarski(X1,u1_struct_0(sK0)) | ~r1_tarski(X1,sK1) | v2_tex_2(X1,sK0)) ) | ~spl3_17),
% 0.20/0.52    inference(avatar_component_clause,[],[f239])).
% 0.20/0.52  fof(f245,plain,(
% 0.20/0.52    ~spl3_1 | spl3_18 | ~spl3_9),
% 0.20/0.52    inference(avatar_split_clause,[],[f232,f119,f243,f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    spl3_1 <=> v2_tex_2(sK2,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.52  fof(f119,plain,(
% 0.20/0.52    spl3_9 <=> l1_pre_topc(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.52  fof(f232,plain,(
% 0.20/0.52    ( ! [X0] : (~l1_pre_topc(sK0) | ~r1_tarski(X0,sK2) | ~v2_tex_2(sK2,sK0) | v2_tex_2(X0,sK0) | ~r1_tarski(X0,u1_struct_0(sK0))) )),
% 0.20/0.52    inference(resolution,[],[f115,f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f10])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : ((~v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v2_tex_2(X2,X0) | v2_tex_2(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,negated_conjecture,(
% 0.20/0.52    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.20/0.52    inference(negated_conjecture,[],[f8])).
% 0.20/0.52  fof(f8,conjecture,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X2,X0) | v2_tex_2(X1,X0)) => v2_tex_2(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tex_2)).
% 0.20/0.52  fof(f115,plain,(
% 0.20/0.52    ( ! [X4,X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) | ~l1_pre_topc(X3) | ~r1_tarski(X4,X2) | ~v2_tex_2(X2,X3) | v2_tex_2(X4,X3) | ~r1_tarski(X4,u1_struct_0(X3))) )),
% 0.20/0.52    inference(resolution,[],[f22,f27])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~r1_tarski(X2,X1) | ~v2_tex_2(X1,X0) | v2_tex_2(X2,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (v2_tex_2(X2,X0) | ~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(flattening,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) | (~v2_tex_2(X1,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & r1_tarski(X2,X1)) => v2_tex_2(X2,X0)))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tex_2)).
% 0.20/0.52  fof(f241,plain,(
% 0.20/0.52    ~spl3_2 | spl3_17 | ~spl3_9),
% 0.20/0.52    inference(avatar_split_clause,[],[f233,f119,f239,f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    spl3_2 <=> v2_tex_2(sK1,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.52  fof(f233,plain,(
% 0.20/0.52    ( ! [X1] : (~l1_pre_topc(sK0) | ~r1_tarski(X1,sK1) | ~v2_tex_2(sK1,sK0) | v2_tex_2(X1,sK0) | ~r1_tarski(X1,u1_struct_0(sK0))) )),
% 0.20/0.52    inference(resolution,[],[f115,f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f189,plain,(
% 0.20/0.52    spl3_15),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f185])).
% 0.20/0.52  fof(f185,plain,(
% 0.20/0.52    $false | spl3_15),
% 0.20/0.52    inference(subsumption_resolution,[],[f20,f179])).
% 0.20/0.52  fof(f179,plain,(
% 0.20/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_15),
% 0.20/0.52    inference(avatar_component_clause,[],[f177])).
% 0.20/0.52  fof(f184,plain,(
% 0.20/0.52    ~spl3_15 | ~spl3_16),
% 0.20/0.52    inference(avatar_split_clause,[],[f164,f181,f177])).
% 0.20/0.52  fof(f164,plain,(
% 0.20/0.52    ~v2_tex_2(k1_setfam_1(k2_tarski(sK2,sK1)),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.52    inference(superposition,[],[f19,f85])).
% 0.20/0.52  fof(f85,plain,(
% 0.20/0.52    ( ! [X4,X5,X3] : (k9_subset_1(X3,X5,X4) = k1_setfam_1(k2_tarski(X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f80])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    ( ! [X4,X5,X3] : (k9_subset_1(X3,X5,X4) = k1_setfam_1(k2_tarski(X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 0.20/0.52    inference(superposition,[],[f31,f32])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ~v2_tex_2(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f11])).
% 0.20/0.53  fof(f127,plain,(
% 0.20/0.53    spl3_9),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f126])).
% 0.20/0.53  fof(f126,plain,(
% 0.20/0.53    $false | spl3_9),
% 0.20/0.53    inference(subsumption_resolution,[],[f21,f121])).
% 0.20/0.53  fof(f121,plain,(
% 0.20/0.53    ~l1_pre_topc(sK0) | spl3_9),
% 0.20/0.53    inference(avatar_component_clause,[],[f119])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    l1_pre_topc(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f11])).
% 0.20/0.53  fof(f100,plain,(
% 0.20/0.53    spl3_7),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f96])).
% 0.20/0.53  fof(f96,plain,(
% 0.20/0.53    $false | spl3_7),
% 0.20/0.53    inference(subsumption_resolution,[],[f18,f90])).
% 0.20/0.53  fof(f90,plain,(
% 0.20/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_7),
% 0.20/0.53    inference(avatar_component_clause,[],[f88])).
% 0.20/0.53  fof(f95,plain,(
% 0.20/0.53    ~spl3_7 | ~spl3_8),
% 0.20/0.53    inference(avatar_split_clause,[],[f78,f92,f88])).
% 0.20/0.53  fof(f78,plain,(
% 0.20/0.53    ~v2_tex_2(k1_setfam_1(k2_tarski(sK1,sK2)),sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.53    inference(superposition,[],[f19,f32])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    spl3_1 | spl3_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f17,f40,f36])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    v2_tex_2(sK1,sK0) | v2_tex_2(sK2,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f11])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (12542)------------------------------
% 0.20/0.53  % (12542)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (12542)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (12542)Memory used [KB]: 6396
% 0.20/0.53  % (12542)Time elapsed: 0.114 s
% 0.20/0.53  % (12542)------------------------------
% 0.20/0.53  % (12542)------------------------------
% 0.20/0.53  % (12548)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.53  % (12531)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (12528)Success in time 0.173 s
%------------------------------------------------------------------------------
