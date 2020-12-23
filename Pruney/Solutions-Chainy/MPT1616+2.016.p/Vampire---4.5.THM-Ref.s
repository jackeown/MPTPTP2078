%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:45 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 202 expanded)
%              Number of leaves         :   22 (  59 expanded)
%              Depth                    :   13
%              Number of atoms          :  329 ( 678 expanded)
%              Number of equality atoms :   33 (  96 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f236,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f159,f163,f212,f222,f225,f227,f235])).

fof(f235,plain,
    ( ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f207,f170])).

fof(f170,plain,
    ( ~ v1_xboole_0(u1_pre_topc(sK4))
    | ~ spl8_2 ),
    inference(resolution,[],[f158,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f158,plain,
    ( r2_hidden(k3_tarski(u1_pre_topc(sK4)),u1_pre_topc(sK4))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl8_2
  <=> r2_hidden(k3_tarski(u1_pre_topc(sK4)),u1_pre_topc(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f207,plain,
    ( v1_xboole_0(u1_pre_topc(sK4))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl8_3
  <=> v1_xboole_0(u1_pre_topc(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f227,plain,
    ( ~ spl8_4
    | ~ spl8_6 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f221,f213])).

fof(f213,plain,
    ( u1_struct_0(sK4) != k3_tarski(u1_pre_topc(sK4))
    | ~ spl8_4 ),
    inference(superposition,[],[f51,f211])).

fof(f211,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK4))) = k3_tarski(u1_pre_topc(sK4))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl8_4
  <=> k4_yellow_0(k2_yellow_1(u1_pre_topc(sK4))) = k3_tarski(u1_pre_topc(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f51,plain,(
    u1_struct_0(sK4) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK4))) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( u1_struct_0(sK4) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK4)))
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( u1_struct_0(sK4) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK4)))
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow_1)).

fof(f221,plain,
    ( u1_struct_0(sK4) = k3_tarski(u1_pre_topc(sK4))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl8_6
  <=> u1_struct_0(sK4) = k3_tarski(u1_pre_topc(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f225,plain,(
    spl8_5 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | spl8_5 ),
    inference(subsumption_resolution,[],[f223,f84])).

fof(f84,plain,(
    sP2(sK4) ),
    inference(subsumption_resolution,[],[f83,f49])).

fof(f49,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f83,plain,
    ( ~ v2_pre_topc(sK4)
    | sP2(sK4) ),
    inference(resolution,[],[f54,f82])).

fof(f82,plain,(
    sP3(sK4) ),
    inference(resolution,[],[f70,f50])).

fof(f50,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f70,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | sP3(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( sP3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f21,f30,f29,f28,f27])).

fof(f27,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X3] :
          ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
          | ~ r1_tarski(X3,u1_pre_topc(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f28,plain,(
    ! [X0] :
      ( sP1(X0)
    <=> ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              | ~ r2_hidden(X2,u1_pre_topc(X0))
              | ~ r2_hidden(X1,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f29,plain,(
    ! [X0] :
      ( sP2(X0)
    <=> ( sP1(X0)
        & sP0(X0)
        & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f30,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> sP2(X0) )
      | ~ sP3(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

fof(f54,plain,(
    ! [X0] :
      ( ~ sP3(X0)
      | ~ v2_pre_topc(X0)
      | sP2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP2(X0) )
        & ( sP2(X0)
          | ~ v2_pre_topc(X0) ) )
      | ~ sP3(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f223,plain,
    ( ~ sP2(sK4)
    | spl8_5 ),
    inference(resolution,[],[f217,f56])).

fof(f56,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ sP2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( sP2(X0)
        | ~ sP1(X0)
        | ~ sP0(X0)
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( sP1(X0)
          & sP0(X0)
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP2(X0) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( sP2(X0)
        | ~ sP1(X0)
        | ~ sP0(X0)
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( sP1(X0)
          & sP0(X0)
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP2(X0) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f217,plain,
    ( ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | spl8_5 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl8_5
  <=> r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f222,plain,
    ( ~ spl8_5
    | spl8_6
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f173,f156,f219,f215])).

fof(f173,plain,
    ( u1_struct_0(sK4) = k3_tarski(u1_pre_topc(sK4))
    | ~ r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))
    | ~ spl8_2 ),
    inference(resolution,[],[f172,f97])).

fof(f97,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k3_tarski(X1),X2)
      | k3_tarski(X1) = X2
      | ~ r2_hidden(X2,X1) ) ),
    inference(resolution,[],[f76,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f172,plain,
    ( r1_tarski(k3_tarski(u1_pre_topc(sK4)),u1_struct_0(sK4))
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f167,f50])).

fof(f167,plain,
    ( ~ l1_pre_topc(sK4)
    | r1_tarski(k3_tarski(u1_pre_topc(sK4)),u1_struct_0(sK4))
    | ~ spl8_2 ),
    inference(resolution,[],[f158,f131])).

fof(f131,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,u1_pre_topc(X4))
      | ~ l1_pre_topc(X4)
      | r1_tarski(X3,u1_struct_0(X4)) ) ),
    inference(resolution,[],[f104,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f104,plain,(
    ! [X4,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ r2_hidden(X3,u1_pre_topc(X4))
      | ~ l1_pre_topc(X4) ) ),
    inference(resolution,[],[f79,f53])).

fof(f53,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f212,plain,
    ( spl8_3
    | spl8_4
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f164,f156,f209,f205])).

fof(f164,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(sK4))) = k3_tarski(u1_pre_topc(sK4))
    | v1_xboole_0(u1_pre_topc(sK4))
    | ~ spl8_2 ),
    inference(resolution,[],[f158,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ r2_hidden(k3_tarski(X0),X0)
      | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

fof(f163,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | spl8_1 ),
    inference(subsumption_resolution,[],[f160,f50])).

fof(f160,plain,
    ( ~ l1_pre_topc(sK4)
    | spl8_1 ),
    inference(resolution,[],[f154,f53])).

fof(f154,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl8_1
  <=> m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f159,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f150,f156,f152])).

fof(f150,plain,
    ( r2_hidden(k3_tarski(u1_pre_topc(sK4)),u1_pre_topc(sK4))
    | ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) ),
    inference(subsumption_resolution,[],[f149,f86])).

fof(f86,plain,(
    sP0(sK4) ),
    inference(resolution,[],[f84,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ sP2(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f149,plain,
    ( r2_hidden(k3_tarski(u1_pre_topc(sK4)),u1_pre_topc(sK4))
    | ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ sP0(sK4) ),
    inference(subsumption_resolution,[],[f147,f80])).

fof(f80,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f147,plain,
    ( r2_hidden(k3_tarski(u1_pre_topc(sK4)),u1_pre_topc(sK4))
    | ~ r1_tarski(u1_pre_topc(sK4),u1_pre_topc(sK4))
    | ~ m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))
    | ~ sP0(sK4) ),
    inference(superposition,[],[f66,f137])).

fof(f137,plain,(
    k3_tarski(u1_pre_topc(sK4)) = k5_setfam_1(u1_struct_0(sK4),u1_pre_topc(sK4)) ),
    inference(resolution,[],[f123,f50])).

fof(f123,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(X2)
      | k3_tarski(u1_pre_topc(X2)) = k5_setfam_1(u1_struct_0(X2),u1_pre_topc(X2)) ) ),
    inference(resolution,[],[f73,f53])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f66,plain,(
    ! [X2,X0] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
      | ~ r1_tarski(X2,u1_pre_topc(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK7(X0)),u1_pre_topc(X0))
          & r1_tarski(sK7(X0),u1_pre_topc(X0))
          & m1_subset_1(sK7(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      & ( ! [X2] :
            ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
            | ~ r1_tarski(X2,u1_pre_topc(X0))
            | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f43,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK7(X0)),u1_pre_topc(X0))
        & r1_tarski(sK7(X0),u1_pre_topc(X0))
        & m1_subset_1(sK7(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
            & r1_tarski(X1,u1_pre_topc(X0))
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      & ( ! [X2] :
            ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
            | ~ r1_tarski(X2,u1_pre_topc(X0))
            | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X3] :
            ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            & r1_tarski(X3,u1_pre_topc(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
      & ( ! [X3] :
            ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            | ~ r1_tarski(X3,u1_pre_topc(X0))
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:26:14 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (21533)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (21545)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.49  % (21531)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.49  % (21525)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.49  % (21531)Refutation not found, incomplete strategy% (21531)------------------------------
% 0.22/0.49  % (21531)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (21531)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (21531)Memory used [KB]: 10618
% 0.22/0.49  % (21531)Time elapsed: 0.070 s
% 0.22/0.49  % (21531)------------------------------
% 0.22/0.49  % (21531)------------------------------
% 0.22/0.50  % (21545)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f236,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f159,f163,f212,f222,f225,f227,f235])).
% 0.22/0.50  fof(f235,plain,(
% 0.22/0.50    ~spl8_2 | ~spl8_3),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f234])).
% 0.22/0.50  fof(f234,plain,(
% 0.22/0.50    $false | (~spl8_2 | ~spl8_3)),
% 0.22/0.50    inference(subsumption_resolution,[],[f207,f170])).
% 0.22/0.50  fof(f170,plain,(
% 0.22/0.50    ~v1_xboole_0(u1_pre_topc(sK4)) | ~spl8_2),
% 0.22/0.50    inference(resolution,[],[f158,f71])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.50    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.50  fof(f158,plain,(
% 0.22/0.50    r2_hidden(k3_tarski(u1_pre_topc(sK4)),u1_pre_topc(sK4)) | ~spl8_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f156])).
% 0.22/0.50  fof(f156,plain,(
% 0.22/0.50    spl8_2 <=> r2_hidden(k3_tarski(u1_pre_topc(sK4)),u1_pre_topc(sK4))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.50  fof(f207,plain,(
% 0.22/0.50    v1_xboole_0(u1_pre_topc(sK4)) | ~spl8_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f205])).
% 0.22/0.50  fof(f205,plain,(
% 0.22/0.50    spl8_3 <=> v1_xboole_0(u1_pre_topc(sK4))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.22/0.50  fof(f227,plain,(
% 0.22/0.50    ~spl8_4 | ~spl8_6),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f226])).
% 0.22/0.50  fof(f226,plain,(
% 0.22/0.50    $false | (~spl8_4 | ~spl8_6)),
% 0.22/0.50    inference(subsumption_resolution,[],[f221,f213])).
% 0.22/0.50  fof(f213,plain,(
% 0.22/0.50    u1_struct_0(sK4) != k3_tarski(u1_pre_topc(sK4)) | ~spl8_4),
% 0.22/0.50    inference(superposition,[],[f51,f211])).
% 0.22/0.50  fof(f211,plain,(
% 0.22/0.50    k4_yellow_0(k2_yellow_1(u1_pre_topc(sK4))) = k3_tarski(u1_pre_topc(sK4)) | ~spl8_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f209])).
% 0.22/0.50  fof(f209,plain,(
% 0.22/0.50    spl8_4 <=> k4_yellow_0(k2_yellow_1(u1_pre_topc(sK4))) = k3_tarski(u1_pre_topc(sK4))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    u1_struct_0(sK4) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK4)))),
% 0.22/0.50    inference(cnf_transformation,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    u1_struct_0(sK4) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK4))) & l1_pre_topc(sK4) & v2_pre_topc(sK4)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (u1_struct_0(sK4) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK4))) & l1_pre_topc(sK4) & v2_pre_topc(sK4))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 0.22/0.50    inference(pure_predicate_removal,[],[f11])).
% 0.22/0.50  fof(f11,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 0.22/0.50    inference(negated_conjecture,[],[f10])).
% 0.22/0.50  fof(f10,conjecture,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow_1)).
% 0.22/0.50  fof(f221,plain,(
% 0.22/0.50    u1_struct_0(sK4) = k3_tarski(u1_pre_topc(sK4)) | ~spl8_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f219])).
% 0.22/0.50  fof(f219,plain,(
% 0.22/0.50    spl8_6 <=> u1_struct_0(sK4) = k3_tarski(u1_pre_topc(sK4))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.22/0.50  fof(f225,plain,(
% 0.22/0.50    spl8_5),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f224])).
% 0.22/0.50  fof(f224,plain,(
% 0.22/0.50    $false | spl8_5),
% 0.22/0.50    inference(subsumption_resolution,[],[f223,f84])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    sP2(sK4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f83,f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    v2_pre_topc(sK4)),
% 0.22/0.50    inference(cnf_transformation,[],[f33])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    ~v2_pre_topc(sK4) | sP2(sK4)),
% 0.22/0.50    inference(resolution,[],[f54,f82])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    sP3(sK4)),
% 0.22/0.50    inference(resolution,[],[f70,f50])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    l1_pre_topc(sK4)),
% 0.22/0.50    inference(cnf_transformation,[],[f33])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_pre_topc(X0) | sP3(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0] : (sP3(X0) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(definition_folding,[],[f21,f30,f29,f28,f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0] : (sP0(X0) <=> ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.22/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0] : (sP1(X0) <=> ! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0] : (sP2(X0) <=> (sP1(X0) & sP0(X0) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))))),
% 0.22/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0] : ((v2_pre_topc(X0) <=> sP2(X0)) | ~sP3(X0))),
% 0.22/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.22/0.50    inference(rectify,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X0] : (~sP3(X0) | ~v2_pre_topc(X0) | sP2(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ! [X0] : (((v2_pre_topc(X0) | ~sP2(X0)) & (sP2(X0) | ~v2_pre_topc(X0))) | ~sP3(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f30])).
% 0.22/0.50  fof(f223,plain,(
% 0.22/0.50    ~sP2(sK4) | spl8_5),
% 0.22/0.50    inference(resolution,[],[f217,f56])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~sP2(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ! [X0] : ((sP2(X0) | ~sP1(X0) | ~sP0(X0) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((sP1(X0) & sP0(X0) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP2(X0)))),
% 0.22/0.50    inference(flattening,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ! [X0] : ((sP2(X0) | (~sP1(X0) | ~sP0(X0) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((sP1(X0) & sP0(X0) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~sP2(X0)))),
% 0.22/0.50    inference(nnf_transformation,[],[f29])).
% 0.22/0.50  fof(f217,plain,(
% 0.22/0.50    ~r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) | spl8_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f215])).
% 0.22/0.50  fof(f215,plain,(
% 0.22/0.50    spl8_5 <=> r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.22/0.50  fof(f222,plain,(
% 0.22/0.50    ~spl8_5 | spl8_6 | ~spl8_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f173,f156,f219,f215])).
% 0.22/0.50  fof(f173,plain,(
% 0.22/0.50    u1_struct_0(sK4) = k3_tarski(u1_pre_topc(sK4)) | ~r2_hidden(u1_struct_0(sK4),u1_pre_topc(sK4)) | ~spl8_2),
% 0.22/0.50    inference(resolution,[],[f172,f97])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    ( ! [X2,X1] : (~r1_tarski(k3_tarski(X1),X2) | k3_tarski(X1) = X2 | ~r2_hidden(X2,X1)) )),
% 0.22/0.50    inference(resolution,[],[f76,f72])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f47])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.50    inference(flattening,[],[f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.50  fof(f172,plain,(
% 0.22/0.50    r1_tarski(k3_tarski(u1_pre_topc(sK4)),u1_struct_0(sK4)) | ~spl8_2),
% 0.22/0.50    inference(subsumption_resolution,[],[f167,f50])).
% 0.22/0.50  fof(f167,plain,(
% 0.22/0.50    ~l1_pre_topc(sK4) | r1_tarski(k3_tarski(u1_pre_topc(sK4)),u1_struct_0(sK4)) | ~spl8_2),
% 0.22/0.50    inference(resolution,[],[f158,f131])).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    ( ! [X4,X3] : (~r2_hidden(X3,u1_pre_topc(X4)) | ~l1_pre_topc(X4) | r1_tarski(X3,u1_struct_0(X4))) )),
% 0.22/0.50    inference(resolution,[],[f104,f77])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.50    inference(nnf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    ( ! [X4,X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4))) | ~r2_hidden(X3,u1_pre_topc(X4)) | ~l1_pre_topc(X4)) )),
% 0.22/0.50    inference(resolution,[],[f79,f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.50    inference(flattening,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.50  fof(f212,plain,(
% 0.22/0.50    spl8_3 | spl8_4 | ~spl8_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f164,f156,f209,f205])).
% 0.22/0.50  fof(f164,plain,(
% 0.22/0.50    k4_yellow_0(k2_yellow_1(u1_pre_topc(sK4))) = k3_tarski(u1_pre_topc(sK4)) | v1_xboole_0(u1_pre_topc(sK4)) | ~spl8_2),
% 0.22/0.50    inference(resolution,[],[f158,f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(k3_tarski(X0),X0) | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0))),
% 0.22/0.50    inference(flattening,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : ((k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) | v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).
% 0.22/0.50  fof(f163,plain,(
% 0.22/0.50    spl8_1),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f162])).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    $false | spl8_1),
% 0.22/0.50    inference(subsumption_resolution,[],[f160,f50])).
% 0.22/0.50  fof(f160,plain,(
% 0.22/0.50    ~l1_pre_topc(sK4) | spl8_1),
% 0.22/0.50    inference(resolution,[],[f154,f53])).
% 0.22/0.50  fof(f154,plain,(
% 0.22/0.50    ~m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) | spl8_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f152])).
% 0.22/0.50  fof(f152,plain,(
% 0.22/0.50    spl8_1 <=> m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.50  fof(f159,plain,(
% 0.22/0.50    ~spl8_1 | spl8_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f150,f156,f152])).
% 0.22/0.50  fof(f150,plain,(
% 0.22/0.50    r2_hidden(k3_tarski(u1_pre_topc(sK4)),u1_pre_topc(sK4)) | ~m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4))))),
% 0.22/0.50    inference(subsumption_resolution,[],[f149,f86])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    sP0(sK4)),
% 0.22/0.50    inference(resolution,[],[f84,f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X0] : (~sP2(X0) | sP0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f149,plain,(
% 0.22/0.50    r2_hidden(k3_tarski(u1_pre_topc(sK4)),u1_pre_topc(sK4)) | ~m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) | ~sP0(sK4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f147,f80])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.50    inference(equality_resolution,[],[f75])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.50    inference(cnf_transformation,[],[f47])).
% 0.22/0.50  fof(f147,plain,(
% 0.22/0.50    r2_hidden(k3_tarski(u1_pre_topc(sK4)),u1_pre_topc(sK4)) | ~r1_tarski(u1_pre_topc(sK4),u1_pre_topc(sK4)) | ~m1_subset_1(u1_pre_topc(sK4),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK4)))) | ~sP0(sK4)),
% 0.22/0.50    inference(superposition,[],[f66,f137])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    k3_tarski(u1_pre_topc(sK4)) = k5_setfam_1(u1_struct_0(sK4),u1_pre_topc(sK4))),
% 0.22/0.50    inference(resolution,[],[f123,f50])).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    ( ! [X2] : (~l1_pre_topc(X2) | k3_tarski(u1_pre_topc(X2)) = k5_setfam_1(u1_struct_0(X2),u1_pre_topc(X2))) )),
% 0.22/0.50    inference(resolution,[],[f73,f53])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k3_tarski(X1) = k5_setfam_1(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k3_tarski(X1) = k5_setfam_1(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    ( ! [X2,X0] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ! [X0] : ((sP0(X0) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK7(X0)),u1_pre_topc(X0)) & r1_tarski(sK7(X0),u1_pre_topc(X0)) & m1_subset_1(sK7(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) & (! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~sP0(X0)))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f43,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ! [X0] : (? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK7(X0)),u1_pre_topc(X0)) & r1_tarski(sK7(X0),u1_pre_topc(X0)) & m1_subset_1(sK7(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ! [X0] : ((sP0(X0) | ? [X1] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) & r1_tarski(X1,u1_pre_topc(X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) & (! [X2] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) | ~r1_tarski(X2,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~sP0(X0)))),
% 0.22/0.50    inference(rectify,[],[f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ! [X0] : ((sP0(X0) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) & (! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~sP0(X0)))),
% 0.22/0.50    inference(nnf_transformation,[],[f27])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (21545)------------------------------
% 0.22/0.50  % (21545)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (21545)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (21545)Memory used [KB]: 10746
% 0.22/0.50  % (21545)Time elapsed: 0.089 s
% 0.22/0.50  % (21545)------------------------------
% 0.22/0.50  % (21545)------------------------------
% 0.22/0.51  % (21519)Success in time 0.138 s
%------------------------------------------------------------------------------
