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
% DateTime   : Thu Dec  3 13:14:43 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 342 expanded)
%              Number of leaves         :   32 ( 135 expanded)
%              Depth                    :   15
%              Number of atoms          :  747 (1585 expanded)
%              Number of equality atoms :   81 ( 208 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f536,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f86,f104,f106,f158,f166,f183,f188,f192,f203,f210,f223,f283,f288,f296,f301,f309,f313,f317,f336,f503,f535])).

fof(f535,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | spl3_5
    | ~ spl3_15
    | ~ spl3_56 ),
    inference(avatar_contradiction_clause,[],[f534])).

fof(f534,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | spl3_5
    | ~ spl3_15
    | ~ spl3_56 ),
    inference(subsumption_resolution,[],[f533,f80])).

fof(f80,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f533,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_2
    | spl3_5
    | ~ spl3_15
    | ~ spl3_56 ),
    inference(subsumption_resolution,[],[f532,f98])).

fof(f98,plain,
    ( ~ v2_compts_1(sK1,sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl3_5
  <=> v2_compts_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f532,plain,
    ( v2_compts_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_2
    | ~ spl3_15
    | ~ spl3_56 ),
    inference(subsumption_resolution,[],[f530,f85])).

fof(f85,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f530,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_compts_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_15
    | ~ spl3_56 ),
    inference(resolution,[],[f502,f165])).

fof(f165,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl3_15
  <=> m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f502,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_compts_1(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f501])).

fof(f501,plain,
    ( spl3_56
  <=> ! [X0] :
        ( v2_compts_1(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f503,plain,
    ( spl3_56
    | ~ spl3_20
    | ~ spl3_22
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f344,f333,f220,f207,f501])).

fof(f207,plain,
    ( spl3_20
  <=> sK1 = k2_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f220,plain,
    ( spl3_22
  <=> v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f333,plain,
    ( spl3_36
  <=> sK1 = sK2(k1_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f344,plain,
    ( ! [X0] :
        ( v2_compts_1(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_20
    | ~ spl3_22
    | ~ spl3_36 ),
    inference(subsumption_resolution,[],[f343,f73])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f343,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,sK1)
        | v2_compts_1(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_20
    | ~ spl3_22
    | ~ spl3_36 ),
    inference(forward_demodulation,[],[f342,f209])).

fof(f209,plain,
    ( sK1 = k2_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f207])).

fof(f342,plain,
    ( ! [X0] :
        ( v2_compts_1(sK1,X0)
        | ~ r1_tarski(sK1,k2_struct_0(k1_pre_topc(sK0,sK1)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_22
    | ~ spl3_36 ),
    inference(subsumption_resolution,[],[f341,f221])).

fof(f221,plain,
    ( v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f220])).

fof(f341,plain,
    ( ! [X0] :
        ( ~ v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
        | v2_compts_1(sK1,X0)
        | ~ r1_tarski(sK1,k2_struct_0(k1_pre_topc(sK0,sK1)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(k1_pre_topc(sK0,sK1),X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_36 ),
    inference(superposition,[],[f59,f335])).

fof(f335,plain,
    ( sK1 = sK2(k1_pre_topc(sK0,sK1),sK1)
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f333])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_compts_1(sK2(X1,X2),X1)
      | v2_compts_1(X2,X0)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ( ~ v2_compts_1(sK2(X1,X2),X1)
                    & sK2(X1,X2) = X2
                    & m1_subset_1(sK2(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v2_compts_1(X4,X1)
                      | X2 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ v2_compts_1(X3,X1)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_compts_1(sK2(X1,X2),X1)
        & sK2(X1,X2) = X2
        & m1_subset_1(sK2(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ? [X3] :
                      ( ~ v2_compts_1(X3,X1)
                      & X2 = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v2_compts_1(X4,X1)
                      | X2 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ? [X3] :
                      ( ~ v2_compts_1(X3,X1)
                      & X2 = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v2_compts_1(X3,X1)
                      | X2 != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_compts_1(X2,X0)
              <=> ! [X3] :
                    ( v2_compts_1(X3,X1)
                    | X2 != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_compts_1(X2,X0)
              <=> ! [X3] :
                    ( v2_compts_1(X3,X1)
                    | X2 != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X2,k2_struct_0(X1))
               => ( v2_compts_1(X2,X0)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( X2 = X3
                       => v2_compts_1(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_compts_1)).

fof(f336,plain,
    ( spl3_36
    | spl3_5
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f328,f315,f97,f333])).

fof(f315,plain,
    ( spl3_33
  <=> ! [X2] :
        ( ~ r1_tarski(X2,sK1)
        | sK2(k1_pre_topc(sK0,sK1),X2) = X2
        | v2_compts_1(X2,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f328,plain,
    ( sK1 = sK2(k1_pre_topc(sK0,sK1),sK1)
    | spl3_5
    | ~ spl3_33 ),
    inference(subsumption_resolution,[],[f327,f98])).

fof(f327,plain,
    ( sK1 = sK2(k1_pre_topc(sK0,sK1),sK1)
    | v2_compts_1(sK1,sK0)
    | ~ spl3_33 ),
    inference(resolution,[],[f316,f73])).

fof(f316,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,sK1)
        | sK2(k1_pre_topc(sK0,sK1),X2) = X2
        | v2_compts_1(X2,sK0) )
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f315])).

fof(f317,plain,
    ( spl3_33
    | ~ spl3_1
    | ~ spl3_15
    | ~ spl3_20
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f303,f286,f207,f163,f78,f315])).

fof(f286,plain,
    ( spl3_30
  <=> ! [X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f303,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,sK1)
        | sK2(k1_pre_topc(sK0,sK1),X2) = X2
        | v2_compts_1(X2,sK0) )
    | ~ spl3_1
    | ~ spl3_15
    | ~ spl3_20
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f302,f287])).

fof(f287,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f286])).

fof(f302,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,sK1)
        | sK2(k1_pre_topc(sK0,sK1),X2) = X2
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_compts_1(X2,sK0) )
    | ~ spl3_1
    | ~ spl3_15
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f175,f209])).

fof(f175,plain,
    ( ! [X2] :
        ( sK2(k1_pre_topc(sK0,sK1),X2) = X2
        | ~ r1_tarski(X2,k2_struct_0(k1_pre_topc(sK0,sK1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_compts_1(X2,sK0) )
    | ~ spl3_1
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f169,f80])).

fof(f169,plain,
    ( ! [X2] :
        ( sK2(k1_pre_topc(sK0,sK1),X2) = X2
        | ~ r1_tarski(X2,k2_struct_0(k1_pre_topc(sK0,sK1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_compts_1(X2,sK0)
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_15 ),
    inference(resolution,[],[f165,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | sK2(X1,X2) = X2
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_compts_1(X2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f313,plain,
    ( spl3_22
    | ~ spl3_6
    | ~ spl3_17
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f312,f207,f185,f101,f220])).

fof(f101,plain,
    ( spl3_6
  <=> v1_compts_1(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f185,plain,
    ( spl3_17
  <=> l1_pre_topc(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f312,plain,
    ( v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
    | ~ spl3_6
    | ~ spl3_17
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f310,f103])).

fof(f103,plain,
    ( v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f101])).

fof(f310,plain,
    ( v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
    | ~ v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ spl3_17
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f212,f187])).

fof(f187,plain,
    ( l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f185])).

fof(f212,plain,
    ( v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
    | ~ v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl3_20 ),
    inference(superposition,[],[f52,f209])).

fof(f52,plain,(
    ! [X0] :
      ( v2_compts_1(k2_struct_0(X0),X0)
      | ~ v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( v1_compts_1(X0)
          | ~ v2_compts_1(k2_struct_0(X0),X0) )
        & ( v2_compts_1(k2_struct_0(X0),X0)
          | ~ v1_compts_1(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_compts_1(X0)
      <=> v2_compts_1(k2_struct_0(X0),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_compts_1)).

fof(f309,plain,
    ( ~ spl3_5
    | spl3_22
    | ~ spl3_32 ),
    inference(avatar_contradiction_clause,[],[f308])).

fof(f308,plain,
    ( $false
    | ~ spl3_5
    | spl3_22
    | ~ spl3_32 ),
    inference(subsumption_resolution,[],[f307,f99])).

fof(f99,plain,
    ( v2_compts_1(sK1,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f97])).

fof(f307,plain,
    ( ~ v2_compts_1(sK1,sK0)
    | spl3_22
    | ~ spl3_32 ),
    inference(subsumption_resolution,[],[f305,f222])).

fof(f222,plain,
    ( ~ v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
    | spl3_22 ),
    inference(avatar_component_clause,[],[f220])).

fof(f305,plain,
    ( v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
    | ~ v2_compts_1(sK1,sK0)
    | ~ spl3_32 ),
    inference(resolution,[],[f300,f73])).

fof(f300,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | v2_compts_1(X0,k1_pre_topc(sK0,sK1))
        | ~ v2_compts_1(X0,sK0) )
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f299])).

fof(f299,plain,
    ( spl3_32
  <=> ! [X0] :
        ( ~ v2_compts_1(X0,sK0)
        | v2_compts_1(X0,k1_pre_topc(sK0,sK1))
        | ~ r1_tarski(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f301,plain,
    ( spl3_32
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f297,f294,f299])).

fof(f294,plain,
    ( spl3_31
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | ~ v2_compts_1(X0,sK0)
        | v2_compts_1(X0,k1_pre_topc(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f297,plain,
    ( ! [X0] :
        ( ~ v2_compts_1(X0,sK0)
        | v2_compts_1(X0,k1_pre_topc(sK0,sK1))
        | ~ r1_tarski(X0,sK1) )
    | ~ spl3_31 ),
    inference(resolution,[],[f295,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f295,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | ~ v2_compts_1(X0,sK0)
        | v2_compts_1(X0,k1_pre_topc(sK0,sK1)) )
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f294])).

fof(f296,plain,
    ( spl3_31
    | ~ spl3_1
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f292,f207,f200,f163,f78,f294])).

fof(f200,plain,
    ( spl3_19
  <=> sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f292,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | ~ v2_compts_1(X0,sK0)
        | v2_compts_1(X0,k1_pre_topc(sK0,sK1)) )
    | ~ spl3_1
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f291,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f291,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | ~ v2_compts_1(X0,sK0)
        | v2_compts_1(X0,k1_pre_topc(sK0,sK1)) )
    | ~ spl3_1
    | ~ spl3_15
    | ~ spl3_19
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f290,f209])).

fof(f290,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | ~ v2_compts_1(X0,sK0)
        | ~ r1_tarski(X0,k2_struct_0(k1_pre_topc(sK0,sK1)))
        | v2_compts_1(X0,k1_pre_topc(sK0,sK1)) )
    | ~ spl3_1
    | ~ spl3_15
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f173,f202])).

fof(f202,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f200])).

fof(f173,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
        | ~ v2_compts_1(X0,sK0)
        | ~ r1_tarski(X0,k2_struct_0(k1_pre_topc(sK0,sK1)))
        | v2_compts_1(X0,k1_pre_topc(sK0,sK1)) )
    | ~ spl3_1
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f167,f80])).

% (29076)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
fof(f167,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
        | ~ v2_compts_1(X0,sK0)
        | ~ r1_tarski(X0,k2_struct_0(k1_pre_topc(sK0,sK1)))
        | v2_compts_1(X0,k1_pre_topc(sK0,sK1))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_15 ),
    inference(resolution,[],[f165,f161])).

fof(f161,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_compts_1(X4,X0)
      | ~ r1_tarski(X4,k2_struct_0(X1))
      | v2_compts_1(X4,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f70,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f70,plain,(
    ! [X4,X0,X1] :
      ( v2_compts_1(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_compts_1(X4,X0)
      | ~ r1_tarski(X4,k2_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_compts_1(X4,X1)
      | X2 != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_compts_1(X2,X0)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f288,plain,
    ( spl3_30
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f284,f281,f286])).

fof(f281,plain,
    ( spl3_29
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
        | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f284,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,sK1) )
    | ~ spl3_29 ),
    inference(resolution,[],[f282,f69])).

fof(f282,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
        | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f281])).

fof(f283,plain,
    ( spl3_29
    | ~ spl3_1
    | ~ spl3_15
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f279,f200,f163,f78,f281])).

fof(f279,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
        | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_1
    | ~ spl3_15
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f178,f202])).

fof(f178,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
        | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_1
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f171,f80])).

fof(f171,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1))))
        | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_15 ),
    inference(resolution,[],[f165,f55])).

fof(f223,plain,
    ( ~ spl3_22
    | spl3_6
    | ~ spl3_17
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f214,f207,f185,f101,f220])).

fof(f214,plain,
    ( ~ v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
    | spl3_6
    | ~ spl3_17
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f213,f187])).

fof(f213,plain,
    ( ~ v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | spl3_6
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f211,f102])).

fof(f102,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,sK1))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f101])).

fof(f211,plain,
    ( ~ v2_compts_1(sK1,k1_pre_topc(sK0,sK1))
    | v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl3_20 ),
    inference(superposition,[],[f53,f209])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v2_compts_1(k2_struct_0(X0),X0)
      | v1_compts_1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f210,plain,
    ( spl3_20
    | ~ spl3_2
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f204,f190,f83,f207])).

fof(f190,plain,
    ( spl3_18
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_struct_0(k1_pre_topc(sK0,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f204,plain,
    ( sK1 = k2_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_18 ),
    inference(resolution,[],[f191,f85])).

fof(f191,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_struct_0(k1_pre_topc(sK0,X0)) = X0 )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f190])).

fof(f203,plain,
    ( spl3_19
    | ~ spl3_2
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f197,f181,f83,f200])).

fof(f181,plain,
    ( spl3_16
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(k1_pre_topc(sK0,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f197,plain,
    ( sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_16 ),
    inference(resolution,[],[f182,f85])).

fof(f182,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(k1_pre_topc(sK0,X0)) = X0 )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f181])).

fof(f192,plain,
    ( spl3_18
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f154,f78,f190])).

fof(f154,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_struct_0(k1_pre_topc(sK0,X0)) = X0 )
    | ~ spl3_1 ),
    inference(resolution,[],[f153,f80])).

fof(f153,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    inference(subsumption_resolution,[],[f152,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f152,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f72,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_pre_topc(k1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k2_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_pre_topc(X0,X1) = X2
                  | k2_struct_0(X2) != X1 )
                & ( k2_struct_0(X2) = X1
                  | k1_pre_topc(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_pre_topc)).

fof(f188,plain,
    ( spl3_17
    | ~ spl3_1
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f179,f163,f78,f185])).

fof(f179,plain,
    ( l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f172,f80])).

fof(f172,plain,
    ( l1_pre_topc(k1_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_15 ),
    inference(resolution,[],[f165,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f183,plain,
    ( spl3_16
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f135,f78,f181])).

fof(f135,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(k1_pre_topc(sK0,X0)) = X0 )
    | ~ spl3_1 ),
    inference(resolution,[],[f60,f80])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f166,plain,
    ( spl3_15
    | ~ spl3_2
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f159,f156,f83,f163])).

fof(f156,plain,
    ( spl3_14
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_pre_topc(k1_pre_topc(sK0,X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f159,plain,
    ( m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)
    | ~ spl3_2
    | ~ spl3_14 ),
    inference(resolution,[],[f157,f85])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_pre_topc(k1_pre_topc(sK0,X0),sK0) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f156])).

fof(f158,plain,
    ( spl3_14
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f132,f78,f156])).

fof(f132,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_pre_topc(k1_pre_topc(sK0,X0),sK0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f64,f80])).

fof(f106,plain,
    ( ~ spl3_6
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f105,f97,f101])).

fof(f105,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f76,f99])).

fof(f76,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ v2_compts_1(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f51])).

fof(f51,plain,
    ( ~ v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ v2_compts_1(sK1,sK0)
    | ~ v1_compts_1(k1_pre_topc(sK0,sK1))
    | ~ v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ( ( ~ v1_compts_1(k1_pre_topc(sK0,sK1))
          | ~ v2_compts_1(sK1,sK0) )
        & ( v1_compts_1(k1_pre_topc(sK0,sK1))
          | v2_compts_1(sK1,sK0) )
        & k1_xboole_0 != sK1
        & v2_pre_topc(sK0) )
      | ( ( ~ v1_compts_1(k1_pre_topc(sK0,sK1))
          | ~ v2_compts_1(sK1,sK0) )
        & ( v1_compts_1(k1_pre_topc(sK0,sK1))
          | v2_compts_1(sK1,sK0) )
        & k1_xboole_0 = sK1 ) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ( ( ~ v1_compts_1(k1_pre_topc(X0,X1))
                  | ~ v2_compts_1(X1,X0) )
                & ( v1_compts_1(k1_pre_topc(X0,X1))
                  | v2_compts_1(X1,X0) )
                & k1_xboole_0 != X1
                & v2_pre_topc(X0) )
              | ( ( ~ v1_compts_1(k1_pre_topc(X0,X1))
                  | ~ v2_compts_1(X1,X0) )
                & ( v1_compts_1(k1_pre_topc(X0,X1))
                  | v2_compts_1(X1,X0) )
                & k1_xboole_0 = X1 ) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ( ( ~ v1_compts_1(k1_pre_topc(sK0,X1))
                | ~ v2_compts_1(X1,sK0) )
              & ( v1_compts_1(k1_pre_topc(sK0,X1))
                | v2_compts_1(X1,sK0) )
              & k1_xboole_0 != X1
              & v2_pre_topc(sK0) )
            | ( ( ~ v1_compts_1(k1_pre_topc(sK0,X1))
                | ~ v2_compts_1(X1,sK0) )
              & ( v1_compts_1(k1_pre_topc(sK0,X1))
                | v2_compts_1(X1,sK0) )
              & k1_xboole_0 = X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ( ( ( ~ v1_compts_1(k1_pre_topc(sK0,X1))
              | ~ v2_compts_1(X1,sK0) )
            & ( v1_compts_1(k1_pre_topc(sK0,X1))
              | v2_compts_1(X1,sK0) )
            & k1_xboole_0 != X1
            & v2_pre_topc(sK0) )
          | ( ( ~ v1_compts_1(k1_pre_topc(sK0,X1))
              | ~ v2_compts_1(X1,sK0) )
            & ( v1_compts_1(k1_pre_topc(sK0,X1))
              | v2_compts_1(X1,sK0) )
            & k1_xboole_0 = X1 ) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ( ( ~ v1_compts_1(k1_pre_topc(sK0,sK1))
            | ~ v2_compts_1(sK1,sK0) )
          & ( v1_compts_1(k1_pre_topc(sK0,sK1))
            | v2_compts_1(sK1,sK0) )
          & k1_xboole_0 != sK1
          & v2_pre_topc(sK0) )
        | ( ( ~ v1_compts_1(k1_pre_topc(sK0,sK1))
            | ~ v2_compts_1(sK1,sK0) )
          & ( v1_compts_1(k1_pre_topc(sK0,sK1))
            | v2_compts_1(sK1,sK0) )
          & k1_xboole_0 = sK1 ) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ( ~ v1_compts_1(k1_pre_topc(X0,X1))
                | ~ v2_compts_1(X1,X0) )
              & ( v1_compts_1(k1_pre_topc(X0,X1))
                | v2_compts_1(X1,X0) )
              & k1_xboole_0 != X1
              & v2_pre_topc(X0) )
            | ( ( ~ v1_compts_1(k1_pre_topc(X0,X1))
                | ~ v2_compts_1(X1,X0) )
              & ( v1_compts_1(k1_pre_topc(X0,X1))
                | v2_compts_1(X1,X0) )
              & k1_xboole_0 = X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ( ~ v1_compts_1(k1_pre_topc(X0,X1))
                | ~ v2_compts_1(X1,X0) )
              & ( v1_compts_1(k1_pre_topc(X0,X1))
                | v2_compts_1(X1,X0) )
              & k1_xboole_0 != X1
              & v2_pre_topc(X0) )
            | ( ( ~ v1_compts_1(k1_pre_topc(X0,X1))
                | ~ v2_compts_1(X1,X0) )
              & ( v1_compts_1(k1_pre_topc(X0,X1))
                | v2_compts_1(X1,X0) )
              & k1_xboole_0 = X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ( v2_compts_1(X1,X0)
              <~> v1_compts_1(k1_pre_topc(X0,X1)) )
              & k1_xboole_0 != X1
              & v2_pre_topc(X0) )
            | ( ( v2_compts_1(X1,X0)
              <~> v1_compts_1(k1_pre_topc(X0,X1)) )
              & k1_xboole_0 = X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( ( v2_compts_1(X1,X0)
              <~> v1_compts_1(k1_pre_topc(X0,X1)) )
              & k1_xboole_0 != X1
              & v2_pre_topc(X0) )
            | ( ( v2_compts_1(X1,X0)
              <~> v1_compts_1(k1_pre_topc(X0,X1)) )
              & k1_xboole_0 = X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v2_pre_topc(X0)
               => ( ( v2_compts_1(X1,X0)
                  <=> v1_compts_1(k1_pre_topc(X0,X1)) )
                  | k1_xboole_0 = X1 ) )
              & ( k1_xboole_0 = X1
               => ( v2_compts_1(X1,X0)
                <=> v1_compts_1(k1_pre_topc(X0,X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_pre_topc(X0)
             => ( ( v2_compts_1(X1,X0)
                <=> v1_compts_1(k1_pre_topc(X0,X1)) )
                | k1_xboole_0 = X1 ) )
            & ( k1_xboole_0 = X1
             => ( v2_compts_1(X1,X0)
              <=> v1_compts_1(k1_pre_topc(X0,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_compts_1)).

fof(f104,plain,
    ( spl3_5
    | spl3_6 ),
    inference(avatar_split_clause,[],[f75,f101,f97])).

fof(f75,plain,
    ( v1_compts_1(k1_pre_topc(sK0,sK1))
    | v2_compts_1(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f47])).

fof(f47,plain,
    ( v1_compts_1(k1_pre_topc(sK0,sK1))
    | v2_compts_1(sK1,sK0)
    | v1_compts_1(k1_pre_topc(sK0,sK1))
    | v2_compts_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f86,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f39,f83])).

fof(f39,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f81,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f38,f78])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:45:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (29078)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (29079)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (29088)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (29082)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.51  % (29071)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (29091)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.51  % (29090)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (29087)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (29073)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (29068)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (29083)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (29074)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (29067)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (29081)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (29075)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (29069)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.25/0.52  % (29066)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.25/0.52  % (29089)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.25/0.52  % (29068)Refutation found. Thanks to Tanya!
% 1.25/0.52  % SZS status Theorem for theBenchmark
% 1.25/0.52  % (29066)Refutation not found, incomplete strategy% (29066)------------------------------
% 1.25/0.52  % (29066)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (29066)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (29066)Memory used [KB]: 10618
% 1.25/0.52  % (29066)Time elapsed: 0.104 s
% 1.25/0.52  % (29066)------------------------------
% 1.25/0.52  % (29066)------------------------------
% 1.25/0.52  % (29070)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.25/0.52  % (29072)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.25/0.52  % (29080)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.25/0.53  % (29071)Refutation not found, incomplete strategy% (29071)------------------------------
% 1.25/0.53  % (29071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  % (29071)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.53  
% 1.25/0.53  % (29071)Memory used [KB]: 6140
% 1.25/0.53  % (29071)Time elapsed: 0.096 s
% 1.25/0.53  % (29071)------------------------------
% 1.25/0.53  % (29071)------------------------------
% 1.25/0.53  % (29084)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.25/0.53  % (29085)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.25/0.53  % (29072)Refutation not found, incomplete strategy% (29072)------------------------------
% 1.25/0.53  % (29072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  % (29072)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.53  
% 1.25/0.53  % (29072)Memory used [KB]: 10618
% 1.25/0.53  % (29072)Time elapsed: 0.078 s
% 1.25/0.53  % (29072)------------------------------
% 1.25/0.53  % (29072)------------------------------
% 1.25/0.53  % (29086)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.25/0.54  % (29077)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.25/0.54  % (29077)Refutation not found, incomplete strategy% (29077)------------------------------
% 1.25/0.54  % (29077)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.54  % (29077)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.54  
% 1.25/0.54  % (29077)Memory used [KB]: 10618
% 1.25/0.54  % (29077)Time elapsed: 0.130 s
% 1.25/0.54  % (29077)------------------------------
% 1.25/0.54  % (29077)------------------------------
% 1.42/0.54  % SZS output start Proof for theBenchmark
% 1.42/0.54  fof(f536,plain,(
% 1.42/0.54    $false),
% 1.42/0.54    inference(avatar_sat_refutation,[],[f81,f86,f104,f106,f158,f166,f183,f188,f192,f203,f210,f223,f283,f288,f296,f301,f309,f313,f317,f336,f503,f535])).
% 1.42/0.54  fof(f535,plain,(
% 1.42/0.54    ~spl3_1 | ~spl3_2 | spl3_5 | ~spl3_15 | ~spl3_56),
% 1.42/0.54    inference(avatar_contradiction_clause,[],[f534])).
% 1.42/0.54  fof(f534,plain,(
% 1.42/0.54    $false | (~spl3_1 | ~spl3_2 | spl3_5 | ~spl3_15 | ~spl3_56)),
% 1.42/0.54    inference(subsumption_resolution,[],[f533,f80])).
% 1.42/0.54  fof(f80,plain,(
% 1.42/0.54    l1_pre_topc(sK0) | ~spl3_1),
% 1.42/0.54    inference(avatar_component_clause,[],[f78])).
% 1.42/0.54  fof(f78,plain,(
% 1.42/0.54    spl3_1 <=> l1_pre_topc(sK0)),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.42/0.54  fof(f533,plain,(
% 1.42/0.54    ~l1_pre_topc(sK0) | (~spl3_2 | spl3_5 | ~spl3_15 | ~spl3_56)),
% 1.42/0.54    inference(subsumption_resolution,[],[f532,f98])).
% 1.42/0.54  fof(f98,plain,(
% 1.42/0.54    ~v2_compts_1(sK1,sK0) | spl3_5),
% 1.42/0.54    inference(avatar_component_clause,[],[f97])).
% 1.42/0.54  fof(f97,plain,(
% 1.42/0.54    spl3_5 <=> v2_compts_1(sK1,sK0)),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.42/0.54  fof(f532,plain,(
% 1.42/0.54    v2_compts_1(sK1,sK0) | ~l1_pre_topc(sK0) | (~spl3_2 | ~spl3_15 | ~spl3_56)),
% 1.42/0.54    inference(subsumption_resolution,[],[f530,f85])).
% 1.42/0.54  fof(f85,plain,(
% 1.42/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 1.42/0.54    inference(avatar_component_clause,[],[f83])).
% 1.42/0.54  fof(f83,plain,(
% 1.42/0.54    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.42/0.54  fof(f530,plain,(
% 1.42/0.54    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_compts_1(sK1,sK0) | ~l1_pre_topc(sK0) | (~spl3_15 | ~spl3_56)),
% 1.42/0.54    inference(resolution,[],[f502,f165])).
% 1.42/0.54  fof(f165,plain,(
% 1.42/0.54    m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | ~spl3_15),
% 1.42/0.54    inference(avatar_component_clause,[],[f163])).
% 1.42/0.54  fof(f163,plain,(
% 1.42/0.54    spl3_15 <=> m1_pre_topc(k1_pre_topc(sK0,sK1),sK0)),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 1.42/0.54  fof(f502,plain,(
% 1.42/0.54    ( ! [X0] : (~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | v2_compts_1(sK1,X0) | ~l1_pre_topc(X0)) ) | ~spl3_56),
% 1.42/0.54    inference(avatar_component_clause,[],[f501])).
% 1.42/0.54  fof(f501,plain,(
% 1.42/0.54    spl3_56 <=> ! [X0] : (v2_compts_1(sK1,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~l1_pre_topc(X0))),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 1.42/0.54  fof(f503,plain,(
% 1.42/0.54    spl3_56 | ~spl3_20 | ~spl3_22 | ~spl3_36),
% 1.42/0.54    inference(avatar_split_clause,[],[f344,f333,f220,f207,f501])).
% 1.42/0.54  fof(f207,plain,(
% 1.42/0.54    spl3_20 <=> sK1 = k2_struct_0(k1_pre_topc(sK0,sK1))),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 1.42/0.54  fof(f220,plain,(
% 1.42/0.54    spl3_22 <=> v2_compts_1(sK1,k1_pre_topc(sK0,sK1))),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 1.42/0.54  fof(f333,plain,(
% 1.42/0.54    spl3_36 <=> sK1 = sK2(k1_pre_topc(sK0,sK1),sK1)),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 1.42/0.54  fof(f344,plain,(
% 1.42/0.54    ( ! [X0] : (v2_compts_1(sK1,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~l1_pre_topc(X0)) ) | (~spl3_20 | ~spl3_22 | ~spl3_36)),
% 1.42/0.54    inference(subsumption_resolution,[],[f343,f73])).
% 1.42/0.54  fof(f73,plain,(
% 1.42/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.42/0.54    inference(equality_resolution,[],[f66])).
% 1.42/0.54  fof(f66,plain,(
% 1.42/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.42/0.54    inference(cnf_transformation,[],[f36])).
% 1.42/0.54  fof(f36,plain,(
% 1.42/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.42/0.54    inference(flattening,[],[f35])).
% 1.42/0.54  fof(f35,plain,(
% 1.42/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.42/0.54    inference(nnf_transformation,[],[f1])).
% 1.42/0.54  fof(f1,axiom,(
% 1.42/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.42/0.54  fof(f343,plain,(
% 1.42/0.54    ( ! [X0] : (~r1_tarski(sK1,sK1) | v2_compts_1(sK1,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~l1_pre_topc(X0)) ) | (~spl3_20 | ~spl3_22 | ~spl3_36)),
% 1.42/0.54    inference(forward_demodulation,[],[f342,f209])).
% 1.42/0.54  fof(f209,plain,(
% 1.42/0.54    sK1 = k2_struct_0(k1_pre_topc(sK0,sK1)) | ~spl3_20),
% 1.42/0.54    inference(avatar_component_clause,[],[f207])).
% 1.42/0.54  fof(f342,plain,(
% 1.42/0.54    ( ! [X0] : (v2_compts_1(sK1,X0) | ~r1_tarski(sK1,k2_struct_0(k1_pre_topc(sK0,sK1))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~l1_pre_topc(X0)) ) | (~spl3_22 | ~spl3_36)),
% 1.42/0.54    inference(subsumption_resolution,[],[f341,f221])).
% 1.42/0.54  fof(f221,plain,(
% 1.42/0.54    v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) | ~spl3_22),
% 1.42/0.54    inference(avatar_component_clause,[],[f220])).
% 1.42/0.54  fof(f341,plain,(
% 1.42/0.54    ( ! [X0] : (~v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) | v2_compts_1(sK1,X0) | ~r1_tarski(sK1,k2_struct_0(k1_pre_topc(sK0,sK1))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(k1_pre_topc(sK0,sK1),X0) | ~l1_pre_topc(X0)) ) | ~spl3_36),
% 1.42/0.54    inference(superposition,[],[f59,f335])).
% 1.42/0.54  fof(f335,plain,(
% 1.42/0.54    sK1 = sK2(k1_pre_topc(sK0,sK1),sK1) | ~spl3_36),
% 1.42/0.54    inference(avatar_component_clause,[],[f333])).
% 1.42/0.54  fof(f59,plain,(
% 1.42/0.54    ( ! [X2,X0,X1] : (~v2_compts_1(sK2(X1,X2),X1) | v2_compts_1(X2,X0) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f33])).
% 1.42/0.54  fof(f33,plain,(
% 1.42/0.54    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | (~v2_compts_1(sK2(X1,X2),X1) & sK2(X1,X2) = X2 & m1_subset_1(sK2(X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.42/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).
% 1.42/0.54  fof(f32,plain,(
% 1.42/0.54    ! [X2,X1] : (? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v2_compts_1(sK2(X1,X2),X1) & sK2(X1,X2) = X2 & m1_subset_1(sK2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 1.42/0.54    introduced(choice_axiom,[])).
% 1.42/0.54  fof(f31,plain,(
% 1.42/0.54    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | ? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.42/0.54    inference(rectify,[],[f30])).
% 1.42/0.54  fof(f30,plain,(
% 1.42/0.54    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | ? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.42/0.54    inference(nnf_transformation,[],[f18])).
% 1.42/0.54  fof(f18,plain,(
% 1.42/0.54    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) <=> ! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.42/0.54    inference(flattening,[],[f17])).
% 1.42/0.54  fof(f17,plain,(
% 1.42/0.54    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) <=> ! [X3] : ((v2_compts_1(X3,X1) | X2 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.42/0.54    inference(ennf_transformation,[],[f9])).
% 1.42/0.54  fof(f9,axiom,(
% 1.42/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,k2_struct_0(X1)) => (v2_compts_1(X2,X0) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => v2_compts_1(X3,X1))))))))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_compts_1)).
% 1.42/0.54  fof(f336,plain,(
% 1.42/0.54    spl3_36 | spl3_5 | ~spl3_33),
% 1.42/0.54    inference(avatar_split_clause,[],[f328,f315,f97,f333])).
% 1.42/0.54  fof(f315,plain,(
% 1.42/0.54    spl3_33 <=> ! [X2] : (~r1_tarski(X2,sK1) | sK2(k1_pre_topc(sK0,sK1),X2) = X2 | v2_compts_1(X2,sK0))),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 1.42/0.54  fof(f328,plain,(
% 1.42/0.54    sK1 = sK2(k1_pre_topc(sK0,sK1),sK1) | (spl3_5 | ~spl3_33)),
% 1.42/0.54    inference(subsumption_resolution,[],[f327,f98])).
% 1.42/0.54  fof(f327,plain,(
% 1.42/0.54    sK1 = sK2(k1_pre_topc(sK0,sK1),sK1) | v2_compts_1(sK1,sK0) | ~spl3_33),
% 1.42/0.54    inference(resolution,[],[f316,f73])).
% 1.42/0.54  fof(f316,plain,(
% 1.42/0.54    ( ! [X2] : (~r1_tarski(X2,sK1) | sK2(k1_pre_topc(sK0,sK1),X2) = X2 | v2_compts_1(X2,sK0)) ) | ~spl3_33),
% 1.42/0.54    inference(avatar_component_clause,[],[f315])).
% 1.42/0.54  fof(f317,plain,(
% 1.42/0.54    spl3_33 | ~spl3_1 | ~spl3_15 | ~spl3_20 | ~spl3_30),
% 1.42/0.54    inference(avatar_split_clause,[],[f303,f286,f207,f163,f78,f315])).
% 1.42/0.54  fof(f286,plain,(
% 1.42/0.54    spl3_30 <=> ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1))),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 1.42/0.54  fof(f303,plain,(
% 1.42/0.54    ( ! [X2] : (~r1_tarski(X2,sK1) | sK2(k1_pre_topc(sK0,sK1),X2) = X2 | v2_compts_1(X2,sK0)) ) | (~spl3_1 | ~spl3_15 | ~spl3_20 | ~spl3_30)),
% 1.42/0.54    inference(subsumption_resolution,[],[f302,f287])).
% 1.42/0.54  fof(f287,plain,(
% 1.42/0.54    ( ! [X0] : (~r1_tarski(X0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_30),
% 1.42/0.54    inference(avatar_component_clause,[],[f286])).
% 1.42/0.54  fof(f302,plain,(
% 1.42/0.54    ( ! [X2] : (~r1_tarski(X2,sK1) | sK2(k1_pre_topc(sK0,sK1),X2) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_compts_1(X2,sK0)) ) | (~spl3_1 | ~spl3_15 | ~spl3_20)),
% 1.42/0.54    inference(forward_demodulation,[],[f175,f209])).
% 1.42/0.54  fof(f175,plain,(
% 1.42/0.54    ( ! [X2] : (sK2(k1_pre_topc(sK0,sK1),X2) = X2 | ~r1_tarski(X2,k2_struct_0(k1_pre_topc(sK0,sK1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_compts_1(X2,sK0)) ) | (~spl3_1 | ~spl3_15)),
% 1.42/0.54    inference(subsumption_resolution,[],[f169,f80])).
% 1.42/0.54  fof(f169,plain,(
% 1.42/0.54    ( ! [X2] : (sK2(k1_pre_topc(sK0,sK1),X2) = X2 | ~r1_tarski(X2,k2_struct_0(k1_pre_topc(sK0,sK1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_compts_1(X2,sK0) | ~l1_pre_topc(sK0)) ) | ~spl3_15),
% 1.42/0.54    inference(resolution,[],[f165,f58])).
% 1.42/0.54  fof(f58,plain,(
% 1.42/0.54    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | sK2(X1,X2) = X2 | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v2_compts_1(X2,X0) | ~l1_pre_topc(X0)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f33])).
% 1.42/0.54  fof(f313,plain,(
% 1.42/0.54    spl3_22 | ~spl3_6 | ~spl3_17 | ~spl3_20),
% 1.42/0.54    inference(avatar_split_clause,[],[f312,f207,f185,f101,f220])).
% 1.42/0.54  fof(f101,plain,(
% 1.42/0.54    spl3_6 <=> v1_compts_1(k1_pre_topc(sK0,sK1))),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.42/0.54  fof(f185,plain,(
% 1.42/0.54    spl3_17 <=> l1_pre_topc(k1_pre_topc(sK0,sK1))),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 1.42/0.54  fof(f312,plain,(
% 1.42/0.54    v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) | (~spl3_6 | ~spl3_17 | ~spl3_20)),
% 1.42/0.54    inference(subsumption_resolution,[],[f310,f103])).
% 1.42/0.54  fof(f103,plain,(
% 1.42/0.54    v1_compts_1(k1_pre_topc(sK0,sK1)) | ~spl3_6),
% 1.42/0.54    inference(avatar_component_clause,[],[f101])).
% 1.42/0.54  fof(f310,plain,(
% 1.42/0.54    v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) | ~v1_compts_1(k1_pre_topc(sK0,sK1)) | (~spl3_17 | ~spl3_20)),
% 1.42/0.54    inference(subsumption_resolution,[],[f212,f187])).
% 1.42/0.54  fof(f187,plain,(
% 1.42/0.54    l1_pre_topc(k1_pre_topc(sK0,sK1)) | ~spl3_17),
% 1.42/0.54    inference(avatar_component_clause,[],[f185])).
% 1.42/0.54  fof(f212,plain,(
% 1.42/0.54    v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) | ~v1_compts_1(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | ~spl3_20),
% 1.42/0.54    inference(superposition,[],[f52,f209])).
% 1.42/0.54  fof(f52,plain,(
% 1.42/0.54    ( ! [X0] : (v2_compts_1(k2_struct_0(X0),X0) | ~v1_compts_1(X0) | ~l1_pre_topc(X0)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f29])).
% 1.42/0.54  fof(f29,plain,(
% 1.42/0.54    ! [X0] : (((v1_compts_1(X0) | ~v2_compts_1(k2_struct_0(X0),X0)) & (v2_compts_1(k2_struct_0(X0),X0) | ~v1_compts_1(X0))) | ~l1_pre_topc(X0))),
% 1.42/0.54    inference(nnf_transformation,[],[f14])).
% 1.42/0.54  fof(f14,plain,(
% 1.42/0.54    ! [X0] : ((v1_compts_1(X0) <=> v2_compts_1(k2_struct_0(X0),X0)) | ~l1_pre_topc(X0))),
% 1.42/0.54    inference(ennf_transformation,[],[f8])).
% 1.42/0.54  fof(f8,axiom,(
% 1.42/0.54    ! [X0] : (l1_pre_topc(X0) => (v1_compts_1(X0) <=> v2_compts_1(k2_struct_0(X0),X0)))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_compts_1)).
% 1.42/0.54  fof(f309,plain,(
% 1.42/0.54    ~spl3_5 | spl3_22 | ~spl3_32),
% 1.42/0.54    inference(avatar_contradiction_clause,[],[f308])).
% 1.42/0.54  fof(f308,plain,(
% 1.42/0.54    $false | (~spl3_5 | spl3_22 | ~spl3_32)),
% 1.42/0.54    inference(subsumption_resolution,[],[f307,f99])).
% 1.42/0.54  fof(f99,plain,(
% 1.42/0.54    v2_compts_1(sK1,sK0) | ~spl3_5),
% 1.42/0.54    inference(avatar_component_clause,[],[f97])).
% 1.42/0.54  fof(f307,plain,(
% 1.42/0.54    ~v2_compts_1(sK1,sK0) | (spl3_22 | ~spl3_32)),
% 1.42/0.54    inference(subsumption_resolution,[],[f305,f222])).
% 1.42/0.54  fof(f222,plain,(
% 1.42/0.54    ~v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) | spl3_22),
% 1.42/0.54    inference(avatar_component_clause,[],[f220])).
% 1.42/0.54  fof(f305,plain,(
% 1.42/0.54    v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) | ~v2_compts_1(sK1,sK0) | ~spl3_32),
% 1.42/0.54    inference(resolution,[],[f300,f73])).
% 1.42/0.54  fof(f300,plain,(
% 1.42/0.54    ( ! [X0] : (~r1_tarski(X0,sK1) | v2_compts_1(X0,k1_pre_topc(sK0,sK1)) | ~v2_compts_1(X0,sK0)) ) | ~spl3_32),
% 1.42/0.54    inference(avatar_component_clause,[],[f299])).
% 1.42/0.54  fof(f299,plain,(
% 1.42/0.54    spl3_32 <=> ! [X0] : (~v2_compts_1(X0,sK0) | v2_compts_1(X0,k1_pre_topc(sK0,sK1)) | ~r1_tarski(X0,sK1))),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 1.42/0.54  fof(f301,plain,(
% 1.42/0.54    spl3_32 | ~spl3_31),
% 1.42/0.54    inference(avatar_split_clause,[],[f297,f294,f299])).
% 1.42/0.54  fof(f294,plain,(
% 1.42/0.54    spl3_31 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~v2_compts_1(X0,sK0) | v2_compts_1(X0,k1_pre_topc(sK0,sK1)))),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 1.42/0.54  fof(f297,plain,(
% 1.42/0.54    ( ! [X0] : (~v2_compts_1(X0,sK0) | v2_compts_1(X0,k1_pre_topc(sK0,sK1)) | ~r1_tarski(X0,sK1)) ) | ~spl3_31),
% 1.42/0.54    inference(resolution,[],[f295,f69])).
% 1.42/0.54  fof(f69,plain,(
% 1.42/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f37])).
% 1.42/0.54  fof(f37,plain,(
% 1.42/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.42/0.54    inference(nnf_transformation,[],[f2])).
% 1.42/0.54  fof(f2,axiom,(
% 1.42/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.42/0.54  fof(f295,plain,(
% 1.42/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~v2_compts_1(X0,sK0) | v2_compts_1(X0,k1_pre_topc(sK0,sK1))) ) | ~spl3_31),
% 1.42/0.54    inference(avatar_component_clause,[],[f294])).
% 1.42/0.54  fof(f296,plain,(
% 1.42/0.54    spl3_31 | ~spl3_1 | ~spl3_15 | ~spl3_19 | ~spl3_20),
% 1.42/0.54    inference(avatar_split_clause,[],[f292,f207,f200,f163,f78,f294])).
% 1.42/0.54  fof(f200,plain,(
% 1.42/0.54    spl3_19 <=> sK1 = u1_struct_0(k1_pre_topc(sK0,sK1))),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 1.42/0.54  fof(f292,plain,(
% 1.42/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~v2_compts_1(X0,sK0) | v2_compts_1(X0,k1_pre_topc(sK0,sK1))) ) | (~spl3_1 | ~spl3_15 | ~spl3_19 | ~spl3_20)),
% 1.42/0.54    inference(subsumption_resolution,[],[f291,f68])).
% 1.42/0.54  fof(f68,plain,(
% 1.42/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f37])).
% 1.42/0.54  fof(f291,plain,(
% 1.42/0.54    ( ! [X0] : (~r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~v2_compts_1(X0,sK0) | v2_compts_1(X0,k1_pre_topc(sK0,sK1))) ) | (~spl3_1 | ~spl3_15 | ~spl3_19 | ~spl3_20)),
% 1.42/0.54    inference(forward_demodulation,[],[f290,f209])).
% 1.42/0.54  fof(f290,plain,(
% 1.42/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~v2_compts_1(X0,sK0) | ~r1_tarski(X0,k2_struct_0(k1_pre_topc(sK0,sK1))) | v2_compts_1(X0,k1_pre_topc(sK0,sK1))) ) | (~spl3_1 | ~spl3_15 | ~spl3_19)),
% 1.42/0.54    inference(forward_demodulation,[],[f173,f202])).
% 1.42/0.54  fof(f202,plain,(
% 1.42/0.54    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) | ~spl3_19),
% 1.42/0.54    inference(avatar_component_clause,[],[f200])).
% 1.42/0.54  fof(f173,plain,(
% 1.42/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) | ~v2_compts_1(X0,sK0) | ~r1_tarski(X0,k2_struct_0(k1_pre_topc(sK0,sK1))) | v2_compts_1(X0,k1_pre_topc(sK0,sK1))) ) | (~spl3_1 | ~spl3_15)),
% 1.42/0.54    inference(subsumption_resolution,[],[f167,f80])).
% 1.42/0.54  % (29076)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.42/0.54  fof(f167,plain,(
% 1.42/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) | ~v2_compts_1(X0,sK0) | ~r1_tarski(X0,k2_struct_0(k1_pre_topc(sK0,sK1))) | v2_compts_1(X0,k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0)) ) | ~spl3_15),
% 1.42/0.54    inference(resolution,[],[f165,f161])).
% 1.42/0.54  fof(f161,plain,(
% 1.42/0.54    ( ! [X4,X0,X1] : (~m1_pre_topc(X1,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_compts_1(X4,X0) | ~r1_tarski(X4,k2_struct_0(X1)) | v2_compts_1(X4,X1) | ~l1_pre_topc(X0)) )),
% 1.42/0.54    inference(subsumption_resolution,[],[f70,f55])).
% 1.42/0.54  fof(f55,plain,(
% 1.42/0.54    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f16])).
% 1.42/0.54  fof(f16,plain,(
% 1.42/0.54    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.42/0.54    inference(ennf_transformation,[],[f7])).
% 1.42/0.54  fof(f7,axiom,(
% 1.42/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).
% 1.42/0.54  fof(f70,plain,(
% 1.42/0.54    ( ! [X4,X0,X1] : (v2_compts_1(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_compts_1(X4,X0) | ~r1_tarski(X4,k2_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.42/0.54    inference(equality_resolution,[],[f56])).
% 1.42/0.54  fof(f56,plain,(
% 1.42/0.54    ( ! [X4,X2,X0,X1] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_compts_1(X2,X0) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f33])).
% 1.42/0.54  fof(f288,plain,(
% 1.42/0.54    spl3_30 | ~spl3_29),
% 1.42/0.54    inference(avatar_split_clause,[],[f284,f281,f286])).
% 1.42/0.54  fof(f281,plain,(
% 1.42/0.54    spl3_29 <=> ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(sK1)) | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 1.42/0.54  fof(f284,plain,(
% 1.42/0.54    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1)) ) | ~spl3_29),
% 1.42/0.54    inference(resolution,[],[f282,f69])).
% 1.42/0.54  fof(f282,plain,(
% 1.42/0.54    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(sK1)) | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_29),
% 1.42/0.54    inference(avatar_component_clause,[],[f281])).
% 1.42/0.54  fof(f283,plain,(
% 1.42/0.54    spl3_29 | ~spl3_1 | ~spl3_15 | ~spl3_19),
% 1.42/0.54    inference(avatar_split_clause,[],[f279,f200,f163,f78,f281])).
% 1.42/0.54  fof(f279,plain,(
% 1.42/0.54    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(sK1)) | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_1 | ~spl3_15 | ~spl3_19)),
% 1.42/0.54    inference(forward_demodulation,[],[f178,f202])).
% 1.42/0.54  fof(f178,plain,(
% 1.42/0.54    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_1 | ~spl3_15)),
% 1.42/0.54    inference(subsumption_resolution,[],[f171,f80])).
% 1.42/0.54  fof(f171,plain,(
% 1.42/0.54    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK1)))) | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl3_15),
% 1.42/0.54    inference(resolution,[],[f165,f55])).
% 1.42/0.54  fof(f223,plain,(
% 1.42/0.54    ~spl3_22 | spl3_6 | ~spl3_17 | ~spl3_20),
% 1.42/0.54    inference(avatar_split_clause,[],[f214,f207,f185,f101,f220])).
% 1.42/0.54  fof(f214,plain,(
% 1.42/0.54    ~v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) | (spl3_6 | ~spl3_17 | ~spl3_20)),
% 1.42/0.54    inference(subsumption_resolution,[],[f213,f187])).
% 1.42/0.54  fof(f213,plain,(
% 1.42/0.54    ~v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | (spl3_6 | ~spl3_20)),
% 1.42/0.54    inference(subsumption_resolution,[],[f211,f102])).
% 1.42/0.54  fof(f102,plain,(
% 1.42/0.54    ~v1_compts_1(k1_pre_topc(sK0,sK1)) | spl3_6),
% 1.42/0.54    inference(avatar_component_clause,[],[f101])).
% 1.42/0.54  fof(f211,plain,(
% 1.42/0.54    ~v2_compts_1(sK1,k1_pre_topc(sK0,sK1)) | v1_compts_1(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(k1_pre_topc(sK0,sK1)) | ~spl3_20),
% 1.42/0.54    inference(superposition,[],[f53,f209])).
% 1.42/0.54  fof(f53,plain,(
% 1.42/0.54    ( ! [X0] : (~v2_compts_1(k2_struct_0(X0),X0) | v1_compts_1(X0) | ~l1_pre_topc(X0)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f29])).
% 1.42/0.54  fof(f210,plain,(
% 1.42/0.54    spl3_20 | ~spl3_2 | ~spl3_18),
% 1.42/0.54    inference(avatar_split_clause,[],[f204,f190,f83,f207])).
% 1.42/0.54  fof(f190,plain,(
% 1.42/0.54    spl3_18 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(k1_pre_topc(sK0,X0)) = X0)),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 1.42/0.54  fof(f204,plain,(
% 1.42/0.54    sK1 = k2_struct_0(k1_pre_topc(sK0,sK1)) | (~spl3_2 | ~spl3_18)),
% 1.42/0.54    inference(resolution,[],[f191,f85])).
% 1.42/0.54  fof(f191,plain,(
% 1.42/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(k1_pre_topc(sK0,X0)) = X0) ) | ~spl3_18),
% 1.42/0.54    inference(avatar_component_clause,[],[f190])).
% 1.42/0.54  fof(f203,plain,(
% 1.42/0.54    spl3_19 | ~spl3_2 | ~spl3_16),
% 1.42/0.54    inference(avatar_split_clause,[],[f197,f181,f83,f200])).
% 1.42/0.54  fof(f181,plain,(
% 1.42/0.54    spl3_16 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(k1_pre_topc(sK0,X0)) = X0)),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.42/0.54  fof(f197,plain,(
% 1.42/0.54    sK1 = u1_struct_0(k1_pre_topc(sK0,sK1)) | (~spl3_2 | ~spl3_16)),
% 1.42/0.54    inference(resolution,[],[f182,f85])).
% 1.42/0.54  fof(f182,plain,(
% 1.42/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(k1_pre_topc(sK0,X0)) = X0) ) | ~spl3_16),
% 1.42/0.54    inference(avatar_component_clause,[],[f181])).
% 1.42/0.54  fof(f192,plain,(
% 1.42/0.54    spl3_18 | ~spl3_1),
% 1.42/0.54    inference(avatar_split_clause,[],[f154,f78,f190])).
% 1.42/0.54  fof(f154,plain,(
% 1.42/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(k1_pre_topc(sK0,X0)) = X0) ) | ~spl3_1),
% 1.42/0.54    inference(resolution,[],[f153,f80])).
% 1.42/0.54  fof(f153,plain,(
% 1.42/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(k1_pre_topc(X0,X1)) = X1) )),
% 1.42/0.54    inference(subsumption_resolution,[],[f152,f64])).
% 1.42/0.54  fof(f64,plain,(
% 1.42/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(k1_pre_topc(X0,X1),X0)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f23])).
% 1.42/0.54  fof(f23,plain,(
% 1.42/0.54    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.42/0.54    inference(flattening,[],[f22])).
% 1.42/0.54  fof(f22,plain,(
% 1.42/0.54    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.42/0.54    inference(ennf_transformation,[],[f4])).
% 1.42/0.54  fof(f4,axiom,(
% 1.42/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 1.42/0.54  fof(f152,plain,(
% 1.42/0.54    ( ! [X0,X1] : (k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.42/0.54    inference(subsumption_resolution,[],[f72,f63])).
% 1.42/0.54  fof(f63,plain,(
% 1.42/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_pre_topc(k1_pre_topc(X0,X1))) )),
% 1.42/0.54    inference(cnf_transformation,[],[f23])).
% 1.42/0.54  fof(f72,plain,(
% 1.42/0.54    ( ! [X0,X1] : (k2_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.42/0.54    inference(equality_resolution,[],[f61])).
% 1.42/0.54  fof(f61,plain,(
% 1.42/0.54    ( ! [X2,X0,X1] : (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f34])).
% 1.42/0.54  fof(f34,plain,(
% 1.42/0.54    ! [X0] : (! [X1] : (! [X2] : (((k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1) & (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.42/0.54    inference(nnf_transformation,[],[f21])).
% 1.42/0.54  fof(f21,plain,(
% 1.42/0.54    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.42/0.54    inference(flattening,[],[f20])).
% 1.42/0.54  fof(f20,plain,(
% 1.42/0.54    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.42/0.54    inference(ennf_transformation,[],[f3])).
% 1.42/0.54  fof(f3,axiom,(
% 1.42/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_pre_topc)).
% 1.42/0.54  fof(f188,plain,(
% 1.42/0.54    spl3_17 | ~spl3_1 | ~spl3_15),
% 1.42/0.54    inference(avatar_split_clause,[],[f179,f163,f78,f185])).
% 1.42/0.54  fof(f179,plain,(
% 1.42/0.54    l1_pre_topc(k1_pre_topc(sK0,sK1)) | (~spl3_1 | ~spl3_15)),
% 1.42/0.54    inference(subsumption_resolution,[],[f172,f80])).
% 1.42/0.54  fof(f172,plain,(
% 1.42/0.54    l1_pre_topc(k1_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl3_15),
% 1.42/0.54    inference(resolution,[],[f165,f54])).
% 1.42/0.54  fof(f54,plain,(
% 1.42/0.54    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.42/0.54    inference(cnf_transformation,[],[f15])).
% 1.42/0.54  fof(f15,plain,(
% 1.42/0.54    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.42/0.54    inference(ennf_transformation,[],[f5])).
% 1.42/0.54  fof(f5,axiom,(
% 1.42/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.42/0.54  fof(f183,plain,(
% 1.42/0.54    spl3_16 | ~spl3_1),
% 1.42/0.54    inference(avatar_split_clause,[],[f135,f78,f181])).
% 1.42/0.54  fof(f135,plain,(
% 1.42/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(k1_pre_topc(sK0,X0)) = X0) ) | ~spl3_1),
% 1.42/0.54    inference(resolution,[],[f60,f80])).
% 1.42/0.54  fof(f60,plain,(
% 1.42/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(k1_pre_topc(X0,X1)) = X1) )),
% 1.42/0.54    inference(cnf_transformation,[],[f19])).
% 1.42/0.54  fof(f19,plain,(
% 1.42/0.54    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.42/0.54    inference(ennf_transformation,[],[f6])).
% 1.42/0.54  fof(f6,axiom,(
% 1.42/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).
% 1.42/0.54  fof(f166,plain,(
% 1.42/0.54    spl3_15 | ~spl3_2 | ~spl3_14),
% 1.42/0.54    inference(avatar_split_clause,[],[f159,f156,f83,f163])).
% 1.42/0.54  fof(f156,plain,(
% 1.42/0.54    spl3_14 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_pre_topc(k1_pre_topc(sK0,X0),sK0))),
% 1.42/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.42/0.54  fof(f159,plain,(
% 1.42/0.54    m1_pre_topc(k1_pre_topc(sK0,sK1),sK0) | (~spl3_2 | ~spl3_14)),
% 1.42/0.54    inference(resolution,[],[f157,f85])).
% 1.42/0.54  fof(f157,plain,(
% 1.42/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_pre_topc(k1_pre_topc(sK0,X0),sK0)) ) | ~spl3_14),
% 1.42/0.54    inference(avatar_component_clause,[],[f156])).
% 1.42/0.54  fof(f158,plain,(
% 1.42/0.54    spl3_14 | ~spl3_1),
% 1.42/0.54    inference(avatar_split_clause,[],[f132,f78,f156])).
% 1.42/0.54  fof(f132,plain,(
% 1.42/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_pre_topc(k1_pre_topc(sK0,X0),sK0)) ) | ~spl3_1),
% 1.42/0.54    inference(resolution,[],[f64,f80])).
% 1.42/0.54  fof(f106,plain,(
% 1.42/0.54    ~spl3_6 | ~spl3_5),
% 1.42/0.54    inference(avatar_split_clause,[],[f105,f97,f101])).
% 1.42/0.54  fof(f105,plain,(
% 1.42/0.54    ~v1_compts_1(k1_pre_topc(sK0,sK1)) | ~spl3_5),
% 1.42/0.54    inference(subsumption_resolution,[],[f76,f99])).
% 1.42/0.54  fof(f76,plain,(
% 1.42/0.54    ~v1_compts_1(k1_pre_topc(sK0,sK1)) | ~v2_compts_1(sK1,sK0)),
% 1.42/0.54    inference(duplicate_literal_removal,[],[f51])).
% 1.42/0.54  fof(f51,plain,(
% 1.42/0.54    ~v1_compts_1(k1_pre_topc(sK0,sK1)) | ~v2_compts_1(sK1,sK0) | ~v1_compts_1(k1_pre_topc(sK0,sK1)) | ~v2_compts_1(sK1,sK0)),
% 1.42/0.54    inference(cnf_transformation,[],[f28])).
% 1.42/0.54  fof(f28,plain,(
% 1.42/0.54    ((((~v1_compts_1(k1_pre_topc(sK0,sK1)) | ~v2_compts_1(sK1,sK0)) & (v1_compts_1(k1_pre_topc(sK0,sK1)) | v2_compts_1(sK1,sK0)) & k1_xboole_0 != sK1 & v2_pre_topc(sK0)) | ((~v1_compts_1(k1_pre_topc(sK0,sK1)) | ~v2_compts_1(sK1,sK0)) & (v1_compts_1(k1_pre_topc(sK0,sK1)) | v2_compts_1(sK1,sK0)) & k1_xboole_0 = sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.42/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f25,f27,f26])).
% 1.42/0.54  fof(f26,plain,(
% 1.42/0.54    ? [X0] : (? [X1] : ((((~v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) & (v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0)) & k1_xboole_0 != X1 & v2_pre_topc(X0)) | ((~v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) & (v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0)) & k1_xboole_0 = X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((((~v1_compts_1(k1_pre_topc(sK0,X1)) | ~v2_compts_1(X1,sK0)) & (v1_compts_1(k1_pre_topc(sK0,X1)) | v2_compts_1(X1,sK0)) & k1_xboole_0 != X1 & v2_pre_topc(sK0)) | ((~v1_compts_1(k1_pre_topc(sK0,X1)) | ~v2_compts_1(X1,sK0)) & (v1_compts_1(k1_pre_topc(sK0,X1)) | v2_compts_1(X1,sK0)) & k1_xboole_0 = X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.42/0.54    introduced(choice_axiom,[])).
% 1.42/0.54  fof(f27,plain,(
% 1.42/0.54    ? [X1] : ((((~v1_compts_1(k1_pre_topc(sK0,X1)) | ~v2_compts_1(X1,sK0)) & (v1_compts_1(k1_pre_topc(sK0,X1)) | v2_compts_1(X1,sK0)) & k1_xboole_0 != X1 & v2_pre_topc(sK0)) | ((~v1_compts_1(k1_pre_topc(sK0,X1)) | ~v2_compts_1(X1,sK0)) & (v1_compts_1(k1_pre_topc(sK0,X1)) | v2_compts_1(X1,sK0)) & k1_xboole_0 = X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((((~v1_compts_1(k1_pre_topc(sK0,sK1)) | ~v2_compts_1(sK1,sK0)) & (v1_compts_1(k1_pre_topc(sK0,sK1)) | v2_compts_1(sK1,sK0)) & k1_xboole_0 != sK1 & v2_pre_topc(sK0)) | ((~v1_compts_1(k1_pre_topc(sK0,sK1)) | ~v2_compts_1(sK1,sK0)) & (v1_compts_1(k1_pre_topc(sK0,sK1)) | v2_compts_1(sK1,sK0)) & k1_xboole_0 = sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.42/0.54    introduced(choice_axiom,[])).
% 1.42/0.54  fof(f25,plain,(
% 1.42/0.54    ? [X0] : (? [X1] : ((((~v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) & (v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0)) & k1_xboole_0 != X1 & v2_pre_topc(X0)) | ((~v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) & (v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0)) & k1_xboole_0 = X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.42/0.54    inference(flattening,[],[f24])).
% 1.42/0.54  fof(f24,plain,(
% 1.42/0.54    ? [X0] : (? [X1] : (((((~v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) & (v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0))) & k1_xboole_0 != X1 & v2_pre_topc(X0)) | (((~v1_compts_1(k1_pre_topc(X0,X1)) | ~v2_compts_1(X1,X0)) & (v1_compts_1(k1_pre_topc(X0,X1)) | v2_compts_1(X1,X0))) & k1_xboole_0 = X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.42/0.54    inference(nnf_transformation,[],[f13])).
% 1.42/0.54  fof(f13,plain,(
% 1.42/0.54    ? [X0] : (? [X1] : ((((v2_compts_1(X1,X0) <~> v1_compts_1(k1_pre_topc(X0,X1))) & k1_xboole_0 != X1 & v2_pre_topc(X0)) | ((v2_compts_1(X1,X0) <~> v1_compts_1(k1_pre_topc(X0,X1))) & k1_xboole_0 = X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.42/0.54    inference(flattening,[],[f12])).
% 1.42/0.54  fof(f12,plain,(
% 1.42/0.54    ? [X0] : (? [X1] : (((((v2_compts_1(X1,X0) <~> v1_compts_1(k1_pre_topc(X0,X1))) & k1_xboole_0 != X1) & v2_pre_topc(X0)) | ((v2_compts_1(X1,X0) <~> v1_compts_1(k1_pre_topc(X0,X1))) & k1_xboole_0 = X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.42/0.54    inference(ennf_transformation,[],[f11])).
% 1.42/0.54  fof(f11,negated_conjecture,(
% 1.42/0.54    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_pre_topc(X0) => ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1)) & (k1_xboole_0 = X1 => (v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1)))))))),
% 1.42/0.54    inference(negated_conjecture,[],[f10])).
% 1.42/0.54  fof(f10,conjecture,(
% 1.42/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_pre_topc(X0) => ((v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1))) | k1_xboole_0 = X1)) & (k1_xboole_0 = X1 => (v2_compts_1(X1,X0) <=> v1_compts_1(k1_pre_topc(X0,X1)))))))),
% 1.42/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_compts_1)).
% 1.42/0.54  fof(f104,plain,(
% 1.42/0.54    spl3_5 | spl3_6),
% 1.42/0.54    inference(avatar_split_clause,[],[f75,f101,f97])).
% 1.42/0.54  fof(f75,plain,(
% 1.42/0.54    v1_compts_1(k1_pre_topc(sK0,sK1)) | v2_compts_1(sK1,sK0)),
% 1.42/0.54    inference(duplicate_literal_removal,[],[f47])).
% 1.42/0.54  fof(f47,plain,(
% 1.42/0.54    v1_compts_1(k1_pre_topc(sK0,sK1)) | v2_compts_1(sK1,sK0) | v1_compts_1(k1_pre_topc(sK0,sK1)) | v2_compts_1(sK1,sK0)),
% 1.42/0.54    inference(cnf_transformation,[],[f28])).
% 1.42/0.54  fof(f86,plain,(
% 1.42/0.54    spl3_2),
% 1.42/0.54    inference(avatar_split_clause,[],[f39,f83])).
% 1.42/0.54  fof(f39,plain,(
% 1.42/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.42/0.54    inference(cnf_transformation,[],[f28])).
% 1.42/0.54  fof(f81,plain,(
% 1.42/0.54    spl3_1),
% 1.42/0.54    inference(avatar_split_clause,[],[f38,f78])).
% 1.42/0.54  fof(f38,plain,(
% 1.42/0.54    l1_pre_topc(sK0)),
% 1.42/0.54    inference(cnf_transformation,[],[f28])).
% 1.42/0.54  % SZS output end Proof for theBenchmark
% 1.42/0.54  % (29068)------------------------------
% 1.42/0.54  % (29068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.54  % (29068)Termination reason: Refutation
% 1.42/0.54  
% 1.42/0.54  % (29068)Memory used [KB]: 6524
% 1.42/0.54  % (29068)Time elapsed: 0.099 s
% 1.42/0.54  % (29068)------------------------------
% 1.42/0.54  % (29068)------------------------------
% 1.42/0.54  % (29065)Success in time 0.18 s
%------------------------------------------------------------------------------
