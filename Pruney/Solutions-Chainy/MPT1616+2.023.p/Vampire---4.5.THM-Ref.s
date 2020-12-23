%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 258 expanded)
%              Number of leaves         :   35 (  97 expanded)
%              Depth                    :   14
%              Number of atoms          :  540 ( 973 expanded)
%              Number of equality atoms :   35 (  72 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f937,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f97,f102,f111,f120,f303,f378,f392,f404,f417,f620,f658,f709,f718,f761,f799,f876,f910,f933])).

fof(f933,plain,
    ( spl6_23
    | ~ spl6_49 ),
    inference(avatar_contradiction_clause,[],[f932])).

fof(f932,plain,
    ( $false
    | spl6_23
    | ~ spl6_49 ),
    inference(subsumption_resolution,[],[f927,f390])).

fof(f390,plain,
    ( ~ sP5(u1_pre_topc(sK0))
    | spl6_23 ),
    inference(avatar_component_clause,[],[f389])).

fof(f389,plain,
    ( spl6_23
  <=> sP5(u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f927,plain,
    ( sP5(u1_pre_topc(sK0))
    | ~ spl6_49 ),
    inference(resolution,[],[f909,f79])).

fof(f79,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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

fof(f909,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_pre_topc(sK0))
        | sP5(X0) )
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f908])).

fof(f908,plain,
    ( spl6_49
  <=> ! [X0] :
        ( sP5(X0)
        | ~ r1_tarski(X0,u1_pre_topc(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f910,plain,
    ( spl6_49
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f903,f874,f908])).

fof(f874,plain,
    ( spl6_48
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_pre_topc(sK0)))
        | sP5(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f903,plain,
    ( ! [X0] :
        ( sP5(X0)
        | ~ r1_tarski(X0,u1_pre_topc(sK0)) )
    | ~ spl6_48 ),
    inference(resolution,[],[f875,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f875,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_pre_topc(sK0)))
        | sP5(X3) )
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f874])).

fof(f876,plain,
    ( spl6_48
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f808,f796,f874])).

fof(f796,plain,
    ( spl6_44
  <=> v1_xboole_0(u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f808,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_pre_topc(sK0)))
        | sP5(X3) )
    | ~ spl6_44 ),
    inference(resolution,[],[f798,f81])).

fof(f81,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | sP5(X1) ) ),
    inference(cnf_transformation,[],[f81_D])).

fof(f81_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ v1_xboole_0(X2)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) )
    <=> ~ sP5(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f798,plain,
    ( v1_xboole_0(u1_pre_topc(sK0))
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f796])).

fof(f799,plain,
    ( spl6_44
    | spl6_4
    | ~ spl6_42
    | ~ spl6_43 ),
    inference(avatar_split_clause,[],[f788,f758,f706,f99,f796])).

fof(f99,plain,
    ( spl6_4
  <=> u1_struct_0(sK0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f706,plain,
    ( spl6_42
  <=> r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f758,plain,
    ( spl6_43
  <=> u1_struct_0(sK0) = k3_tarski(u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f788,plain,
    ( v1_xboole_0(u1_pre_topc(sK0))
    | spl6_4
    | ~ spl6_42
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f787,f101])).

fof(f101,plain,
    ( u1_struct_0(sK0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
    | spl6_4 ),
    inference(avatar_component_clause,[],[f99])).

fof(f787,plain,
    ( u1_struct_0(sK0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
    | v1_xboole_0(u1_pre_topc(sK0))
    | ~ spl6_42
    | ~ spl6_43 ),
    inference(subsumption_resolution,[],[f769,f707])).

fof(f707,plain,
    ( r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f706])).

fof(f769,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | u1_struct_0(sK0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
    | v1_xboole_0(u1_pre_topc(sK0))
    | ~ spl6_43 ),
    inference(superposition,[],[f45,f760])).

fof(f760,plain,
    ( u1_struct_0(sK0) = k3_tarski(u1_pre_topc(sK0))
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f758])).

fof(f45,plain,(
    ! [X0] :
      ( ~ r2_hidden(k3_tarski(X0),X0)
      | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

fof(f761,plain,
    ( spl6_43
    | ~ spl6_39
    | ~ spl6_41 ),
    inference(avatar_split_clause,[],[f728,f693,f655,f758])).

fof(f655,plain,
    ( spl6_39
  <=> r1_tarski(k3_tarski(u1_pre_topc(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f693,plain,
    ( spl6_41
  <=> r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f728,plain,
    ( u1_struct_0(sK0) = k3_tarski(u1_pre_topc(sK0))
    | ~ spl6_39
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f724,f657])).

fof(f657,plain,
    ( r1_tarski(k3_tarski(u1_pre_topc(sK0)),u1_struct_0(sK0))
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f655])).

fof(f724,plain,
    ( ~ r1_tarski(k3_tarski(u1_pre_topc(sK0)),u1_struct_0(sK0))
    | u1_struct_0(sK0) = k3_tarski(u1_pre_topc(sK0))
    | ~ spl6_41 ),
    inference(resolution,[],[f694,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f694,plain,
    ( r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0)))
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f693])).

fof(f718,plain,
    ( ~ spl6_2
    | ~ spl6_3
    | spl6_42 ),
    inference(avatar_contradiction_clause,[],[f717])).

fof(f717,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_3
    | spl6_42 ),
    inference(subsumption_resolution,[],[f716,f96])).

fof(f96,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl6_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f716,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl6_2
    | spl6_42 ),
    inference(subsumption_resolution,[],[f714,f91])).

fof(f91,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl6_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f714,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | spl6_42 ),
    inference(resolution,[],[f708,f47])).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),sK2(X0)),u1_pre_topc(X0))
            & r2_hidden(sK2(X0),u1_pre_topc(X0))
            & r2_hidden(sK1(X0),u1_pre_topc(X0))
            & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
            & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) )
          | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
            & r1_tarski(sK3(X0),u1_pre_topc(X0))
            & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0))
                    | ~ r2_hidden(X5,u1_pre_topc(X0))
                    | ~ r2_hidden(X4,u1_pre_topc(X0))
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            & ! [X6] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0))
                | ~ r1_tarski(X6,u1_pre_topc(X0))
                | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f30,f33,f32,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              & r2_hidden(X2,u1_pre_topc(X0))
              & r2_hidden(X1,u1_pre_topc(X0))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),X2),u1_pre_topc(X0))
            & r2_hidden(X2,u1_pre_topc(X0))
            & r2_hidden(sK1(X0),u1_pre_topc(X0))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),X2),u1_pre_topc(X0))
          & r2_hidden(X2,u1_pre_topc(X0))
          & r2_hidden(sK1(X0),u1_pre_topc(X0))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),sK2(X0)),u1_pre_topc(X0))
        & r2_hidden(sK2(X0),u1_pre_topc(X0))
        & r2_hidden(sK1(X0),u1_pre_topc(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
          & r1_tarski(X3,u1_pre_topc(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0))
        & r1_tarski(sK3(X0),u1_pre_topc(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  & r2_hidden(X2,u1_pre_topc(X0))
                  & r2_hidden(X1,u1_pre_topc(X0))
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0))
                    | ~ r2_hidden(X5,u1_pre_topc(X0))
                    | ~ r2_hidden(X4,u1_pre_topc(X0))
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            & ! [X6] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0))
                | ~ r1_tarski(X6,u1_pre_topc(X0))
                | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  & r2_hidden(X2,u1_pre_topc(X0))
                  & r2_hidden(X1,u1_pre_topc(X0))
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( ! [X1] :
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
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  & r2_hidden(X2,u1_pre_topc(X0))
                  & r2_hidden(X1,u1_pre_topc(X0))
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( ! [X1] :
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
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(rectify,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

fof(f708,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | spl6_42 ),
    inference(avatar_component_clause,[],[f706])).

fof(f709,plain,
    ( ~ spl6_42
    | spl6_41 ),
    inference(avatar_split_clause,[],[f697,f693,f706])).

fof(f697,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | spl6_41 ),
    inference(resolution,[],[f695,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f695,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0)))
    | spl6_41 ),
    inference(avatar_component_clause,[],[f693])).

fof(f658,plain,
    ( spl6_39
    | ~ spl6_6
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f630,f618,f117,f655])).

fof(f117,plain,
    ( spl6_6
  <=> r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f618,plain,
    ( spl6_37
  <=> ! [X2] :
        ( r1_tarski(k3_tarski(X2),u1_struct_0(sK0))
        | ~ r1_tarski(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f630,plain,
    ( r1_tarski(k3_tarski(u1_pre_topc(sK0)),u1_struct_0(sK0))
    | ~ spl6_6
    | ~ spl6_37 ),
    inference(resolution,[],[f619,f119])).

fof(f119,plain,
    ( r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f117])).

fof(f619,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k3_tarski(X2),u1_struct_0(sK0)) )
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f618])).

fof(f620,plain,
    ( spl6_37
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f345,f300,f618])).

fof(f300,plain,
    ( spl6_16
  <=> u1_struct_0(sK0) = k3_tarski(k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f345,plain,
    ( ! [X2] :
        ( r1_tarski(k3_tarski(X2),u1_struct_0(sK0))
        | ~ r1_tarski(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_16 ),
    inference(superposition,[],[f70,f302])).

fof(f302,plain,
    ( u1_struct_0(sK0) = k3_tarski(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f300])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(f417,plain,
    ( ~ spl6_2
    | ~ spl6_3
    | ~ spl6_25 ),
    inference(avatar_contradiction_clause,[],[f416])).

fof(f416,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f415,f96])).

fof(f415,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl6_2
    | ~ spl6_25 ),
    inference(subsumption_resolution,[],[f408,f91])).

fof(f408,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl6_25 ),
    inference(resolution,[],[f403,f47])).

fof(f403,plain,
    ( ! [X0] : ~ r2_hidden(X0,u1_pre_topc(sK0))
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f402])).

fof(f402,plain,
    ( spl6_25
  <=> ! [X0] : ~ r2_hidden(X0,u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f404,plain,
    ( spl6_25
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f394,f389,f402])).

fof(f394,plain,
    ( ! [X0] : ~ r2_hidden(X0,u1_pre_topc(sK0))
    | ~ spl6_23 ),
    inference(resolution,[],[f391,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ sP5(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(general_splitting,[],[f78,f81_D])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f391,plain,
    ( sP5(u1_pre_topc(sK0))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f389])).

fof(f392,plain,
    ( spl6_23
    | ~ spl6_5
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f386,f376,f108,f389])).

fof(f108,plain,
    ( spl6_5
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f376,plain,
    ( spl6_22
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | sP5(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f386,plain,
    ( sP5(u1_pre_topc(sK0))
    | ~ spl6_5
    | ~ spl6_22 ),
    inference(resolution,[],[f377,f110])).

fof(f110,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f108])).

fof(f377,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | sP5(X2) )
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f376])).

fof(f378,plain,
    ( spl6_22
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f362,f279,f376])).

fof(f279,plain,
    ( spl6_13
  <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f362,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | sP5(X2) )
    | ~ spl6_13 ),
    inference(resolution,[],[f281,f81])).

fof(f281,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f279])).

fof(f303,plain,
    ( spl6_16
    | spl6_13 ),
    inference(avatar_split_clause,[],[f296,f279,f300])).

fof(f296,plain,
    ( u1_struct_0(sK0) = k3_tarski(k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_13 ),
    inference(resolution,[],[f280,f205])).

fof(f205,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_zfmisc_1(X0))
      | k3_tarski(k1_zfmisc_1(X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f204,f79])).

fof(f204,plain,(
    ! [X0] :
      ( k3_tarski(k1_zfmisc_1(X0)) = X0
      | v1_xboole_0(k1_zfmisc_1(X0))
      | ~ r1_tarski(X0,X0) ) ),
    inference(duplicate_literal_removal,[],[f203])).

fof(f203,plain,(
    ! [X0] :
      ( k3_tarski(k1_zfmisc_1(X0)) = X0
      | v1_xboole_0(k1_zfmisc_1(X0))
      | v1_xboole_0(k1_zfmisc_1(X0))
      | ~ r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f199,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_zfmisc_1(X1))
      | v1_xboole_0(k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f65,f77])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f199,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_zfmisc_1(X1))
      | k3_tarski(k1_zfmisc_1(X1)) = X1
      | v1_xboole_0(k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f197,f122])).

fof(f122,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k3_tarski(X1),X2)
      | k3_tarski(X1) = X2
      | ~ r2_hidden(X2,X1) ) ),
    inference(resolution,[],[f75,f69])).

fof(f197,plain,(
    ! [X0] :
      ( r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0)
      | v1_xboole_0(k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f194])).

fof(f194,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_zfmisc_1(X0))
      | r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0)
      | r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0) ) ),
    inference(resolution,[],[f130,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK4(X0,X1),X1)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ( ~ r1_tarski(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_tarski(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(f130,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK4(k1_zfmisc_1(X0),X1),X0)
      | v1_xboole_0(k1_zfmisc_1(X0))
      | r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X1) ) ),
    inference(resolution,[],[f112,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f112,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),X0)
      | r1_tarski(k3_tarski(X0),X1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f71,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f280,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_13 ),
    inference(avatar_component_clause,[],[f279])).

fof(f120,plain,
    ( spl6_6
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f113,f108,f117])).

fof(f113,plain,
    ( r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_5 ),
    inference(resolution,[],[f110,f76])).

fof(f111,plain,
    ( spl6_5
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f105,f94,f108])).

fof(f105,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_3 ),
    inference(resolution,[],[f46,f96])).

fof(f46,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f102,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f44,f99])).

fof(f44,plain,(
    u1_struct_0(sK0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( u1_struct_0(sK0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( u1_struct_0(sK0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow_1)).

fof(f97,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f43,f94])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f92,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f42,f89])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:01:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (27048)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (27059)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (27052)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (27064)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (27065)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (27056)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (27067)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (27047)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (27063)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (27055)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.53  % (27051)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.53  % (27046)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (27051)Refutation not found, incomplete strategy% (27051)------------------------------
% 0.21/0.53  % (27051)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (27045)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.53  % (27050)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.53  % (27049)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.53  % (27051)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (27051)Memory used [KB]: 10618
% 0.21/0.53  % (27051)Time elapsed: 0.069 s
% 0.21/0.53  % (27051)------------------------------
% 0.21/0.53  % (27051)------------------------------
% 0.21/0.54  % (27060)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.54  % (27061)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.54  % (27070)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.54  % (27068)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.54  % (27058)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (27069)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.54  % (27057)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.54  % (27054)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.55  % (27066)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.55  % (27053)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.55  % (27062)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.55  % (27046)Refutation not found, incomplete strategy% (27046)------------------------------
% 0.21/0.55  % (27046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (27046)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (27046)Memory used [KB]: 10618
% 0.21/0.55  % (27046)Time elapsed: 0.132 s
% 0.21/0.55  % (27046)------------------------------
% 0.21/0.55  % (27046)------------------------------
% 0.21/0.56  % (27047)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f937,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f92,f97,f102,f111,f120,f303,f378,f392,f404,f417,f620,f658,f709,f718,f761,f799,f876,f910,f933])).
% 0.21/0.57  fof(f933,plain,(
% 0.21/0.57    spl6_23 | ~spl6_49),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f932])).
% 0.21/0.57  fof(f932,plain,(
% 0.21/0.57    $false | (spl6_23 | ~spl6_49)),
% 0.21/0.57    inference(subsumption_resolution,[],[f927,f390])).
% 0.21/0.57  fof(f390,plain,(
% 0.21/0.57    ~sP5(u1_pre_topc(sK0)) | spl6_23),
% 0.21/0.57    inference(avatar_component_clause,[],[f389])).
% 0.21/0.57  fof(f389,plain,(
% 0.21/0.57    spl6_23 <=> sP5(u1_pre_topc(sK0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.21/0.57  fof(f927,plain,(
% 0.21/0.57    sP5(u1_pre_topc(sK0)) | ~spl6_49),
% 0.21/0.57    inference(resolution,[],[f909,f79])).
% 0.21/0.57  fof(f79,plain,(
% 0.21/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.57    inference(equality_resolution,[],[f74])).
% 0.21/0.57  fof(f74,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f39])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.57    inference(flattening,[],[f38])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.57    inference(nnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.57  fof(f909,plain,(
% 0.21/0.57    ( ! [X0] : (~r1_tarski(X0,u1_pre_topc(sK0)) | sP5(X0)) ) | ~spl6_49),
% 0.21/0.57    inference(avatar_component_clause,[],[f908])).
% 0.21/0.57  fof(f908,plain,(
% 0.21/0.57    spl6_49 <=> ! [X0] : (sP5(X0) | ~r1_tarski(X0,u1_pre_topc(sK0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).
% 0.21/0.57  fof(f910,plain,(
% 0.21/0.57    spl6_49 | ~spl6_48),
% 0.21/0.57    inference(avatar_split_clause,[],[f903,f874,f908])).
% 0.21/0.57  fof(f874,plain,(
% 0.21/0.57    spl6_48 <=> ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_pre_topc(sK0))) | sP5(X3))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).
% 0.21/0.57  fof(f903,plain,(
% 0.21/0.57    ( ! [X0] : (sP5(X0) | ~r1_tarski(X0,u1_pre_topc(sK0))) ) | ~spl6_48),
% 0.21/0.57    inference(resolution,[],[f875,f77])).
% 0.21/0.57  fof(f77,plain,(
% 0.21/0.57    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f40])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.57    inference(nnf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.57  fof(f875,plain,(
% 0.21/0.57    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_pre_topc(sK0))) | sP5(X3)) ) | ~spl6_48),
% 0.21/0.57    inference(avatar_component_clause,[],[f874])).
% 0.21/0.57  fof(f876,plain,(
% 0.21/0.57    spl6_48 | ~spl6_44),
% 0.21/0.57    inference(avatar_split_clause,[],[f808,f796,f874])).
% 0.21/0.57  fof(f796,plain,(
% 0.21/0.57    spl6_44 <=> v1_xboole_0(u1_pre_topc(sK0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 0.21/0.57  fof(f808,plain,(
% 0.21/0.57    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_pre_topc(sK0))) | sP5(X3)) ) | ~spl6_44),
% 0.21/0.57    inference(resolution,[],[f798,f81])).
% 0.21/0.57  fof(f81,plain,(
% 0.21/0.57    ( ! [X2,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | sP5(X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f81_D])).
% 0.21/0.57  fof(f81_D,plain,(
% 0.21/0.57    ( ! [X1] : (( ! [X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2))) ) <=> ~sP5(X1)) )),
% 0.21/0.57    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).
% 0.21/0.57  fof(f798,plain,(
% 0.21/0.57    v1_xboole_0(u1_pre_topc(sK0)) | ~spl6_44),
% 0.21/0.57    inference(avatar_component_clause,[],[f796])).
% 0.21/0.57  fof(f799,plain,(
% 0.21/0.57    spl6_44 | spl6_4 | ~spl6_42 | ~spl6_43),
% 0.21/0.57    inference(avatar_split_clause,[],[f788,f758,f706,f99,f796])).
% 0.21/0.57  fof(f99,plain,(
% 0.21/0.57    spl6_4 <=> u1_struct_0(sK0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.57  fof(f706,plain,(
% 0.21/0.57    spl6_42 <=> r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 0.21/0.57  fof(f758,plain,(
% 0.21/0.57    spl6_43 <=> u1_struct_0(sK0) = k3_tarski(u1_pre_topc(sK0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 0.21/0.57  fof(f788,plain,(
% 0.21/0.57    v1_xboole_0(u1_pre_topc(sK0)) | (spl6_4 | ~spl6_42 | ~spl6_43)),
% 0.21/0.57    inference(subsumption_resolution,[],[f787,f101])).
% 0.21/0.57  fof(f101,plain,(
% 0.21/0.57    u1_struct_0(sK0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) | spl6_4),
% 0.21/0.57    inference(avatar_component_clause,[],[f99])).
% 0.21/0.57  fof(f787,plain,(
% 0.21/0.57    u1_struct_0(sK0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) | v1_xboole_0(u1_pre_topc(sK0)) | (~spl6_42 | ~spl6_43)),
% 0.21/0.57    inference(subsumption_resolution,[],[f769,f707])).
% 0.21/0.57  fof(f707,plain,(
% 0.21/0.57    r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~spl6_42),
% 0.21/0.57    inference(avatar_component_clause,[],[f706])).
% 0.21/0.57  fof(f769,plain,(
% 0.21/0.57    ~r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) | u1_struct_0(sK0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) | v1_xboole_0(u1_pre_topc(sK0)) | ~spl6_43),
% 0.21/0.57    inference(superposition,[],[f45,f760])).
% 0.21/0.57  fof(f760,plain,(
% 0.21/0.57    u1_struct_0(sK0) = k3_tarski(u1_pre_topc(sK0)) | ~spl6_43),
% 0.21/0.57    inference(avatar_component_clause,[],[f758])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(k3_tarski(X0),X0) | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0))),
% 0.21/0.57    inference(flattening,[],[f16])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ! [X0] : ((k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) | v1_xboole_0(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,axiom,(
% 0.21/0.57    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).
% 0.21/0.57  fof(f761,plain,(
% 0.21/0.57    spl6_43 | ~spl6_39 | ~spl6_41),
% 0.21/0.57    inference(avatar_split_clause,[],[f728,f693,f655,f758])).
% 0.21/0.57  fof(f655,plain,(
% 0.21/0.57    spl6_39 <=> r1_tarski(k3_tarski(u1_pre_topc(sK0)),u1_struct_0(sK0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 0.21/0.57  fof(f693,plain,(
% 0.21/0.57    spl6_41 <=> r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 0.21/0.57  fof(f728,plain,(
% 0.21/0.57    u1_struct_0(sK0) = k3_tarski(u1_pre_topc(sK0)) | (~spl6_39 | ~spl6_41)),
% 0.21/0.57    inference(subsumption_resolution,[],[f724,f657])).
% 0.21/0.57  fof(f657,plain,(
% 0.21/0.57    r1_tarski(k3_tarski(u1_pre_topc(sK0)),u1_struct_0(sK0)) | ~spl6_39),
% 0.21/0.57    inference(avatar_component_clause,[],[f655])).
% 0.21/0.57  fof(f724,plain,(
% 0.21/0.57    ~r1_tarski(k3_tarski(u1_pre_topc(sK0)),u1_struct_0(sK0)) | u1_struct_0(sK0) = k3_tarski(u1_pre_topc(sK0)) | ~spl6_41),
% 0.21/0.57    inference(resolution,[],[f694,f75])).
% 1.65/0.57  fof(f75,plain,(
% 1.65/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.65/0.57    inference(cnf_transformation,[],[f39])).
% 1.65/0.57  fof(f694,plain,(
% 1.65/0.57    r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0))) | ~spl6_41),
% 1.65/0.57    inference(avatar_component_clause,[],[f693])).
% 1.65/0.57  fof(f718,plain,(
% 1.65/0.57    ~spl6_2 | ~spl6_3 | spl6_42),
% 1.65/0.57    inference(avatar_contradiction_clause,[],[f717])).
% 1.65/0.57  fof(f717,plain,(
% 1.65/0.57    $false | (~spl6_2 | ~spl6_3 | spl6_42)),
% 1.65/0.57    inference(subsumption_resolution,[],[f716,f96])).
% 1.65/0.57  fof(f96,plain,(
% 1.65/0.57    l1_pre_topc(sK0) | ~spl6_3),
% 1.65/0.57    inference(avatar_component_clause,[],[f94])).
% 1.65/0.57  fof(f94,plain,(
% 1.65/0.57    spl6_3 <=> l1_pre_topc(sK0)),
% 1.65/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.65/0.57  fof(f716,plain,(
% 1.65/0.57    ~l1_pre_topc(sK0) | (~spl6_2 | spl6_42)),
% 1.65/0.57    inference(subsumption_resolution,[],[f714,f91])).
% 1.65/0.57  fof(f91,plain,(
% 1.65/0.57    v2_pre_topc(sK0) | ~spl6_2),
% 1.65/0.57    inference(avatar_component_clause,[],[f89])).
% 1.65/0.57  fof(f89,plain,(
% 1.65/0.57    spl6_2 <=> v2_pre_topc(sK0)),
% 1.65/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.65/0.57  fof(f714,plain,(
% 1.65/0.57    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | spl6_42),
% 1.65/0.57    inference(resolution,[],[f708,f47])).
% 1.65/0.57  fof(f47,plain,(
% 1.65/0.57    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 1.65/0.57    inference(cnf_transformation,[],[f34])).
% 1.65/0.57  fof(f34,plain,(
% 1.65/0.57    ! [X0] : (((v2_pre_topc(X0) | ((~r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),sK2(X0)),u1_pre_topc(X0)) & r2_hidden(sK2(X0),u1_pre_topc(X0)) & r2_hidden(sK1(X0),u1_pre_topc(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))) | (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((! [X4] : (! [X5] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0)) | ~r2_hidden(X5,u1_pre_topc(X0)) | ~r2_hidden(X4,u1_pre_topc(X0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X6] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0)) | ~r1_tarski(X6,u1_pre_topc(X0)) | ~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 1.65/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f30,f33,f32,f31])).
% 1.65/0.57  fof(f31,plain,(
% 1.65/0.57    ! [X0] : (? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(sK1(X0),u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.65/0.57    introduced(choice_axiom,[])).
% 1.65/0.57  fof(f32,plain,(
% 1.65/0.57    ! [X0] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(sK1(X0),u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(k9_subset_1(u1_struct_0(X0),sK1(X0),sK2(X0)),u1_pre_topc(X0)) & r2_hidden(sK2(X0),u1_pre_topc(X0)) & r2_hidden(sK1(X0),u1_pre_topc(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.65/0.57    introduced(choice_axiom,[])).
% 1.65/0.57  fof(f33,plain,(
% 1.65/0.57    ! [X0] : (? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (~r2_hidden(k5_setfam_1(u1_struct_0(X0),sK3(X0)),u1_pre_topc(X0)) & r1_tarski(sK3(X0),u1_pre_topc(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.65/0.57    introduced(choice_axiom,[])).
% 1.65/0.57  fof(f30,plain,(
% 1.65/0.57    ! [X0] : (((v2_pre_topc(X0) | ? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((! [X4] : (! [X5] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0)) | ~r2_hidden(X5,u1_pre_topc(X0)) | ~r2_hidden(X4,u1_pre_topc(X0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X6] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0)) | ~r1_tarski(X6,u1_pre_topc(X0)) | ~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 1.65/0.57    inference(rectify,[],[f29])).
% 1.65/0.57  fof(f29,plain,(
% 1.65/0.57    ! [X0] : (((v2_pre_topc(X0) | ? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) & ((! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 1.65/0.57    inference(flattening,[],[f28])).
% 1.65/0.57  fof(f28,plain,(
% 1.65/0.57    ! [X0] : (((v2_pre_topc(X0) | (? [X1] : (? [X2] : (~r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) & r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ? [X3] : (~r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) & r1_tarski(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) & ((! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0))) | ~l1_pre_topc(X0))),
% 1.65/0.57    inference(nnf_transformation,[],[f20])).
% 1.65/0.57  fof(f20,plain,(
% 1.65/0.57    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.65/0.57    inference(flattening,[],[f19])).
% 1.65/0.57  fof(f19,plain,(
% 1.65/0.57    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 1.65/0.57    inference(ennf_transformation,[],[f13])).
% 1.65/0.57  fof(f13,plain,(
% 1.65/0.57    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 1.65/0.57    inference(rectify,[],[f8])).
% 1.65/0.57  fof(f8,axiom,(
% 1.65/0.57    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 1.65/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).
% 1.65/0.57  fof(f708,plain,(
% 1.65/0.57    ~r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) | spl6_42),
% 1.65/0.57    inference(avatar_component_clause,[],[f706])).
% 1.65/0.57  fof(f709,plain,(
% 1.65/0.57    ~spl6_42 | spl6_41),
% 1.65/0.57    inference(avatar_split_clause,[],[f697,f693,f706])).
% 1.65/0.57  fof(f697,plain,(
% 1.65/0.57    ~r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) | spl6_41),
% 1.65/0.57    inference(resolution,[],[f695,f69])).
% 1.65/0.57  fof(f69,plain,(
% 1.65/0.57    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 1.65/0.57    inference(cnf_transformation,[],[f22])).
% 1.65/0.57  fof(f22,plain,(
% 1.65/0.57    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 1.65/0.57    inference(ennf_transformation,[],[f2])).
% 1.65/0.57  fof(f2,axiom,(
% 1.65/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 1.65/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 1.65/0.57  fof(f695,plain,(
% 1.65/0.57    ~r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0))) | spl6_41),
% 1.65/0.57    inference(avatar_component_clause,[],[f693])).
% 1.65/0.57  fof(f658,plain,(
% 1.65/0.57    spl6_39 | ~spl6_6 | ~spl6_37),
% 1.65/0.57    inference(avatar_split_clause,[],[f630,f618,f117,f655])).
% 1.65/0.57  fof(f117,plain,(
% 1.65/0.57    spl6_6 <=> r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.65/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.65/0.57  fof(f618,plain,(
% 1.65/0.57    spl6_37 <=> ! [X2] : (r1_tarski(k3_tarski(X2),u1_struct_0(sK0)) | ~r1_tarski(X2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.65/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 1.65/0.57  fof(f630,plain,(
% 1.65/0.57    r1_tarski(k3_tarski(u1_pre_topc(sK0)),u1_struct_0(sK0)) | (~spl6_6 | ~spl6_37)),
% 1.65/0.57    inference(resolution,[],[f619,f119])).
% 1.65/0.57  fof(f119,plain,(
% 1.65/0.57    r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_6),
% 1.65/0.57    inference(avatar_component_clause,[],[f117])).
% 1.65/0.57  fof(f619,plain,(
% 1.65/0.57    ( ! [X2] : (~r1_tarski(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k3_tarski(X2),u1_struct_0(sK0))) ) | ~spl6_37),
% 1.65/0.57    inference(avatar_component_clause,[],[f618])).
% 1.65/0.57  fof(f620,plain,(
% 1.65/0.57    spl6_37 | ~spl6_16),
% 1.65/0.57    inference(avatar_split_clause,[],[f345,f300,f618])).
% 1.65/0.57  fof(f300,plain,(
% 1.65/0.57    spl6_16 <=> u1_struct_0(sK0) = k3_tarski(k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.65/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.65/0.57  fof(f345,plain,(
% 1.65/0.57    ( ! [X2] : (r1_tarski(k3_tarski(X2),u1_struct_0(sK0)) | ~r1_tarski(X2,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl6_16),
% 1.65/0.57    inference(superposition,[],[f70,f302])).
% 1.65/0.57  fof(f302,plain,(
% 1.65/0.57    u1_struct_0(sK0) = k3_tarski(k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_16),
% 1.65/0.57    inference(avatar_component_clause,[],[f300])).
% 1.65/0.57  fof(f70,plain,(
% 1.65/0.57    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1)) )),
% 1.65/0.57    inference(cnf_transformation,[],[f23])).
% 1.65/0.57  fof(f23,plain,(
% 1.65/0.57    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 1.65/0.57    inference(ennf_transformation,[],[f4])).
% 1.65/0.57  fof(f4,axiom,(
% 1.65/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 1.65/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).
% 1.65/0.57  fof(f417,plain,(
% 1.65/0.57    ~spl6_2 | ~spl6_3 | ~spl6_25),
% 1.65/0.57    inference(avatar_contradiction_clause,[],[f416])).
% 1.65/0.57  fof(f416,plain,(
% 1.65/0.57    $false | (~spl6_2 | ~spl6_3 | ~spl6_25)),
% 1.65/0.57    inference(subsumption_resolution,[],[f415,f96])).
% 1.65/0.57  fof(f415,plain,(
% 1.65/0.57    ~l1_pre_topc(sK0) | (~spl6_2 | ~spl6_25)),
% 1.65/0.57    inference(subsumption_resolution,[],[f408,f91])).
% 1.65/0.57  fof(f408,plain,(
% 1.65/0.57    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~spl6_25),
% 1.65/0.57    inference(resolution,[],[f403,f47])).
% 1.65/0.57  fof(f403,plain,(
% 1.65/0.57    ( ! [X0] : (~r2_hidden(X0,u1_pre_topc(sK0))) ) | ~spl6_25),
% 1.65/0.57    inference(avatar_component_clause,[],[f402])).
% 1.65/0.57  fof(f402,plain,(
% 1.65/0.57    spl6_25 <=> ! [X0] : ~r2_hidden(X0,u1_pre_topc(sK0))),
% 1.65/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 1.65/0.57  fof(f404,plain,(
% 1.65/0.57    spl6_25 | ~spl6_23),
% 1.65/0.57    inference(avatar_split_clause,[],[f394,f389,f402])).
% 1.65/0.57  fof(f394,plain,(
% 1.65/0.57    ( ! [X0] : (~r2_hidden(X0,u1_pre_topc(sK0))) ) | ~spl6_23),
% 1.65/0.57    inference(resolution,[],[f391,f82])).
% 1.65/0.57  fof(f82,plain,(
% 1.65/0.57    ( ! [X0,X1] : (~sP5(X1) | ~r2_hidden(X0,X1)) )),
% 1.65/0.57    inference(general_splitting,[],[f78,f81_D])).
% 1.65/0.57  fof(f78,plain,(
% 1.65/0.57    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.65/0.57    inference(cnf_transformation,[],[f25])).
% 1.65/0.57  fof(f25,plain,(
% 1.65/0.57    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.65/0.57    inference(ennf_transformation,[],[f7])).
% 1.65/0.57  fof(f7,axiom,(
% 1.65/0.57    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.65/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.65/0.57  fof(f391,plain,(
% 1.65/0.57    sP5(u1_pre_topc(sK0)) | ~spl6_23),
% 1.65/0.57    inference(avatar_component_clause,[],[f389])).
% 1.65/0.57  fof(f392,plain,(
% 1.65/0.57    spl6_23 | ~spl6_5 | ~spl6_22),
% 1.65/0.57    inference(avatar_split_clause,[],[f386,f376,f108,f389])).
% 1.65/0.57  fof(f108,plain,(
% 1.65/0.57    spl6_5 <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.65/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.65/0.57  fof(f376,plain,(
% 1.65/0.57    spl6_22 <=> ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | sP5(X2))),
% 1.65/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 1.65/0.57  fof(f386,plain,(
% 1.65/0.57    sP5(u1_pre_topc(sK0)) | (~spl6_5 | ~spl6_22)),
% 1.65/0.57    inference(resolution,[],[f377,f110])).
% 1.65/0.57  fof(f110,plain,(
% 1.65/0.57    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl6_5),
% 1.65/0.57    inference(avatar_component_clause,[],[f108])).
% 1.65/0.57  fof(f377,plain,(
% 1.65/0.57    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | sP5(X2)) ) | ~spl6_22),
% 1.65/0.57    inference(avatar_component_clause,[],[f376])).
% 1.65/0.57  fof(f378,plain,(
% 1.65/0.57    spl6_22 | ~spl6_13),
% 1.65/0.57    inference(avatar_split_clause,[],[f362,f279,f376])).
% 1.65/0.57  fof(f279,plain,(
% 1.65/0.57    spl6_13 <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.65/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.65/0.57  fof(f362,plain,(
% 1.65/0.57    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | sP5(X2)) ) | ~spl6_13),
% 1.65/0.57    inference(resolution,[],[f281,f81])).
% 1.65/0.57  fof(f281,plain,(
% 1.65/0.57    v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_13),
% 1.65/0.57    inference(avatar_component_clause,[],[f279])).
% 1.65/0.57  fof(f303,plain,(
% 1.65/0.57    spl6_16 | spl6_13),
% 1.65/0.57    inference(avatar_split_clause,[],[f296,f279,f300])).
% 1.65/0.57  fof(f296,plain,(
% 1.65/0.57    u1_struct_0(sK0) = k3_tarski(k1_zfmisc_1(u1_struct_0(sK0))) | spl6_13),
% 1.65/0.57    inference(resolution,[],[f280,f205])).
% 1.65/0.57  fof(f205,plain,(
% 1.65/0.57    ( ! [X0] : (v1_xboole_0(k1_zfmisc_1(X0)) | k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 1.65/0.57    inference(subsumption_resolution,[],[f204,f79])).
% 1.65/0.57  fof(f204,plain,(
% 1.65/0.57    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0 | v1_xboole_0(k1_zfmisc_1(X0)) | ~r1_tarski(X0,X0)) )),
% 1.65/0.57    inference(duplicate_literal_removal,[],[f203])).
% 1.65/0.57  fof(f203,plain,(
% 1.65/0.57    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0 | v1_xboole_0(k1_zfmisc_1(X0)) | v1_xboole_0(k1_zfmisc_1(X0)) | ~r1_tarski(X0,X0)) )),
% 1.65/0.57    inference(resolution,[],[f199,f104])).
% 1.65/0.57  fof(f104,plain,(
% 1.65/0.57    ( ! [X0,X1] : (r2_hidden(X0,k1_zfmisc_1(X1)) | v1_xboole_0(k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.65/0.57    inference(resolution,[],[f65,f77])).
% 1.65/0.57  fof(f65,plain,(
% 1.65/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.65/0.57    inference(cnf_transformation,[],[f35])).
% 1.65/0.57  fof(f35,plain,(
% 1.65/0.57    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.65/0.57    inference(nnf_transformation,[],[f21])).
% 1.65/0.57  fof(f21,plain,(
% 1.65/0.57    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.65/0.57    inference(ennf_transformation,[],[f5])).
% 1.65/0.57  fof(f5,axiom,(
% 1.65/0.57    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.65/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.65/0.57  fof(f199,plain,(
% 1.65/0.57    ( ! [X1] : (~r2_hidden(X1,k1_zfmisc_1(X1)) | k3_tarski(k1_zfmisc_1(X1)) = X1 | v1_xboole_0(k1_zfmisc_1(X1))) )),
% 1.65/0.57    inference(resolution,[],[f197,f122])).
% 1.65/0.57  fof(f122,plain,(
% 1.65/0.57    ( ! [X2,X1] : (~r1_tarski(k3_tarski(X1),X2) | k3_tarski(X1) = X2 | ~r2_hidden(X2,X1)) )),
% 1.65/0.57    inference(resolution,[],[f75,f69])).
% 1.65/0.57  fof(f197,plain,(
% 1.65/0.57    ( ! [X0] : (r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0) | v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.65/0.57    inference(duplicate_literal_removal,[],[f194])).
% 1.65/0.57  fof(f194,plain,(
% 1.65/0.57    ( ! [X0] : (v1_xboole_0(k1_zfmisc_1(X0)) | r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0) | r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0)) )),
% 1.65/0.57    inference(resolution,[],[f130,f72])).
% 1.65/0.57  fof(f72,plain,(
% 1.65/0.57    ( ! [X0,X1] : (~r1_tarski(sK4(X0,X1),X1) | r1_tarski(k3_tarski(X0),X1)) )),
% 1.65/0.57    inference(cnf_transformation,[],[f37])).
% 1.65/0.57  fof(f37,plain,(
% 1.65/0.57    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | (~r1_tarski(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.65/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f36])).
% 1.65/0.57  fof(f36,plain,(
% 1.65/0.57    ! [X1,X0] : (? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)) => (~r1_tarski(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.65/0.57    introduced(choice_axiom,[])).
% 1.65/0.57  fof(f24,plain,(
% 1.65/0.57    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 1.65/0.57    inference(ennf_transformation,[],[f3])).
% 1.65/0.57  fof(f3,axiom,(
% 1.65/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 1.65/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).
% 1.65/0.57  fof(f130,plain,(
% 1.65/0.57    ( ! [X0,X1] : (r1_tarski(sK4(k1_zfmisc_1(X0),X1),X0) | v1_xboole_0(k1_zfmisc_1(X0)) | r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X1)) )),
% 1.65/0.57    inference(resolution,[],[f112,f76])).
% 1.65/0.57  fof(f76,plain,(
% 1.65/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.65/0.57    inference(cnf_transformation,[],[f40])).
% 1.65/0.57  fof(f112,plain,(
% 1.65/0.57    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),X0) | r1_tarski(k3_tarski(X0),X1) | v1_xboole_0(X0)) )),
% 1.65/0.57    inference(resolution,[],[f71,f66])).
% 1.65/0.57  fof(f66,plain,(
% 1.65/0.57    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.65/0.57    inference(cnf_transformation,[],[f35])).
% 1.65/0.57  fof(f71,plain,(
% 1.65/0.57    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(k3_tarski(X0),X1)) )),
% 1.65/0.57    inference(cnf_transformation,[],[f37])).
% 1.65/0.57  fof(f280,plain,(
% 1.65/0.57    ~v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | spl6_13),
% 1.65/0.57    inference(avatar_component_clause,[],[f279])).
% 1.65/0.57  fof(f120,plain,(
% 1.65/0.57    spl6_6 | ~spl6_5),
% 1.65/0.57    inference(avatar_split_clause,[],[f113,f108,f117])).
% 1.65/0.57  fof(f113,plain,(
% 1.65/0.57    r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_5),
% 1.65/0.57    inference(resolution,[],[f110,f76])).
% 1.65/0.57  fof(f111,plain,(
% 1.65/0.57    spl6_5 | ~spl6_3),
% 1.65/0.57    inference(avatar_split_clause,[],[f105,f94,f108])).
% 1.65/0.57  fof(f105,plain,(
% 1.65/0.57    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl6_3),
% 1.65/0.57    inference(resolution,[],[f46,f96])).
% 1.65/0.57  fof(f46,plain,(
% 1.65/0.57    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.65/0.57    inference(cnf_transformation,[],[f18])).
% 1.65/0.57  fof(f18,plain,(
% 1.65/0.57    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.65/0.57    inference(ennf_transformation,[],[f9])).
% 1.65/0.57  fof(f9,axiom,(
% 1.65/0.57    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.65/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 1.65/0.57  fof(f102,plain,(
% 1.65/0.57    ~spl6_4),
% 1.65/0.57    inference(avatar_split_clause,[],[f44,f99])).
% 1.65/0.57  fof(f44,plain,(
% 1.65/0.57    u1_struct_0(sK0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))),
% 1.65/0.57    inference(cnf_transformation,[],[f27])).
% 1.65/0.57  fof(f27,plain,(
% 1.65/0.57    u1_struct_0(sK0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.65/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f26])).
% 1.65/0.57  fof(f26,plain,(
% 1.65/0.57    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (u1_struct_0(sK0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.65/0.57    introduced(choice_axiom,[])).
% 1.65/0.57  fof(f15,plain,(
% 1.65/0.57    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.65/0.57    inference(flattening,[],[f14])).
% 1.65/0.57  fof(f14,plain,(
% 1.65/0.57    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.65/0.57    inference(ennf_transformation,[],[f12])).
% 1.65/0.57  fof(f12,negated_conjecture,(
% 1.65/0.57    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 1.65/0.57    inference(negated_conjecture,[],[f11])).
% 1.65/0.57  fof(f11,conjecture,(
% 1.65/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 1.65/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow_1)).
% 1.65/0.57  fof(f97,plain,(
% 1.65/0.57    spl6_3),
% 1.65/0.57    inference(avatar_split_clause,[],[f43,f94])).
% 1.65/0.57  fof(f43,plain,(
% 1.65/0.57    l1_pre_topc(sK0)),
% 1.65/0.57    inference(cnf_transformation,[],[f27])).
% 1.65/0.57  fof(f92,plain,(
% 1.65/0.57    spl6_2),
% 1.65/0.57    inference(avatar_split_clause,[],[f42,f89])).
% 1.65/0.57  fof(f42,plain,(
% 1.65/0.57    v2_pre_topc(sK0)),
% 1.65/0.57    inference(cnf_transformation,[],[f27])).
% 1.65/0.57  % SZS output end Proof for theBenchmark
% 1.65/0.57  % (27047)------------------------------
% 1.65/0.57  % (27047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.57  % (27047)Termination reason: Refutation
% 1.65/0.57  
% 1.65/0.57  % (27047)Memory used [KB]: 6652
% 1.65/0.57  % (27047)Time elapsed: 0.133 s
% 1.65/0.57  % (27047)------------------------------
% 1.65/0.57  % (27047)------------------------------
% 1.65/0.58  % (27044)Success in time 0.214 s
%------------------------------------------------------------------------------
