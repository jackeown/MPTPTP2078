%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:31 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 276 expanded)
%              Number of leaves         :   28 ( 108 expanded)
%              Depth                    :   15
%              Number of atoms          :  525 (1661 expanded)
%              Number of equality atoms :   61 ( 227 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f344,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f70,f75,f84,f90,f95,f100,f124,f162,f167,f190,f250,f273,f283,f288,f320,f337])).

fof(f337,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_13
    | spl3_22 ),
    inference(avatar_contradiction_clause,[],[f336])).

fof(f336,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_13
    | spl3_22 ),
    inference(subsumption_resolution,[],[f335,f319])).

fof(f319,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | spl3_22 ),
    inference(avatar_component_clause,[],[f317])).

fof(f317,plain,
    ( spl3_22
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f335,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f325,f165])).

fof(f165,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl3_13
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f325,plain,
    ( r1_tarski(sK2,k1_tops_1(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f69,f89,f83,f74,f99,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

fof(f99,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl3_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f74,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f83,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl3_5
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f89,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl3_6
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f69,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl3_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f320,plain,
    ( ~ spl3_22
    | spl3_7 ),
    inference(avatar_split_clause,[],[f315,f92,f317])).

fof(f92,plain,
    ( spl3_7
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f315,plain,
    ( ~ r1_tarski(sK2,k1_xboole_0)
    | spl3_7 ),
    inference(unit_resulting_resolution,[],[f43,f94,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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

fof(f94,plain,
    ( k1_xboole_0 != sK2
    | spl3_7 ),
    inference(avatar_component_clause,[],[f92])).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f288,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_13 ),
    inference(avatar_contradiction_clause,[],[f287])).

fof(f287,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_13 ),
    inference(subsumption_resolution,[],[f78,f175])).

fof(f175,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ spl3_2
    | ~ spl3_3
    | spl3_13 ),
    inference(unit_resulting_resolution,[],[f69,f74,f166,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_1(X1,X0)
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(f166,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f164])).

fof(f78,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl3_4
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f283,plain,
    ( spl3_4
    | ~ spl3_12
    | spl3_13
    | ~ spl3_17
    | ~ spl3_20 ),
    inference(avatar_contradiction_clause,[],[f282])).

fof(f282,plain,
    ( $false
    | spl3_4
    | ~ spl3_12
    | spl3_13
    | ~ spl3_17
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f281,f265])).

fof(f265,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_17 ),
    inference(unit_resulting_resolution,[],[f249,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f249,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl3_17
  <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f281,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_4
    | ~ spl3_12
    | spl3_13
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f280,f161])).

fof(f161,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl3_12
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f280,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_4
    | spl3_13
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f275,f166])).

fof(f275,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_4
    | ~ spl3_20 ),
    inference(resolution,[],[f272,f85])).

fof(f85,plain,
    ( ! [X3] :
        ( ~ v3_pre_topc(X3,sK0)
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,sK1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl3_4 ),
    inference(subsumption_resolution,[],[f38,f79])).

fof(f79,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f38,plain,(
    ! [X3] :
      ( k1_xboole_0 = X3
      | ~ v3_pre_topc(X3,sK0)
      | ~ r1_tarski(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ( k1_xboole_0 != sK2
        & v3_pre_topc(sK2,sK0)
        & r1_tarski(sK2,sK1)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ v2_tops_1(sK1,sK0) )
    & ( ! [X3] :
          ( k1_xboole_0 = X3
          | ~ v3_pre_topc(X3,sK0)
          | ~ r1_tarski(X3,sK1)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( k1_xboole_0 != X2
                  & v3_pre_topc(X2,X0)
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tops_1(X1,X0) )
            & ( ! [X3] :
                  ( k1_xboole_0 = X3
                  | ~ v3_pre_topc(X3,X0)
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,sK0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ v2_tops_1(X1,sK0) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,sK0)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( k1_xboole_0 != X2
              & v3_pre_topc(X2,sK0)
              & r1_tarski(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          | ~ v2_tops_1(X1,sK0) )
        & ( ! [X3] :
              ( k1_xboole_0 = X3
              | ~ v3_pre_topc(X3,sK0)
              | ~ r1_tarski(X3,X1)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          | v2_tops_1(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ? [X2] :
            ( k1_xboole_0 != X2
            & v3_pre_topc(X2,sK0)
            & r1_tarski(X2,sK1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        | ~ v2_tops_1(sK1,sK0) )
      & ( ! [X3] :
            ( k1_xboole_0 = X3
            | ~ v3_pre_topc(X3,sK0)
            | ~ r1_tarski(X3,sK1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        | v2_tops_1(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( k1_xboole_0 != X2
        & v3_pre_topc(X2,sK0)
        & r1_tarski(X2,sK1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k1_xboole_0 != sK2
      & v3_pre_topc(sK2,sK0)
      & r1_tarski(sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X3] :
                ( k1_xboole_0 = X3
                | ~ v3_pre_topc(X3,X0)
                | ~ r1_tarski(X3,X1)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( k1_xboole_0 != X2
                & v3_pre_topc(X2,X0)
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ v2_tops_1(X1,X0) )
          & ( ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( v3_pre_topc(X2,X0)
                      & r1_tarski(X2,X1) )
                   => k1_xboole_0 = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & r1_tarski(X2,X1) )
                 => k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).

fof(f272,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f270])).

fof(f270,plain,
    ( spl3_20
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

% (26394)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f273,plain,
    ( spl3_20
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_14
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f268,f247,f187,f67,f62,f270])).

fof(f62,plain,
    ( spl3_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f187,plain,
    ( spl3_14
  <=> k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f268,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_14
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f200,f265])).

fof(f200,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f199,f64])).

fof(f64,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f199,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ spl3_2
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f198,f69])).

fof(f198,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_14 ),
    inference(trivial_inequality_removal,[],[f196])).

fof(f196,plain,
    ( k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1)
    | v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_14 ),
    inference(superposition,[],[f60,f189])).

fof(f189,plain,
    ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f187])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X1,X0) != X0
      | v3_pre_topc(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(duplicate_literal_removal,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | v3_pre_topc(X0,X1)
      | k1_tops_1(X1,X0) != X0
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1) ) ),
    inference(condensation,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

fof(f250,plain,
    ( spl3_17
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f171,f159,f121,f247])).

fof(f121,plain,
    ( spl3_9
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f171,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f123,f161,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f123,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f121])).

fof(f190,plain,
    ( spl3_14
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f126,f72,f67,f187])).

fof(f126,plain,
    ( k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f69,f74,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

fof(f167,plain,
    ( ~ spl3_13
    | ~ spl3_2
    | ~ spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f125,f77,f72,f67,f164])).

fof(f125,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | ~ spl3_2
    | ~ spl3_3
    | spl3_4 ),
    inference(unit_resulting_resolution,[],[f69,f79,f74,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_tops_1(X0,X1)
      | v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f162,plain,
    ( spl3_12
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f118,f72,f67,f159])).

fof(f118,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f69,f74,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f124,plain,
    ( spl3_9
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f101,f72,f121])).

fof(f101,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f74,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f100,plain,
    ( ~ spl3_4
    | spl3_8 ),
    inference(avatar_split_clause,[],[f39,f97,f77])).

fof(f39,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f95,plain,
    ( ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f42,f92,f77])).

fof(f42,plain,
    ( k1_xboole_0 != sK2
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f90,plain,
    ( ~ spl3_4
    | spl3_6 ),
    inference(avatar_split_clause,[],[f41,f87,f77])).

fof(f41,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f84,plain,
    ( ~ spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f40,f81,f77])).

fof(f40,plain,
    ( r1_tarski(sK2,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f75,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f37,f72])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f70,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f36,f67])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f65,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f35,f62])).

fof(f35,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:49:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.50  % (26380)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.23/0.50  % (26396)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.23/0.51  % (26396)Refutation found. Thanks to Tanya!
% 0.23/0.51  % SZS status Theorem for theBenchmark
% 0.23/0.51  % (26380)Refutation not found, incomplete strategy% (26380)------------------------------
% 0.23/0.51  % (26380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.51  % (26380)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.51  
% 0.23/0.51  % (26380)Memory used [KB]: 1663
% 0.23/0.51  % (26380)Time elapsed: 0.069 s
% 0.23/0.51  % (26380)------------------------------
% 0.23/0.51  % (26380)------------------------------
% 0.23/0.51  % SZS output start Proof for theBenchmark
% 0.23/0.51  fof(f344,plain,(
% 0.23/0.51    $false),
% 0.23/0.51    inference(avatar_sat_refutation,[],[f65,f70,f75,f84,f90,f95,f100,f124,f162,f167,f190,f250,f273,f283,f288,f320,f337])).
% 0.23/0.51  fof(f337,plain,(
% 0.23/0.51    ~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_6 | ~spl3_8 | ~spl3_13 | spl3_22),
% 0.23/0.51    inference(avatar_contradiction_clause,[],[f336])).
% 0.23/0.51  fof(f336,plain,(
% 0.23/0.51    $false | (~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_6 | ~spl3_8 | ~spl3_13 | spl3_22)),
% 0.23/0.51    inference(subsumption_resolution,[],[f335,f319])).
% 0.23/0.51  fof(f319,plain,(
% 0.23/0.51    ~r1_tarski(sK2,k1_xboole_0) | spl3_22),
% 0.23/0.51    inference(avatar_component_clause,[],[f317])).
% 0.23/0.51  fof(f317,plain,(
% 0.23/0.51    spl3_22 <=> r1_tarski(sK2,k1_xboole_0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.23/0.51  fof(f335,plain,(
% 0.23/0.51    r1_tarski(sK2,k1_xboole_0) | (~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_6 | ~spl3_8 | ~spl3_13)),
% 0.23/0.51    inference(forward_demodulation,[],[f325,f165])).
% 0.23/0.51  fof(f165,plain,(
% 0.23/0.51    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl3_13),
% 0.23/0.51    inference(avatar_component_clause,[],[f164])).
% 0.23/0.51  fof(f164,plain,(
% 0.23/0.51    spl3_13 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.23/0.51  fof(f325,plain,(
% 0.23/0.51    r1_tarski(sK2,k1_tops_1(sK0,sK1)) | (~spl3_2 | ~spl3_3 | ~spl3_5 | ~spl3_6 | ~spl3_8)),
% 0.23/0.51    inference(unit_resulting_resolution,[],[f69,f89,f83,f74,f99,f47])).
% 0.23/0.51  fof(f47,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~v3_pre_topc(X1,X0) | ~r1_tarski(X1,X2) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f17])).
% 0.23/0.51  fof(f17,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.51    inference(flattening,[],[f16])).
% 0.23/0.51  fof(f16,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.51    inference(ennf_transformation,[],[f8])).
% 0.23/0.51  fof(f8,axiom,(
% 0.23/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).
% 0.23/0.51  fof(f99,plain,(
% 0.23/0.51    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_8),
% 0.23/0.51    inference(avatar_component_clause,[],[f97])).
% 0.23/0.51  fof(f97,plain,(
% 0.23/0.51    spl3_8 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.23/0.51  fof(f74,plain,(
% 0.23/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 0.23/0.51    inference(avatar_component_clause,[],[f72])).
% 0.23/0.51  fof(f72,plain,(
% 0.23/0.51    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.23/0.51  fof(f83,plain,(
% 0.23/0.51    r1_tarski(sK2,sK1) | ~spl3_5),
% 0.23/0.51    inference(avatar_component_clause,[],[f81])).
% 0.23/0.51  fof(f81,plain,(
% 0.23/0.51    spl3_5 <=> r1_tarski(sK2,sK1)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.23/0.51  fof(f89,plain,(
% 0.23/0.51    v3_pre_topc(sK2,sK0) | ~spl3_6),
% 0.23/0.51    inference(avatar_component_clause,[],[f87])).
% 0.23/0.51  fof(f87,plain,(
% 0.23/0.51    spl3_6 <=> v3_pre_topc(sK2,sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.23/0.51  fof(f69,plain,(
% 0.23/0.51    l1_pre_topc(sK0) | ~spl3_2),
% 0.23/0.51    inference(avatar_component_clause,[],[f67])).
% 0.23/0.51  fof(f67,plain,(
% 0.23/0.51    spl3_2 <=> l1_pre_topc(sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.23/0.51  fof(f320,plain,(
% 0.23/0.51    ~spl3_22 | spl3_7),
% 0.23/0.51    inference(avatar_split_clause,[],[f315,f92,f317])).
% 0.23/0.51  fof(f92,plain,(
% 0.23/0.51    spl3_7 <=> k1_xboole_0 = sK2),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.23/0.51  fof(f315,plain,(
% 0.23/0.51    ~r1_tarski(sK2,k1_xboole_0) | spl3_7),
% 0.23/0.51    inference(unit_resulting_resolution,[],[f43,f94,f53])).
% 0.23/0.51  fof(f53,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.23/0.51    inference(cnf_transformation,[],[f33])).
% 0.23/0.51  fof(f33,plain,(
% 0.23/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.23/0.51    inference(flattening,[],[f32])).
% 0.23/0.51  fof(f32,plain,(
% 0.23/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.23/0.51    inference(nnf_transformation,[],[f1])).
% 0.23/0.51  fof(f1,axiom,(
% 0.23/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.23/0.51  fof(f94,plain,(
% 0.23/0.51    k1_xboole_0 != sK2 | spl3_7),
% 0.23/0.51    inference(avatar_component_clause,[],[f92])).
% 0.23/0.51  fof(f43,plain,(
% 0.23/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f3])).
% 0.23/0.51  fof(f3,axiom,(
% 0.23/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.23/0.51  fof(f288,plain,(
% 0.23/0.51    ~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_13),
% 0.23/0.51    inference(avatar_contradiction_clause,[],[f287])).
% 0.23/0.51  fof(f287,plain,(
% 0.23/0.51    $false | (~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_13)),
% 0.23/0.51    inference(subsumption_resolution,[],[f78,f175])).
% 0.23/0.51  fof(f175,plain,(
% 0.23/0.51    ~v2_tops_1(sK1,sK0) | (~spl3_2 | ~spl3_3 | spl3_13)),
% 0.23/0.51    inference(unit_resulting_resolution,[],[f69,f74,f166,f45])).
% 0.23/0.51  fof(f45,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~v2_tops_1(X1,X0) | k1_xboole_0 = k1_tops_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f31])).
% 0.23/0.51  fof(f31,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.51    inference(nnf_transformation,[],[f15])).
% 0.23/0.51  fof(f15,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.51    inference(ennf_transformation,[],[f9])).
% 0.23/0.51  fof(f9,axiom,(
% 0.23/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).
% 0.23/0.51  fof(f166,plain,(
% 0.23/0.51    k1_xboole_0 != k1_tops_1(sK0,sK1) | spl3_13),
% 0.23/0.51    inference(avatar_component_clause,[],[f164])).
% 0.23/0.51  fof(f78,plain,(
% 0.23/0.51    v2_tops_1(sK1,sK0) | ~spl3_4),
% 0.23/0.51    inference(avatar_component_clause,[],[f77])).
% 0.23/0.51  fof(f77,plain,(
% 0.23/0.51    spl3_4 <=> v2_tops_1(sK1,sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.23/0.51  fof(f283,plain,(
% 0.23/0.51    spl3_4 | ~spl3_12 | spl3_13 | ~spl3_17 | ~spl3_20),
% 0.23/0.51    inference(avatar_contradiction_clause,[],[f282])).
% 0.23/0.51  fof(f282,plain,(
% 0.23/0.51    $false | (spl3_4 | ~spl3_12 | spl3_13 | ~spl3_17 | ~spl3_20)),
% 0.23/0.51    inference(subsumption_resolution,[],[f281,f265])).
% 0.23/0.51  fof(f265,plain,(
% 0.23/0.51    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_17),
% 0.23/0.51    inference(unit_resulting_resolution,[],[f249,f55])).
% 0.23/0.51  fof(f55,plain,(
% 0.23/0.51    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f34])).
% 0.23/0.51  fof(f34,plain,(
% 0.23/0.51    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.23/0.51    inference(nnf_transformation,[],[f4])).
% 0.23/0.51  fof(f4,axiom,(
% 0.23/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.23/0.51  fof(f249,plain,(
% 0.23/0.51    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | ~spl3_17),
% 0.23/0.51    inference(avatar_component_clause,[],[f247])).
% 0.23/0.51  fof(f247,plain,(
% 0.23/0.51    spl3_17 <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.23/0.51  fof(f281,plain,(
% 0.23/0.51    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_4 | ~spl3_12 | spl3_13 | ~spl3_20)),
% 0.23/0.51    inference(subsumption_resolution,[],[f280,f161])).
% 0.23/0.51  fof(f161,plain,(
% 0.23/0.51    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl3_12),
% 0.23/0.51    inference(avatar_component_clause,[],[f159])).
% 0.23/0.51  fof(f159,plain,(
% 0.23/0.51    spl3_12 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.23/0.51  fof(f280,plain,(
% 0.23/0.51    ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_4 | spl3_13 | ~spl3_20)),
% 0.23/0.51    inference(subsumption_resolution,[],[f275,f166])).
% 0.23/0.51  fof(f275,plain,(
% 0.23/0.51    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (spl3_4 | ~spl3_20)),
% 0.23/0.51    inference(resolution,[],[f272,f85])).
% 0.23/0.51  fof(f85,plain,(
% 0.23/0.51    ( ! [X3] : (~v3_pre_topc(X3,sK0) | k1_xboole_0 = X3 | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) ) | spl3_4),
% 0.23/0.51    inference(subsumption_resolution,[],[f38,f79])).
% 0.23/0.51  fof(f79,plain,(
% 0.23/0.51    ~v2_tops_1(sK1,sK0) | spl3_4),
% 0.23/0.51    inference(avatar_component_clause,[],[f77])).
% 0.23/0.51  fof(f38,plain,(
% 0.23/0.51    ( ! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tops_1(sK1,sK0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f30])).
% 0.23/0.51  fof(f30,plain,(
% 0.23/0.51    (((k1_xboole_0 != sK2 & v3_pre_topc(sK2,sK0) & r1_tarski(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(sK1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.23/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).
% 0.23/0.51  fof(f27,plain,(
% 0.23/0.51    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(X1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.23/0.51    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f28,plain,(
% 0.23/0.51    ? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(X1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) | ~v2_tops_1(sK1,sK0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | v2_tops_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.23/0.51    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f29,plain,(
% 0.23/0.51    ? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,sK0) & r1_tarski(X2,sK1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (k1_xboole_0 != sK2 & v3_pre_topc(sK2,sK0) & r1_tarski(sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.23/0.51    introduced(choice_axiom,[])).
% 0.23/0.51  fof(f26,plain,(
% 0.23/0.51    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X3] : (k1_xboole_0 = X3 | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.23/0.51    inference(rectify,[],[f25])).
% 0.23/0.51  fof(f25,plain,(
% 0.23/0.51    ? [X0] : (? [X1] : ((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.23/0.51    inference(flattening,[],[f24])).
% 0.23/0.51  fof(f24,plain,(
% 0.23/0.51    ? [X0] : (? [X1] : (((? [X2] : (k1_xboole_0 != X2 & v3_pre_topc(X2,X0) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tops_1(X1,X0)) & (! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | v2_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.23/0.51    inference(nnf_transformation,[],[f13])).
% 0.23/0.51  fof(f13,plain,(
% 0.23/0.51    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.23/0.51    inference(flattening,[],[f12])).
% 0.23/0.51  fof(f12,plain,(
% 0.23/0.51    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.23/0.51    inference(ennf_transformation,[],[f11])).
% 0.23/0.51  fof(f11,negated_conjecture,(
% 0.23/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 0.23/0.51    inference(negated_conjecture,[],[f10])).
% 0.23/0.51  fof(f10,conjecture,(
% 0.23/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).
% 0.23/0.51  fof(f272,plain,(
% 0.23/0.51    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~spl3_20),
% 0.23/0.51    inference(avatar_component_clause,[],[f270])).
% 0.23/0.51  fof(f270,plain,(
% 0.23/0.51    spl3_20 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.23/0.51  % (26394)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.23/0.51  fof(f273,plain,(
% 0.23/0.51    spl3_20 | ~spl3_1 | ~spl3_2 | ~spl3_14 | ~spl3_17),
% 0.23/0.51    inference(avatar_split_clause,[],[f268,f247,f187,f67,f62,f270])).
% 0.23/0.51  fof(f62,plain,(
% 0.23/0.51    spl3_1 <=> v2_pre_topc(sK0)),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.23/0.51  fof(f187,plain,(
% 0.23/0.51    spl3_14 <=> k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.23/0.51  fof(f268,plain,(
% 0.23/0.51    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | (~spl3_1 | ~spl3_2 | ~spl3_14 | ~spl3_17)),
% 0.23/0.51    inference(subsumption_resolution,[],[f200,f265])).
% 0.23/0.51  fof(f200,plain,(
% 0.23/0.51    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_1 | ~spl3_2 | ~spl3_14)),
% 0.23/0.51    inference(subsumption_resolution,[],[f199,f64])).
% 0.23/0.51  fof(f64,plain,(
% 0.23/0.51    v2_pre_topc(sK0) | ~spl3_1),
% 0.23/0.51    inference(avatar_component_clause,[],[f62])).
% 0.23/0.51  fof(f199,plain,(
% 0.23/0.51    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | (~spl3_2 | ~spl3_14)),
% 0.23/0.51    inference(subsumption_resolution,[],[f198,f69])).
% 0.23/0.51  fof(f198,plain,(
% 0.23/0.51    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl3_14),
% 0.23/0.51    inference(trivial_inequality_removal,[],[f196])).
% 0.23/0.51  fof(f196,plain,(
% 0.23/0.51    k1_tops_1(sK0,sK1) != k1_tops_1(sK0,sK1) | v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl3_14),
% 0.23/0.51    inference(superposition,[],[f60,f189])).
% 0.23/0.51  fof(f189,plain,(
% 0.23/0.51    k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1)) | ~spl3_14),
% 0.23/0.51    inference(avatar_component_clause,[],[f187])).
% 0.23/0.51  fof(f60,plain,(
% 0.23/0.51    ( ! [X0,X1] : (k1_tops_1(X1,X0) != X0 | v3_pre_topc(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 0.23/0.51    inference(duplicate_literal_removal,[],[f59])).
% 0.23/0.51  fof(f59,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | v3_pre_topc(X0,X1) | k1_tops_1(X1,X0) != X0 | ~l1_pre_topc(X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) )),
% 0.23/0.51    inference(condensation,[],[f49])).
% 0.23/0.51  fof(f49,plain,(
% 0.23/0.51    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f19])).
% 0.23/0.51  fof(f19,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.23/0.51    inference(flattening,[],[f18])).
% 0.23/0.51  fof(f18,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.23/0.51    inference(ennf_transformation,[],[f7])).
% 0.23/0.51  fof(f7,axiom,(
% 0.23/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).
% 0.23/0.51  fof(f250,plain,(
% 0.23/0.51    spl3_17 | ~spl3_9 | ~spl3_12),
% 0.23/0.51    inference(avatar_split_clause,[],[f171,f159,f121,f247])).
% 0.23/0.51  fof(f121,plain,(
% 0.23/0.51    spl3_9 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 0.23/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.23/0.51  fof(f171,plain,(
% 0.23/0.51    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | (~spl3_9 | ~spl3_12)),
% 0.23/0.51    inference(unit_resulting_resolution,[],[f123,f161,f56])).
% 0.23/0.51  fof(f56,plain,(
% 0.23/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f23])).
% 0.23/0.51  fof(f23,plain,(
% 0.23/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.23/0.51    inference(flattening,[],[f22])).
% 0.23/0.51  fof(f22,plain,(
% 0.23/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.23/0.51    inference(ennf_transformation,[],[f2])).
% 0.23/0.51  fof(f2,axiom,(
% 0.23/0.51    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.23/0.51  fof(f123,plain,(
% 0.23/0.51    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_9),
% 0.23/0.51    inference(avatar_component_clause,[],[f121])).
% 0.23/0.51  fof(f190,plain,(
% 0.23/0.51    spl3_14 | ~spl3_2 | ~spl3_3),
% 0.23/0.51    inference(avatar_split_clause,[],[f126,f72,f67,f187])).
% 0.23/0.51  fof(f126,plain,(
% 0.23/0.51    k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1)) | (~spl3_2 | ~spl3_3)),
% 0.23/0.51    inference(unit_resulting_resolution,[],[f69,f74,f50])).
% 0.23/0.51  fof(f50,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))) )),
% 0.23/0.51    inference(cnf_transformation,[],[f21])).
% 0.23/0.51  fof(f21,plain,(
% 0.23/0.51    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.23/0.51    inference(flattening,[],[f20])).
% 0.23/0.51  fof(f20,plain,(
% 0.23/0.51    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.23/0.51    inference(ennf_transformation,[],[f5])).
% 0.23/0.51  fof(f5,axiom,(
% 0.23/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).
% 0.23/0.51  fof(f167,plain,(
% 0.23/0.51    ~spl3_13 | ~spl3_2 | ~spl3_3 | spl3_4),
% 0.23/0.51    inference(avatar_split_clause,[],[f125,f77,f72,f67,f164])).
% 0.23/0.51  fof(f125,plain,(
% 0.23/0.51    k1_xboole_0 != k1_tops_1(sK0,sK1) | (~spl3_2 | ~spl3_3 | spl3_4)),
% 0.23/0.51    inference(unit_resulting_resolution,[],[f69,f79,f74,f46])).
% 0.23/0.51  fof(f46,plain,(
% 0.23/0.51    ( ! [X0,X1] : (k1_xboole_0 != k1_tops_1(X0,X1) | v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f31])).
% 0.23/0.51  fof(f162,plain,(
% 0.23/0.51    spl3_12 | ~spl3_2 | ~spl3_3),
% 0.23/0.51    inference(avatar_split_clause,[],[f118,f72,f67,f159])).
% 0.23/0.51  fof(f118,plain,(
% 0.23/0.51    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl3_2 | ~spl3_3)),
% 0.23/0.51    inference(unit_resulting_resolution,[],[f69,f74,f44])).
% 0.23/0.51  fof(f44,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f14])).
% 0.23/0.51  fof(f14,plain,(
% 0.23/0.51    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.51    inference(ennf_transformation,[],[f6])).
% 0.23/0.51  fof(f6,axiom,(
% 0.23/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.23/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 0.23/0.51  fof(f124,plain,(
% 0.23/0.51    spl3_9 | ~spl3_3),
% 0.23/0.51    inference(avatar_split_clause,[],[f101,f72,f121])).
% 0.23/0.51  fof(f101,plain,(
% 0.23/0.51    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_3),
% 0.23/0.51    inference(unit_resulting_resolution,[],[f74,f54])).
% 0.23/0.51  fof(f54,plain,(
% 0.23/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.23/0.51    inference(cnf_transformation,[],[f34])).
% 0.23/0.51  fof(f100,plain,(
% 0.23/0.51    ~spl3_4 | spl3_8),
% 0.23/0.51    inference(avatar_split_clause,[],[f39,f97,f77])).
% 0.23/0.51  fof(f39,plain,(
% 0.23/0.51    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(sK1,sK0)),
% 0.23/0.51    inference(cnf_transformation,[],[f30])).
% 0.23/0.51  fof(f95,plain,(
% 0.23/0.51    ~spl3_4 | ~spl3_7),
% 0.23/0.51    inference(avatar_split_clause,[],[f42,f92,f77])).
% 0.23/0.51  fof(f42,plain,(
% 0.23/0.51    k1_xboole_0 != sK2 | ~v2_tops_1(sK1,sK0)),
% 0.23/0.51    inference(cnf_transformation,[],[f30])).
% 0.23/0.51  fof(f90,plain,(
% 0.23/0.51    ~spl3_4 | spl3_6),
% 0.23/0.51    inference(avatar_split_clause,[],[f41,f87,f77])).
% 0.23/0.51  fof(f41,plain,(
% 0.23/0.51    v3_pre_topc(sK2,sK0) | ~v2_tops_1(sK1,sK0)),
% 0.23/0.51    inference(cnf_transformation,[],[f30])).
% 0.23/0.51  fof(f84,plain,(
% 0.23/0.51    ~spl3_4 | spl3_5),
% 0.23/0.51    inference(avatar_split_clause,[],[f40,f81,f77])).
% 0.23/0.51  fof(f40,plain,(
% 0.23/0.51    r1_tarski(sK2,sK1) | ~v2_tops_1(sK1,sK0)),
% 0.23/0.51    inference(cnf_transformation,[],[f30])).
% 0.23/0.51  fof(f75,plain,(
% 0.23/0.51    spl3_3),
% 0.23/0.51    inference(avatar_split_clause,[],[f37,f72])).
% 0.23/0.51  fof(f37,plain,(
% 0.23/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.51    inference(cnf_transformation,[],[f30])).
% 0.23/0.51  fof(f70,plain,(
% 0.23/0.51    spl3_2),
% 0.23/0.51    inference(avatar_split_clause,[],[f36,f67])).
% 0.23/0.51  fof(f36,plain,(
% 0.23/0.51    l1_pre_topc(sK0)),
% 0.23/0.51    inference(cnf_transformation,[],[f30])).
% 0.23/0.51  fof(f65,plain,(
% 0.23/0.51    spl3_1),
% 0.23/0.51    inference(avatar_split_clause,[],[f35,f62])).
% 0.23/0.51  fof(f35,plain,(
% 0.23/0.51    v2_pre_topc(sK0)),
% 0.23/0.51    inference(cnf_transformation,[],[f30])).
% 0.23/0.51  % SZS output end Proof for theBenchmark
% 0.23/0.51  % (26396)------------------------------
% 0.23/0.51  % (26396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.51  % (26396)Termination reason: Refutation
% 0.23/0.51  
% 0.23/0.51  % (26396)Memory used [KB]: 10746
% 0.23/0.51  % (26396)Time elapsed: 0.082 s
% 0.23/0.51  % (26396)------------------------------
% 0.23/0.51  % (26396)------------------------------
% 0.23/0.51  % (26378)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.23/0.51  % (26372)Success in time 0.143 s
%------------------------------------------------------------------------------
