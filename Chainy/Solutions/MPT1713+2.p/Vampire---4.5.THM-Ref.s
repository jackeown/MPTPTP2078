%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1713+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:30 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 211 expanded)
%              Number of leaves         :   25 (  90 expanded)
%              Depth                    :    8
%              Number of atoms          :  352 (1073 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5338,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4527,f4532,f4537,f4547,f4552,f4557,f4566,f4596,f4606,f4741,f4747,f4773,f5293,f5335,f5337])).

fof(f5337,plain,
    ( ~ spl118_9
    | ~ spl118_33
    | ~ spl118_34
    | ~ spl118_35
    | spl118_50 ),
    inference(avatar_contradiction_clause,[],[f5336])).

fof(f5336,plain,
    ( $false
    | ~ spl118_9
    | ~ spl118_33
    | ~ spl118_34
    | ~ spl118_35
    | spl118_50 ),
    inference(subsumption_resolution,[],[f5298,f4811])).

fof(f4811,plain,
    ( r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl118_9
    | ~ spl118_34
    | ~ spl118_35 ),
    inference(unit_resulting_resolution,[],[f4746,f4561,f4772,f3891])).

fof(f3891,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3687])).

fof(f3687,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3376])).

fof(f3376,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3327])).

fof(f3327,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f4772,plain,
    ( l1_struct_0(sK2)
    | ~ spl118_35 ),
    inference(avatar_component_clause,[],[f4770])).

fof(f4770,plain,
    ( spl118_35
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl118_35])])).

fof(f4561,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ spl118_9 ),
    inference(avatar_component_clause,[],[f4559])).

fof(f4559,plain,
    ( spl118_9
  <=> r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl118_9])])).

fof(f4746,plain,
    ( l1_struct_0(sK1)
    | ~ spl118_34 ),
    inference(avatar_component_clause,[],[f4744])).

fof(f4744,plain,
    ( spl118_34
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl118_34])])).

fof(f5298,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl118_33
    | spl118_50 ),
    inference(unit_resulting_resolution,[],[f4400,f4740,f5292,f3942])).

fof(f3942,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | ~ r1_tarski(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f3428])).

fof(f3428,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f3427])).

fof(f3427,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f134])).

fof(f134,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_xboole_0(X0,X1)
          & r1_tarski(X2,X1)
          & r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).

fof(f5292,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl118_50 ),
    inference(avatar_component_clause,[],[f5290])).

fof(f5290,plain,
    ( spl118_50
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl118_50])])).

fof(f4740,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl118_33 ),
    inference(avatar_component_clause,[],[f4738])).

fof(f4738,plain,
    ( spl118_33
  <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl118_33])])).

fof(f4400,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f4084])).

fof(f4084,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3779])).

fof(f3779,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f3778])).

fof(f3778,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f5335,plain,
    ( ~ spl118_10
    | ~ spl118_33
    | ~ spl118_34
    | ~ spl118_35
    | spl118_50 ),
    inference(avatar_contradiction_clause,[],[f5334])).

fof(f5334,plain,
    ( $false
    | ~ spl118_10
    | ~ spl118_33
    | ~ spl118_34
    | ~ spl118_35
    | spl118_50 ),
    inference(subsumption_resolution,[],[f5299,f4810])).

fof(f4810,plain,
    ( r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl118_10
    | ~ spl118_34
    | ~ spl118_35 ),
    inference(unit_resulting_resolution,[],[f4746,f4565,f4772,f3891])).

fof(f4565,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ spl118_10 ),
    inference(avatar_component_clause,[],[f4563])).

fof(f4563,plain,
    ( spl118_10
  <=> r1_tsep_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl118_10])])).

fof(f5299,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl118_33
    | spl118_50 ),
    inference(unit_resulting_resolution,[],[f4740,f4400,f5292,f3942])).

fof(f5293,plain,
    ( ~ spl118_50
    | spl118_4
    | ~ spl118_34 ),
    inference(avatar_split_clause,[],[f4818,f4744,f4534,f5290])).

fof(f4534,plain,
    ( spl118_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl118_4])])).

fof(f4818,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | spl118_4
    | ~ spl118_34 ),
    inference(unit_resulting_resolution,[],[f4536,f4746,f3918])).

fof(f3918,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3400])).

fof(f3400,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3399])).

fof(f3399,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1795])).

fof(f1795,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f4536,plain,
    ( ~ v2_struct_0(sK1)
    | spl118_4 ),
    inference(avatar_component_clause,[],[f4534])).

fof(f4773,plain,
    ( spl118_35
    | ~ spl118_15 ),
    inference(avatar_split_clause,[],[f4698,f4603,f4770])).

fof(f4603,plain,
    ( spl118_15
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl118_15])])).

fof(f4698,plain,
    ( l1_struct_0(sK2)
    | ~ spl118_15 ),
    inference(unit_resulting_resolution,[],[f4605,f3920])).

fof(f3920,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3402])).

fof(f3402,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1782])).

fof(f1782,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f4605,plain,
    ( l1_pre_topc(sK2)
    | ~ spl118_15 ),
    inference(avatar_component_clause,[],[f4603])).

fof(f4747,plain,
    ( spl118_34
    | ~ spl118_14 ),
    inference(avatar_split_clause,[],[f4697,f4593,f4744])).

fof(f4593,plain,
    ( spl118_14
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl118_14])])).

fof(f4697,plain,
    ( l1_struct_0(sK1)
    | ~ spl118_14 ),
    inference(unit_resulting_resolution,[],[f4595,f3920])).

fof(f4595,plain,
    ( l1_pre_topc(sK1)
    | ~ spl118_14 ),
    inference(avatar_component_clause,[],[f4593])).

fof(f4741,plain,
    ( spl118_33
    | ~ spl118_2
    | ~ spl118_3
    | ~ spl118_6
    | ~ spl118_7
    | ~ spl118_8 ),
    inference(avatar_split_clause,[],[f4607,f4554,f4549,f4544,f4529,f4524,f4738])).

fof(f4524,plain,
    ( spl118_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl118_2])])).

fof(f4529,plain,
    ( spl118_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl118_3])])).

fof(f4544,plain,
    ( spl118_6
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl118_6])])).

fof(f4549,plain,
    ( spl118_7
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl118_7])])).

fof(f4554,plain,
    ( spl118_8
  <=> m1_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl118_8])])).

fof(f4607,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl118_2
    | ~ spl118_3
    | ~ spl118_6
    | ~ spl118_7
    | ~ spl118_8 ),
    inference(unit_resulting_resolution,[],[f4526,f4531,f4546,f4551,f4556,f3900])).

fof(f3900,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f3693])).

fof(f3693,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f3380])).

fof(f3380,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f3379])).

fof(f3379,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3359])).

fof(f3359,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f4556,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ spl118_8 ),
    inference(avatar_component_clause,[],[f4554])).

fof(f4551,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl118_7 ),
    inference(avatar_component_clause,[],[f4549])).

fof(f4546,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl118_6 ),
    inference(avatar_component_clause,[],[f4544])).

fof(f4531,plain,
    ( l1_pre_topc(sK0)
    | ~ spl118_3 ),
    inference(avatar_component_clause,[],[f4529])).

fof(f4526,plain,
    ( v2_pre_topc(sK0)
    | ~ spl118_2 ),
    inference(avatar_component_clause,[],[f4524])).

fof(f4606,plain,
    ( spl118_15
    | ~ spl118_3
    | ~ spl118_7 ),
    inference(avatar_split_clause,[],[f4582,f4549,f4529,f4603])).

fof(f4582,plain,
    ( l1_pre_topc(sK2)
    | ~ spl118_3
    | ~ spl118_7 ),
    inference(unit_resulting_resolution,[],[f4551,f4531,f3910])).

fof(f3910,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f3393])).

fof(f3393,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1784])).

fof(f1784,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f4596,plain,
    ( spl118_14
    | ~ spl118_3
    | ~ spl118_6 ),
    inference(avatar_split_clause,[],[f4581,f4544,f4529,f4593])).

fof(f4581,plain,
    ( l1_pre_topc(sK1)
    | ~ spl118_3
    | ~ spl118_6 ),
    inference(unit_resulting_resolution,[],[f4546,f4531,f3910])).

fof(f4566,plain,
    ( spl118_9
    | spl118_10 ),
    inference(avatar_split_clause,[],[f3889,f4563,f4559])).

fof(f3889,plain,
    ( r1_tsep_1(sK2,sK1)
    | r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f3686])).

fof(f3686,plain,
    ( ( r1_tsep_1(sK2,sK1)
      | r1_tsep_1(sK1,sK2) )
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f3373,f3685,f3684,f3683])).

fof(f3683,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( r1_tsep_1(X2,X1)
                  | r1_tsep_1(X1,X2) )
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3684,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( r1_tsep_1(X2,X1)
              | r1_tsep_1(X1,X2) )
            & m1_pre_topc(X1,X2)
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( r1_tsep_1(X2,sK1)
            | r1_tsep_1(sK1,X2) )
          & m1_pre_topc(sK1,X2)
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f3685,plain,
    ( ? [X2] :
        ( ( r1_tsep_1(X2,sK1)
          | r1_tsep_1(sK1,X2) )
        & m1_pre_topc(sK1,X2)
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ( r1_tsep_1(sK2,sK1)
        | r1_tsep_1(sK1,sK2) )
      & m1_pre_topc(sK1,sK2)
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3373,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3372])).

fof(f3372,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3357])).

fof(f3357,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( m1_pre_topc(X1,X2)
                 => ( ~ r1_tsep_1(X2,X1)
                    & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3356])).

fof(f3356,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( m1_pre_topc(X1,X2)
               => ( ~ r1_tsep_1(X2,X1)
                  & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tmap_1)).

fof(f4557,plain,(
    spl118_8 ),
    inference(avatar_split_clause,[],[f3888,f4554])).

fof(f3888,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f3686])).

fof(f4552,plain,(
    spl118_7 ),
    inference(avatar_split_clause,[],[f3887,f4549])).

fof(f3887,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f3686])).

fof(f4547,plain,(
    spl118_6 ),
    inference(avatar_split_clause,[],[f3885,f4544])).

fof(f3885,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f3686])).

fof(f4537,plain,(
    ~ spl118_4 ),
    inference(avatar_split_clause,[],[f3884,f4534])).

fof(f3884,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f3686])).

fof(f4532,plain,(
    spl118_3 ),
    inference(avatar_split_clause,[],[f3883,f4529])).

fof(f3883,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3686])).

fof(f4527,plain,(
    spl118_2 ),
    inference(avatar_split_clause,[],[f3882,f4524])).

fof(f3882,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3686])).
%------------------------------------------------------------------------------
