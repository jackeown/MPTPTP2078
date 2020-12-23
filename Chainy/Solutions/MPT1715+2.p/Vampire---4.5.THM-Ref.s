%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1715+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:30 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 267 expanded)
%              Number of leaves         :   20 ( 126 expanded)
%              Depth                    :    7
%              Number of atoms          :  427 (2389 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3650,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3459,f3466,f3470,f3474,f3478,f3482,f3486,f3490,f3494,f3498,f3502,f3506,f3606,f3632,f3645,f3649])).

fof(f3649,plain,
    ( spl10_2
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | ~ spl10_8
    | spl10_9
    | ~ spl10_10
    | spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | spl10_14 ),
    inference(avatar_contradiction_clause,[],[f3648])).

fof(f3648,plain,
    ( $false
    | spl10_2
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | ~ spl10_8
    | spl10_9
    | ~ spl10_10
    | spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | spl10_14 ),
    inference(unit_resulting_resolution,[],[f3505,f3501,f3497,f3493,f3477,f3485,f3489,f3481,f3473,f3469,f3458,f3462,f3425])).

fof(f3425,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X3)
      | r1_tsep_1(X3,X1)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | ~ r1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3372])).

fof(f3372,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3371])).

fof(f3371,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3358])).

fof(f3358,axiom,(
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
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tmap_1)).

fof(f3462,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f3461])).

fof(f3461,plain,
    ( spl10_3
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f3458,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f3457])).

fof(f3457,plain,
    ( spl10_2
  <=> r1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f3469,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f3468])).

fof(f3468,plain,
    ( spl10_5
  <=> m1_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f3473,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f3472])).

fof(f3472,plain,
    ( spl10_6
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f3481,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f3480])).

fof(f3480,plain,
    ( spl10_8
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f3489,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f3488])).

fof(f3488,plain,
    ( spl10_10
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f3485,plain,
    ( ~ v2_struct_0(sK2)
    | spl10_9 ),
    inference(avatar_component_clause,[],[f3484])).

% (3044)ott+11_8:1_av=off:bs=on:bce=on:fde=none:gsp=input_only:gs=on:gsem=on:irw=on:lcm=predicate:nm=6:nwc=1.5:sd=2:ss=axioms:st=1.2:sos=theory:urr=on:updr=off_49 on theBenchmark
% (3021)dis+4_8:1_add=large:afp=100000:afq=1.4:ep=RST:fde=unused:gsp=input_only:lcm=predicate:nwc=1:sos=all:sp=occurrence:updr=off:uhcvi=on_33 on theBenchmark
% (3019)lrs+1002_8:1_av=off:cond=on:gsp=input_only:gs=on:irw=on:lma=on:nm=0:nwc=1.7:stl=30:sd=2:ss=axioms:sos=on:sp=occurrence:urr=on_41 on theBenchmark
fof(f3484,plain,
    ( spl10_9
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f3477,plain,
    ( ~ v2_struct_0(sK3)
    | spl10_7 ),
    inference(avatar_component_clause,[],[f3476])).

fof(f3476,plain,
    ( spl10_7
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f3493,plain,
    ( ~ v2_struct_0(sK1)
    | spl10_11 ),
    inference(avatar_component_clause,[],[f3492])).

fof(f3492,plain,
    ( spl10_11
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f3497,plain,
    ( l1_pre_topc(sK0)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f3496])).

fof(f3496,plain,
    ( spl10_12
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f3501,plain,
    ( v2_pre_topc(sK0)
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f3500])).

fof(f3500,plain,
    ( spl10_13
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f3505,plain,
    ( ~ v2_struct_0(sK0)
    | spl10_14 ),
    inference(avatar_component_clause,[],[f3504])).

fof(f3504,plain,
    ( spl10_14
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f3645,plain,
    ( spl10_2
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | ~ spl10_8
    | spl10_9
    | ~ spl10_10
    | spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | spl10_14 ),
    inference(avatar_contradiction_clause,[],[f3635])).

fof(f3635,plain,
    ( $false
    | spl10_2
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | ~ spl10_8
    | spl10_9
    | ~ spl10_10
    | spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | spl10_14 ),
    inference(unit_resulting_resolution,[],[f3505,f3501,f3497,f3493,f3485,f3489,f3481,f3473,f3465,f3469,f3458,f3477,f3427])).

fof(f3427,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X3)
      | r1_tsep_1(X3,X1)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | ~ r1_tsep_1(X3,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3372])).

fof(f3465,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f3464])).

fof(f3464,plain,
    ( spl10_4
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f3632,plain,
    ( spl10_1
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | ~ spl10_8
    | spl10_9
    | ~ spl10_10
    | spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | spl10_14 ),
    inference(avatar_contradiction_clause,[],[f3622])).

fof(f3622,plain,
    ( $false
    | spl10_1
    | ~ spl10_4
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | ~ spl10_8
    | spl10_9
    | ~ spl10_10
    | spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | spl10_14 ),
    inference(unit_resulting_resolution,[],[f3505,f3501,f3497,f3493,f3485,f3489,f3481,f3473,f3465,f3469,f3455,f3477,f3426])).

fof(f3426,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X3)
      | r1_tsep_1(X1,X3)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | ~ r1_tsep_1(X3,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3372])).

fof(f3455,plain,
    ( ~ r1_tsep_1(sK1,sK3)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f3454])).

fof(f3454,plain,
    ( spl10_1
  <=> r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f3606,plain,
    ( spl10_1
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | ~ spl10_8
    | spl10_9
    | ~ spl10_10
    | spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | spl10_14 ),
    inference(avatar_contradiction_clause,[],[f3596])).

fof(f3596,plain,
    ( $false
    | spl10_1
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_6
    | spl10_7
    | ~ spl10_8
    | spl10_9
    | ~ spl10_10
    | spl10_11
    | ~ spl10_12
    | ~ spl10_13
    | spl10_14 ),
    inference(unit_resulting_resolution,[],[f3505,f3501,f3497,f3493,f3485,f3489,f3481,f3473,f3462,f3469,f3455,f3477,f3424])).

fof(f3424,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X3)
      | r1_tsep_1(X1,X3)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | ~ r1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3372])).

fof(f3506,plain,(
    ~ spl10_14 ),
    inference(avatar_split_clause,[],[f3412,f3504])).

fof(f3412,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f3397])).

fof(f3397,plain,
    ( ( ~ r1_tsep_1(sK3,sK1)
      | ~ r1_tsep_1(sK1,sK3) )
    & ( r1_tsep_1(sK3,sK2)
      | r1_tsep_1(sK2,sK3) )
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f3370,f3396,f3395,f3394,f3393])).

fof(f3393,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ r1_tsep_1(X3,X1)
                      | ~ r1_tsep_1(X1,X3) )
                    & ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X2,X3) )
                    & m1_pre_topc(X1,X2)
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f3394,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ r1_tsep_1(X3,X1)
                  | ~ r1_tsep_1(X1,X3) )
                & ( r1_tsep_1(X3,X2)
                  | r1_tsep_1(X2,X3) )
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ r1_tsep_1(X3,sK1)
                | ~ r1_tsep_1(sK1,X3) )
              & ( r1_tsep_1(X3,X2)
                | r1_tsep_1(X2,X3) )
              & m1_pre_topc(sK1,X2)
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f3395,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ r1_tsep_1(X3,sK1)
              | ~ r1_tsep_1(sK1,X3) )
            & ( r1_tsep_1(X3,X2)
              | r1_tsep_1(X2,X3) )
            & m1_pre_topc(sK1,X2)
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( ~ r1_tsep_1(X3,sK1)
            | ~ r1_tsep_1(sK1,X3) )
          & ( r1_tsep_1(X3,sK2)
            | r1_tsep_1(sK2,X3) )
          & m1_pre_topc(sK1,sK2)
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3396,plain,
    ( ? [X3] :
        ( ( ~ r1_tsep_1(X3,sK1)
          | ~ r1_tsep_1(sK1,X3) )
        & ( r1_tsep_1(X3,sK2)
          | r1_tsep_1(sK2,X3) )
        & m1_pre_topc(sK1,sK2)
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ( ~ r1_tsep_1(sK3,sK1)
        | ~ r1_tsep_1(sK1,sK3) )
      & ( r1_tsep_1(sK3,sK2)
        | r1_tsep_1(sK2,sK3) )
      & m1_pre_topc(sK1,sK2)
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f3370,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3369])).

fof(f3369,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3360])).

fof(f3360,negated_conjecture,(
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
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( m1_pre_topc(X1,X2)
                     => ( ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) )
                        | ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3359])).

fof(f3359,conjecture,(
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
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) )
                      | ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tmap_1)).

fof(f3502,plain,(
    spl10_13 ),
    inference(avatar_split_clause,[],[f3413,f3500])).

fof(f3413,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3397])).

fof(f3498,plain,(
    spl10_12 ),
    inference(avatar_split_clause,[],[f3414,f3496])).

fof(f3414,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3397])).

fof(f3494,plain,(
    ~ spl10_11 ),
    inference(avatar_split_clause,[],[f3415,f3492])).

fof(f3415,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f3397])).

fof(f3490,plain,(
    spl10_10 ),
    inference(avatar_split_clause,[],[f3416,f3488])).

fof(f3416,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f3397])).

fof(f3486,plain,(
    ~ spl10_9 ),
    inference(avatar_split_clause,[],[f3417,f3484])).

fof(f3417,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f3397])).

fof(f3482,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f3418,f3480])).

fof(f3418,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f3397])).

fof(f3478,plain,(
    ~ spl10_7 ),
    inference(avatar_split_clause,[],[f3419,f3476])).

fof(f3419,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f3397])).

fof(f3474,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f3420,f3472])).

fof(f3420,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f3397])).

fof(f3470,plain,(
    spl10_5 ),
    inference(avatar_split_clause,[],[f3421,f3468])).

fof(f3421,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f3397])).

fof(f3466,plain,
    ( spl10_3
    | spl10_4 ),
    inference(avatar_split_clause,[],[f3422,f3464,f3461])).

fof(f3422,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f3397])).

fof(f3459,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f3423,f3457,f3454])).

fof(f3423,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | ~ r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f3397])).
%------------------------------------------------------------------------------
