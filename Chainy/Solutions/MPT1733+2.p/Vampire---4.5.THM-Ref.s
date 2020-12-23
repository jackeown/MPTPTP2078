%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1733+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:31 EST 2020

% Result     : Theorem 1.87s
% Output     : Refutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 297 expanded)
%              Number of leaves         :   22 ( 144 expanded)
%              Depth                    :    7
%              Number of atoms          :  483 (3113 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4048,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3574,f3581,f3588,f3589,f3593,f3597,f3601,f3605,f3609,f3613,f3617,f3621,f3625,f3629,f4001,f4016,f4030,f4045])).

fof(f4045,plain,
    ( spl9_2
    | ~ spl9_6
    | spl9_7
    | ~ spl9_8
    | spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16 ),
    inference(avatar_contradiction_clause,[],[f4034])).

fof(f4034,plain,
    ( $false
    | spl9_2
    | ~ spl9_6
    | spl9_7
    | ~ spl9_8
    | spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16 ),
    inference(unit_resulting_resolution,[],[f3628,f3624,f3620,f3616,f3600,f3608,f3612,f3604,f3587,f3596,f3592,f3573,f3503])).

fof(f3503,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X3)
      | r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | ~ r1_tsep_1(X3,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3412])).

fof(f3412,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X3,X1) )
                      | r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                    & ( ( ~ r1_tsep_1(X2,X3)
                        & ~ r1_tsep_1(X1,X3) )
                      | r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) ) )
                  | r1_tsep_1(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3411])).

fof(f3411,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X3,X1) )
                      | r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                    & ( ( ~ r1_tsep_1(X2,X3)
                        & ~ r1_tsep_1(X1,X3) )
                      | r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) ) )
                  | r1_tsep_1(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3381])).

fof(f3381,axiom,(
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
                 => ( ~ r1_tsep_1(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
                       => ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X3,X1) ) )
                      & ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                       => ( ~ r1_tsep_1(X2,X3)
                          & ~ r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tmap_1)).

fof(f3573,plain,
    ( ~ r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
    | spl9_2 ),
    inference(avatar_component_clause,[],[f3572])).

fof(f3572,plain,
    ( spl9_2
  <=> r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f3592,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | spl9_7 ),
    inference(avatar_component_clause,[],[f3591])).

fof(f3591,plain,
    ( spl9_7
  <=> r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f3596,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f3595])).

fof(f3595,plain,
    ( spl9_8
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f3587,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f3586])).

fof(f3586,plain,
    ( spl9_6
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f3604,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f3603])).

fof(f3603,plain,
    ( spl9_10
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f3612,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f3611])).

fof(f3611,plain,
    ( spl9_12
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f3608,plain,
    ( ~ v2_struct_0(sK2)
    | spl9_11 ),
    inference(avatar_component_clause,[],[f3607])).

fof(f3607,plain,
    ( spl9_11
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f3600,plain,
    ( ~ v2_struct_0(sK3)
    | spl9_9 ),
    inference(avatar_component_clause,[],[f3599])).

fof(f3599,plain,
    ( spl9_9
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f3616,plain,
    ( ~ v2_struct_0(sK1)
    | spl9_13 ),
    inference(avatar_component_clause,[],[f3615])).

fof(f3615,plain,
    ( spl9_13
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f3620,plain,
    ( l1_pre_topc(sK0)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f3619])).

fof(f3619,plain,
    ( spl9_14
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f3624,plain,
    ( v2_pre_topc(sK0)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f3623])).

fof(f3623,plain,
    ( spl9_15
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f3628,plain,
    ( ~ v2_struct_0(sK0)
    | spl9_16 ),
    inference(avatar_component_clause,[],[f3627])).

fof(f3627,plain,
    ( spl9_16
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f4030,plain,
    ( spl9_2
    | ~ spl9_5
    | spl9_7
    | ~ spl9_8
    | spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16 ),
    inference(avatar_contradiction_clause,[],[f4019])).

fof(f4019,plain,
    ( $false
    | spl9_2
    | ~ spl9_5
    | spl9_7
    | ~ spl9_8
    | spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16 ),
    inference(unit_resulting_resolution,[],[f3628,f3624,f3620,f3616,f3600,f3608,f3612,f3604,f3584,f3596,f3592,f3573,f3502])).

fof(f3502,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X3)
      | r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | ~ r1_tsep_1(X3,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3412])).

fof(f3584,plain,
    ( r1_tsep_1(sK3,sK1)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f3583])).

fof(f3583,plain,
    ( spl9_5
  <=> r1_tsep_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f4016,plain,
    ( spl9_1
    | ~ spl9_4
    | spl9_7
    | ~ spl9_8
    | spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16 ),
    inference(avatar_contradiction_clause,[],[f4005])).

fof(f4005,plain,
    ( $false
    | spl9_1
    | ~ spl9_4
    | spl9_7
    | ~ spl9_8
    | spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16 ),
    inference(unit_resulting_resolution,[],[f3628,f3624,f3620,f3616,f3600,f3608,f3612,f3604,f3580,f3596,f3592,f3570,f3501])).

fof(f3501,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X3)
      | r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | ~ r1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3412])).

fof(f3570,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f3569])).

fof(f3569,plain,
    ( spl9_1
  <=> r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f3580,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f3579])).

fof(f3579,plain,
    ( spl9_4
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f4001,plain,
    ( spl9_1
    | ~ spl9_3
    | spl9_7
    | ~ spl9_8
    | spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16 ),
    inference(avatar_contradiction_clause,[],[f3990])).

fof(f3990,plain,
    ( $false
    | spl9_1
    | ~ spl9_3
    | spl9_7
    | ~ spl9_8
    | spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_12
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16 ),
    inference(unit_resulting_resolution,[],[f3628,f3624,f3620,f3616,f3600,f3608,f3612,f3604,f3577,f3596,f3592,f3570,f3500])).

fof(f3500,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X3)
      | r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | ~ r1_tsep_1(X1,X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3412])).

fof(f3577,plain,
    ( r1_tsep_1(sK1,sK3)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f3576])).

fof(f3576,plain,
    ( spl9_3
  <=> r1_tsep_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f3629,plain,(
    ~ spl9_16 ),
    inference(avatar_split_clause,[],[f3467,f3627])).

fof(f3467,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f3455])).

fof(f3455,plain,
    ( ( ( ~ r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
        & ( r1_tsep_1(sK3,sK2)
          | r1_tsep_1(sK3,sK1) ) )
      | ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)
        & ( r1_tsep_1(sK2,sK3)
          | r1_tsep_1(sK1,sK3) ) ) )
    & ~ r1_tsep_1(sK1,sK2)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f3394,f3454,f3453,f3452,f3451])).

fof(f3451,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
                        & ( r1_tsep_1(X3,X2)
                          | r1_tsep_1(X3,X1) ) )
                      | ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                        & ( r1_tsep_1(X2,X3)
                          | r1_tsep_1(X1,X3) ) ) )
                    & ~ r1_tsep_1(X1,X2)
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
                  ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(sK0,X1,X2))
                      & ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) ) )
                    | ( ~ r1_tsep_1(k2_tsep_1(sK0,X1,X2),X3)
                      & ( r1_tsep_1(X2,X3)
                        | r1_tsep_1(X1,X3) ) ) )
                  & ~ r1_tsep_1(X1,X2)
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

fof(f3452,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(sK0,X1,X2))
                    & ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X3,X1) ) )
                  | ( ~ r1_tsep_1(k2_tsep_1(sK0,X1,X2),X3)
                    & ( r1_tsep_1(X2,X3)
                      | r1_tsep_1(X1,X3) ) ) )
                & ~ r1_tsep_1(X1,X2)
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(sK0,sK1,X2))
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X3,sK1) ) )
                | ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,X2),X3)
                  & ( r1_tsep_1(X2,X3)
                    | r1_tsep_1(sK1,X3) ) ) )
              & ~ r1_tsep_1(sK1,X2)
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f3453,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(sK0,sK1,X2))
                & ( r1_tsep_1(X3,X2)
                  | r1_tsep_1(X3,sK1) ) )
              | ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,X2),X3)
                & ( r1_tsep_1(X2,X3)
                  | r1_tsep_1(sK1,X3) ) ) )
            & ~ r1_tsep_1(sK1,X2)
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(sK0,sK1,sK2))
              & ( r1_tsep_1(X3,sK2)
                | r1_tsep_1(X3,sK1) ) )
            | ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),X3)
              & ( r1_tsep_1(sK2,X3)
                | r1_tsep_1(sK1,X3) ) ) )
          & ~ r1_tsep_1(sK1,sK2)
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f3454,plain,
    ( ? [X3] :
        ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(sK0,sK1,sK2))
            & ( r1_tsep_1(X3,sK2)
              | r1_tsep_1(X3,sK1) ) )
          | ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),X3)
            & ( r1_tsep_1(sK2,X3)
              | r1_tsep_1(sK1,X3) ) ) )
        & ~ r1_tsep_1(sK1,sK2)
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ( ( ~ r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
          & ( r1_tsep_1(sK3,sK2)
            | r1_tsep_1(sK3,sK1) ) )
        | ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3)
          & ( r1_tsep_1(sK2,sK3)
            | r1_tsep_1(sK1,sK3) ) ) )
      & ~ r1_tsep_1(sK1,sK2)
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f3394,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
                      & ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) ) )
                    | ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                      & ( r1_tsep_1(X2,X3)
                        | r1_tsep_1(X1,X3) ) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3393])).

fof(f3393,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
                      & ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) ) )
                    | ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                      & ( r1_tsep_1(X2,X3)
                        | r1_tsep_1(X1,X3) ) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3383])).

fof(f3383,negated_conjecture,(
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
                   => ( ~ r1_tsep_1(X1,X2)
                     => ( ( ( r1_tsep_1(X3,X2)
                            | r1_tsep_1(X3,X1) )
                         => r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                        & ( ( r1_tsep_1(X2,X3)
                            | r1_tsep_1(X1,X3) )
                         => r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3382])).

fof(f3382,conjecture,(
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
                 => ( ~ r1_tsep_1(X1,X2)
                   => ( ( ( r1_tsep_1(X3,X2)
                          | r1_tsep_1(X3,X1) )
                       => r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                      & ( ( r1_tsep_1(X2,X3)
                          | r1_tsep_1(X1,X3) )
                       => r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_tmap_1)).

fof(f3625,plain,(
    spl9_15 ),
    inference(avatar_split_clause,[],[f3468,f3623])).

fof(f3468,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3455])).

fof(f3621,plain,(
    spl9_14 ),
    inference(avatar_split_clause,[],[f3469,f3619])).

fof(f3469,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3455])).

fof(f3617,plain,(
    ~ spl9_13 ),
    inference(avatar_split_clause,[],[f3470,f3615])).

fof(f3470,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f3455])).

fof(f3613,plain,(
    spl9_12 ),
    inference(avatar_split_clause,[],[f3471,f3611])).

fof(f3471,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f3455])).

fof(f3609,plain,(
    ~ spl9_11 ),
    inference(avatar_split_clause,[],[f3472,f3607])).

fof(f3472,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f3455])).

fof(f3605,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f3473,f3603])).

fof(f3473,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f3455])).

fof(f3601,plain,(
    ~ spl9_9 ),
    inference(avatar_split_clause,[],[f3474,f3599])).

fof(f3474,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f3455])).

fof(f3597,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f3475,f3595])).

fof(f3475,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f3455])).

fof(f3593,plain,(
    ~ spl9_7 ),
    inference(avatar_split_clause,[],[f3476,f3591])).

fof(f3476,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f3455])).

fof(f3589,plain,
    ( spl9_3
    | spl9_4
    | spl9_5
    | spl9_6 ),
    inference(avatar_split_clause,[],[f3477,f3586,f3583,f3579,f3576])).

fof(f3477,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK3,sK1)
    | r1_tsep_1(sK2,sK3)
    | r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f3455])).

fof(f3588,plain,
    ( ~ spl9_1
    | spl9_5
    | spl9_6 ),
    inference(avatar_split_clause,[],[f3478,f3586,f3583,f3569])).

fof(f3478,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK3,sK1)
    | ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f3455])).

fof(f3581,plain,
    ( spl9_3
    | spl9_4
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f3479,f3572,f3579,f3576])).

fof(f3479,plain,
    ( ~ r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
    | r1_tsep_1(sK2,sK3)
    | r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f3455])).

fof(f3574,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f3480,f3572,f3569])).

fof(f3480,plain,
    ( ~ r1_tsep_1(sK3,k2_tsep_1(sK0,sK1,sK2))
    | ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f3455])).
%------------------------------------------------------------------------------
