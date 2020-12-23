%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1721+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:30 EST 2020

% Result     : Theorem 2.45s
% Output     : Refutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 257 expanded)
%              Number of leaves         :   26 ( 134 expanded)
%              Depth                    :    7
%              Number of atoms          :  388 (2170 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6270,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3823,f3828,f3833,f3838,f3843,f3848,f3853,f3858,f3863,f3868,f3873,f3878,f3883,f3983,f4867,f5700,f5815,f6269])).

fof(f6269,plain,
    ( spl48_327
    | spl48_2
    | ~ spl48_3
    | ~ spl48_4
    | ~ spl48_5
    | spl48_6
    | ~ spl48_7
    | spl48_8
    | ~ spl48_9
    | spl48_10
    | ~ spl48_11
    | ~ spl48_12
    | spl48_13 ),
    inference(avatar_split_clause,[],[f6202,f3880,f3875,f3870,f3865,f3860,f3855,f3850,f3845,f3840,f3835,f3830,f3825,f5812])).

fof(f5812,plain,
    ( spl48_327
  <=> m1_pre_topc(k2_tsep_1(sK4,sK5,sK6),k2_tsep_1(sK4,sK7,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl48_327])])).

fof(f3825,plain,
    ( spl48_2
  <=> r1_tsep_1(sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl48_2])])).

fof(f3830,plain,
    ( spl48_3
  <=> m1_pre_topc(sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl48_3])])).

fof(f3835,plain,
    ( spl48_4
  <=> m1_pre_topc(sK5,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl48_4])])).

fof(f3840,plain,
    ( spl48_5
  <=> m1_pre_topc(sK7,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl48_5])])).

fof(f3845,plain,
    ( spl48_6
  <=> v2_struct_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl48_6])])).

fof(f3850,plain,
    ( spl48_7
  <=> m1_pre_topc(sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl48_7])])).

fof(f3855,plain,
    ( spl48_8
  <=> v2_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl48_8])])).

fof(f3860,plain,
    ( spl48_9
  <=> m1_pre_topc(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl48_9])])).

fof(f3865,plain,
    ( spl48_10
  <=> v2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl48_10])])).

fof(f3870,plain,
    ( spl48_11
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl48_11])])).

fof(f3875,plain,
    ( spl48_12
  <=> v2_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl48_12])])).

fof(f3880,plain,
    ( spl48_13
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl48_13])])).

fof(f6202,plain,
    ( m1_pre_topc(k2_tsep_1(sK4,sK5,sK6),k2_tsep_1(sK4,sK7,sK7))
    | spl48_2
    | ~ spl48_3
    | ~ spl48_4
    | ~ spl48_5
    | spl48_6
    | ~ spl48_7
    | spl48_8
    | ~ spl48_9
    | spl48_10
    | ~ spl48_11
    | ~ spl48_12
    | spl48_13 ),
    inference(unit_resulting_resolution,[],[f3882,f3877,f3872,f3867,f3847,f3857,f3847,f3862,f3852,f3842,f3842,f3837,f3832,f3827,f3614])).

fof(f3614,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X4)
      | ~ m1_pre_topc(X1,X3)
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3386])).

fof(f3386,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                      | r1_tsep_1(X1,X2)
                      | ~ m1_pre_topc(X2,X4)
                      | ~ m1_pre_topc(X1,X3)
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3385])).

fof(f3385,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                      | r1_tsep_1(X1,X2)
                      | ~ m1_pre_topc(X2,X4)
                      | ~ m1_pre_topc(X1,X3)
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3364])).

fof(f3364,axiom,(
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
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X2,X4)
                          & m1_pre_topc(X1,X3) )
                       => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                          | r1_tsep_1(X1,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tmap_1)).

fof(f3827,plain,
    ( ~ r1_tsep_1(sK5,sK6)
    | spl48_2 ),
    inference(avatar_component_clause,[],[f3825])).

fof(f3832,plain,
    ( m1_pre_topc(sK6,sK7)
    | ~ spl48_3 ),
    inference(avatar_component_clause,[],[f3830])).

fof(f3837,plain,
    ( m1_pre_topc(sK5,sK7)
    | ~ spl48_4 ),
    inference(avatar_component_clause,[],[f3835])).

fof(f3842,plain,
    ( m1_pre_topc(sK7,sK4)
    | ~ spl48_5 ),
    inference(avatar_component_clause,[],[f3840])).

fof(f3852,plain,
    ( m1_pre_topc(sK6,sK4)
    | ~ spl48_7 ),
    inference(avatar_component_clause,[],[f3850])).

fof(f3862,plain,
    ( m1_pre_topc(sK5,sK4)
    | ~ spl48_9 ),
    inference(avatar_component_clause,[],[f3860])).

fof(f3857,plain,
    ( ~ v2_struct_0(sK6)
    | spl48_8 ),
    inference(avatar_component_clause,[],[f3855])).

fof(f3847,plain,
    ( ~ v2_struct_0(sK7)
    | spl48_6 ),
    inference(avatar_component_clause,[],[f3845])).

fof(f3867,plain,
    ( ~ v2_struct_0(sK5)
    | spl48_10 ),
    inference(avatar_component_clause,[],[f3865])).

fof(f3872,plain,
    ( l1_pre_topc(sK4)
    | ~ spl48_11 ),
    inference(avatar_component_clause,[],[f3870])).

fof(f3877,plain,
    ( v2_pre_topc(sK4)
    | ~ spl48_12 ),
    inference(avatar_component_clause,[],[f3875])).

fof(f3882,plain,
    ( ~ v2_struct_0(sK4)
    | spl48_13 ),
    inference(avatar_component_clause,[],[f3880])).

fof(f5815,plain,
    ( ~ spl48_327
    | spl48_174
    | ~ spl48_307 ),
    inference(avatar_split_clause,[],[f5799,f5697,f4863,f5812])).

fof(f4863,plain,
    ( spl48_174
  <=> m1_pre_topc(k2_tsep_1(sK4,sK5,sK6),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl48_174])])).

fof(f5697,plain,
    ( spl48_307
  <=> g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = k2_tsep_1(sK4,sK7,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl48_307])])).

fof(f5799,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK4,sK5,sK6),k2_tsep_1(sK4,sK7,sK7))
    | spl48_174
    | ~ spl48_307 ),
    inference(backward_demodulation,[],[f4865,f5699])).

fof(f5699,plain,
    ( g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = k2_tsep_1(sK4,sK7,sK7)
    | ~ spl48_307 ),
    inference(avatar_component_clause,[],[f5697])).

fof(f4865,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK4,sK5,sK6),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | spl48_174 ),
    inference(avatar_component_clause,[],[f4863])).

fof(f5700,plain,
    ( spl48_307
    | ~ spl48_5
    | spl48_6
    | ~ spl48_11
    | ~ spl48_12
    | spl48_13 ),
    inference(avatar_split_clause,[],[f5689,f3880,f3875,f3870,f3845,f3840,f5697])).

fof(f5689,plain,
    ( g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)) = k2_tsep_1(sK4,sK7,sK7)
    | ~ spl48_5
    | spl48_6
    | ~ spl48_11
    | ~ spl48_12
    | spl48_13 ),
    inference(unit_resulting_resolution,[],[f3882,f3877,f3872,f3847,f3842,f3623])).

fof(f3623,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X1)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3392])).

fof(f3392,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3391])).

fof(f3391,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3362])).

fof(f3362,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tmap_1)).

fof(f4867,plain,
    ( ~ spl48_29
    | ~ spl48_174
    | spl48_1 ),
    inference(avatar_split_clause,[],[f4861,f3820,f4863,f3980])).

fof(f3980,plain,
    ( spl48_29
  <=> l1_pre_topc(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl48_29])])).

fof(f3820,plain,
    ( spl48_1
  <=> m1_pre_topc(k2_tsep_1(sK4,sK5,sK6),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl48_1])])).

fof(f4861,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK4,sK5,sK6),g1_pre_topc(u1_struct_0(sK7),u1_pre_topc(sK7)))
    | ~ l1_pre_topc(sK7)
    | spl48_1 ),
    inference(resolution,[],[f3663,f3822])).

fof(f3822,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK4,sK5,sK6),sK7)
    | spl48_1 ),
    inference(avatar_component_clause,[],[f3820])).

fof(f3663,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3425])).

fof(f3425,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1850])).

fof(f1850,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f3983,plain,
    ( spl48_29
    | ~ spl48_5
    | ~ spl48_11 ),
    inference(avatar_split_clause,[],[f3978,f3870,f3840,f3980])).

fof(f3978,plain,
    ( l1_pre_topc(sK7)
    | ~ spl48_5
    | ~ spl48_11 ),
    inference(unit_resulting_resolution,[],[f3872,f3842,f3690])).

fof(f3690,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3448])).

fof(f3448,plain,(
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

fof(f3883,plain,(
    ~ spl48_13 ),
    inference(avatar_split_clause,[],[f3598,f3880])).

fof(f3598,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f3517])).

fof(f3517,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK4,sK5,sK6),sK7)
    & ~ r1_tsep_1(sK5,sK6)
    & m1_pre_topc(sK6,sK7)
    & m1_pre_topc(sK5,sK7)
    & m1_pre_topc(sK7,sK4)
    & ~ v2_struct_0(sK7)
    & m1_pre_topc(sK6,sK4)
    & ~ v2_struct_0(sK6)
    & m1_pre_topc(sK5,sK4)
    & ~ v2_struct_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f3382,f3516,f3515,f3514,f3513])).

fof(f3513,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                    & ~ r1_tsep_1(X1,X2)
                    & m1_pre_topc(X2,X3)
                    & m1_pre_topc(X1,X3)
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
                  ( ~ m1_pre_topc(k2_tsep_1(sK4,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,sK4)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK4)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK4)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f3514,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_pre_topc(k2_tsep_1(sK4,X1,X2),X3)
                & ~ r1_tsep_1(X1,X2)
                & m1_pre_topc(X2,X3)
                & m1_pre_topc(X1,X3)
                & m1_pre_topc(X3,sK4)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK4)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK4)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_pre_topc(k2_tsep_1(sK4,sK5,X2),X3)
              & ~ r1_tsep_1(sK5,X2)
              & m1_pre_topc(X2,X3)
              & m1_pre_topc(sK5,X3)
              & m1_pre_topc(X3,sK4)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK4)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK5,sK4)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f3515,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ m1_pre_topc(k2_tsep_1(sK4,sK5,X2),X3)
            & ~ r1_tsep_1(sK5,X2)
            & m1_pre_topc(X2,X3)
            & m1_pre_topc(sK5,X3)
            & m1_pre_topc(X3,sK4)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK4)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ~ m1_pre_topc(k2_tsep_1(sK4,sK5,sK6),X3)
          & ~ r1_tsep_1(sK5,sK6)
          & m1_pre_topc(sK6,X3)
          & m1_pre_topc(sK5,X3)
          & m1_pre_topc(X3,sK4)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK6,sK4)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f3516,plain,
    ( ? [X3] :
        ( ~ m1_pre_topc(k2_tsep_1(sK4,sK5,sK6),X3)
        & ~ r1_tsep_1(sK5,sK6)
        & m1_pre_topc(sK6,X3)
        & m1_pre_topc(sK5,X3)
        & m1_pre_topc(X3,sK4)
        & ~ v2_struct_0(X3) )
   => ( ~ m1_pre_topc(k2_tsep_1(sK4,sK5,sK6),sK7)
      & ~ r1_tsep_1(sK5,sK6)
      & m1_pre_topc(sK6,sK7)
      & m1_pre_topc(sK5,sK7)
      & m1_pre_topc(sK7,sK4)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f3382,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3381])).

fof(f3381,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3368])).

fof(f3368,negated_conjecture,(
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
                   => ( ( m1_pre_topc(X2,X3)
                        & m1_pre_topc(X1,X3) )
                     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                        | r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3367])).

fof(f3367,conjecture,(
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
                 => ( ( m1_pre_topc(X2,X3)
                      & m1_pre_topc(X1,X3) )
                   => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                      | r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tmap_1)).

fof(f3878,plain,(
    spl48_12 ),
    inference(avatar_split_clause,[],[f3599,f3875])).

fof(f3599,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f3517])).

fof(f3873,plain,(
    spl48_11 ),
    inference(avatar_split_clause,[],[f3600,f3870])).

fof(f3600,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f3517])).

fof(f3868,plain,(
    ~ spl48_10 ),
    inference(avatar_split_clause,[],[f3601,f3865])).

fof(f3601,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f3517])).

fof(f3863,plain,(
    spl48_9 ),
    inference(avatar_split_clause,[],[f3602,f3860])).

fof(f3602,plain,(
    m1_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f3517])).

fof(f3858,plain,(
    ~ spl48_8 ),
    inference(avatar_split_clause,[],[f3603,f3855])).

fof(f3603,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f3517])).

fof(f3853,plain,(
    spl48_7 ),
    inference(avatar_split_clause,[],[f3604,f3850])).

fof(f3604,plain,(
    m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f3517])).

fof(f3848,plain,(
    ~ spl48_6 ),
    inference(avatar_split_clause,[],[f3605,f3845])).

fof(f3605,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f3517])).

fof(f3843,plain,(
    spl48_5 ),
    inference(avatar_split_clause,[],[f3606,f3840])).

fof(f3606,plain,(
    m1_pre_topc(sK7,sK4) ),
    inference(cnf_transformation,[],[f3517])).

fof(f3838,plain,(
    spl48_4 ),
    inference(avatar_split_clause,[],[f3607,f3835])).

fof(f3607,plain,(
    m1_pre_topc(sK5,sK7) ),
    inference(cnf_transformation,[],[f3517])).

fof(f3833,plain,(
    spl48_3 ),
    inference(avatar_split_clause,[],[f3608,f3830])).

fof(f3608,plain,(
    m1_pre_topc(sK6,sK7) ),
    inference(cnf_transformation,[],[f3517])).

fof(f3828,plain,(
    ~ spl48_2 ),
    inference(avatar_split_clause,[],[f3609,f3825])).

fof(f3609,plain,(
    ~ r1_tsep_1(sK5,sK6) ),
    inference(cnf_transformation,[],[f3517])).

fof(f3823,plain,(
    ~ spl48_1 ),
    inference(avatar_split_clause,[],[f3610,f3820])).

fof(f3610,plain,(
    ~ m1_pre_topc(k2_tsep_1(sK4,sK5,sK6),sK7) ),
    inference(cnf_transformation,[],[f3517])).
%------------------------------------------------------------------------------
