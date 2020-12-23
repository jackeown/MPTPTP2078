%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1884+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:50 EST 2020

% Result     : Theorem 2.73s
% Output     : Refutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :  430 (2300 expanded)
%              Number of leaves         :   62 ( 747 expanded)
%              Depth                    :   23
%              Number of atoms          : 2019 (27350 expanded)
%              Number of equality atoms :  201 (3004 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4809,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f130,f135,f140,f145,f150,f154,f208,f214,f220,f240,f256,f264,f297,f301,f305,f372,f452,f476,f481,f486,f491,f512,f712,f722,f731,f1246,f1254,f1278,f1281,f1440,f1524,f1544,f1589,f1994,f2020,f2032,f2034,f2159,f2238,f2580,f2609,f3736,f4278,f4385,f4657,f4808])).

fof(f4808,plain,
    ( spl8_3
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_66
    | ~ spl8_92
    | ~ spl8_106
    | ~ spl8_117
    | ~ spl8_149
    | ~ spl8_165 ),
    inference(avatar_contradiction_clause,[],[f4807])).

fof(f4807,plain,
    ( $false
    | spl8_3
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_66
    | ~ spl8_92
    | ~ spl8_106
    | ~ spl8_117
    | ~ spl8_149
    | ~ spl8_165 ),
    inference(subsumption_resolution,[],[f4806,f1716])).

fof(f1716,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK5(sK0,u1_struct_0(sK1))
    | ~ spl8_20
    | ~ spl8_66
    | ~ spl8_106 ),
    inference(backward_demodulation,[],[f883,f1713])).

fof(f1713,plain,
    ( u1_pre_topc(sK1) = u1_pre_topc(sK5(sK0,u1_struct_0(sK1)))
    | ~ spl8_20
    | ~ spl8_66
    | ~ spl8_106 ),
    inference(trivial_inequality_removal,[],[f1712])).

fof(f1712,plain,
    ( sK5(sK0,u1_struct_0(sK1)) != sK5(sK0,u1_struct_0(sK1))
    | u1_pre_topc(sK1) = u1_pre_topc(sK5(sK0,u1_struct_0(sK1)))
    | ~ spl8_20
    | ~ spl8_66
    | ~ spl8_106 ),
    inference(superposition,[],[f1277,f883])).

fof(f1277,plain,
    ( ! [X4,X5] :
        ( sK5(sK0,u1_struct_0(sK1)) != g1_pre_topc(X4,X5)
        | u1_pre_topc(sK1) = X5 )
    | ~ spl8_106 ),
    inference(avatar_component_clause,[],[f1276])).

fof(f1276,plain,
    ( spl8_106
  <=> ! [X5,X4] :
        ( sK5(sK0,u1_struct_0(sK1)) != g1_pre_topc(X4,X5)
        | u1_pre_topc(sK1) = X5 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_106])])).

fof(f883,plain,
    ( sK5(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK5(sK0,u1_struct_0(sK1))))
    | ~ spl8_20
    | ~ spl8_66 ),
    inference(forward_demodulation,[],[f721,f263])).

fof(f263,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK5(sK0,u1_struct_0(sK1)))
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl8_20
  <=> u1_struct_0(sK1) = u1_struct_0(sK5(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f721,plain,
    ( sK5(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK5(sK0,u1_struct_0(sK1))),u1_pre_topc(sK5(sK0,u1_struct_0(sK1))))
    | ~ spl8_66 ),
    inference(avatar_component_clause,[],[f719])).

fof(f719,plain,
    ( spl8_66
  <=> sK5(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK5(sK0,u1_struct_0(sK1))),u1_pre_topc(sK5(sK0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_66])])).

fof(f4806,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != sK5(sK0,u1_struct_0(sK1))
    | spl8_3
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_66
    | ~ spl8_92
    | ~ spl8_106
    | ~ spl8_117
    | ~ spl8_149
    | ~ spl8_165 ),
    inference(forward_demodulation,[],[f4607,f4668])).

fof(f4668,plain,
    ( u1_pre_topc(sK1) = u1_pre_topc(sK2)
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_66
    | ~ spl8_92
    | ~ spl8_117
    | ~ spl8_165 ),
    inference(forward_demodulation,[],[f2996,f1270])).

fof(f1270,plain,
    ( u1_pre_topc(sK1) = u1_pre_topc(sK5(sK0,u1_struct_0(sK1)))
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_66
    | ~ spl8_92 ),
    inference(trivial_inequality_removal,[],[f1269])).

fof(f1269,plain,
    ( sK5(sK0,u1_struct_0(sK1)) != sK5(sK0,u1_struct_0(sK1))
    | u1_pre_topc(sK1) = u1_pre_topc(sK5(sK0,u1_struct_0(sK1)))
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_66
    | ~ spl8_92 ),
    inference(superposition,[],[f893,f1051])).

fof(f1051,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK5(sK0,u1_struct_0(sK1))
    | ~ spl8_92 ),
    inference(avatar_component_clause,[],[f1049])).

fof(f1049,plain,
    ( spl8_92
  <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK5(sK0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_92])])).

fof(f893,plain,
    ( ! [X6,X7] :
        ( sK5(sK0,u1_struct_0(sK1)) != g1_pre_topc(X6,X7)
        | u1_pre_topc(sK5(sK0,u1_struct_0(sK1))) = X7 )
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_66 ),
    inference(subsumption_resolution,[],[f891,f755])).

fof(f755,plain,
    ( m1_subset_1(u1_pre_topc(sK5(sK0,u1_struct_0(sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl8_19
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f732,f729])).

fof(f729,plain,
    ( l1_pre_topc(sK5(sK0,u1_struct_0(sK1)))
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f725,f71])).

fof(f71,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ( ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
        & m1_pre_topc(sK1,sK2)
        & m1_pre_topc(sK2,sK0)
        & v1_tdlat_3(sK2)
        & ~ v2_struct_0(sK2) )
      | ~ v1_tdlat_3(sK1)
      | ~ v4_tex_2(sK1,sK0) )
    & ( ( ! [X3] :
            ( g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
            | ~ m1_pre_topc(sK1,X3)
            | ~ m1_pre_topc(X3,sK0)
            | ~ v1_tdlat_3(X3)
            | v2_struct_0(X3) )
        & v1_tdlat_3(sK1) )
      | v4_tex_2(sK1,sK0) )
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f47,f50,f49,f48])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X2,X0)
                  & v1_tdlat_3(X2)
                  & ~ v2_struct_0(X2) )
              | ~ v1_tdlat_3(X1)
              | ~ v4_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                    | ~ m1_pre_topc(X1,X3)
                    | ~ m1_pre_topc(X3,X0)
                    | ~ v1_tdlat_3(X3)
                    | v2_struct_0(X3) )
                & v1_tdlat_3(X1) )
              | v4_tex_2(X1,X0) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,sK0)
                & v1_tdlat_3(X2)
                & ~ v2_struct_0(X2) )
            | ~ v1_tdlat_3(X1)
            | ~ v4_tex_2(X1,sK0) )
          & ( ( ! [X3] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | ~ m1_pre_topc(X1,X3)
                  | ~ m1_pre_topc(X3,sK0)
                  | ~ v1_tdlat_3(X3)
                  | v2_struct_0(X3) )
              & v1_tdlat_3(X1) )
            | v4_tex_2(X1,sK0) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,sK0)
              & v1_tdlat_3(X2)
              & ~ v2_struct_0(X2) )
          | ~ v1_tdlat_3(X1)
          | ~ v4_tex_2(X1,sK0) )
        & ( ( ! [X3] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                | ~ m1_pre_topc(X1,X3)
                | ~ m1_pre_topc(X3,sK0)
                | ~ v1_tdlat_3(X3)
                | v2_struct_0(X3) )
            & v1_tdlat_3(X1) )
          | v4_tex_2(X1,sK0) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ( ? [X2] :
            ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
            & m1_pre_topc(sK1,X2)
            & m1_pre_topc(X2,sK0)
            & v1_tdlat_3(X2)
            & ~ v2_struct_0(X2) )
        | ~ v1_tdlat_3(sK1)
        | ~ v4_tex_2(sK1,sK0) )
      & ( ( ! [X3] :
              ( g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
              | ~ m1_pre_topc(sK1,X3)
              | ~ m1_pre_topc(X3,sK0)
              | ~ v1_tdlat_3(X3)
              | v2_struct_0(X3) )
          & v1_tdlat_3(sK1) )
        | v4_tex_2(sK1,sK0) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X2] :
        ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        & m1_pre_topc(sK1,X2)
        & m1_pre_topc(X2,sK0)
        & v1_tdlat_3(X2)
        & ~ v2_struct_0(X2) )
   => ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
      & m1_pre_topc(sK1,sK2)
      & m1_pre_topc(sK2,sK0)
      & v1_tdlat_3(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & v1_tdlat_3(X2)
                & ~ v2_struct_0(X2) )
            | ~ v1_tdlat_3(X1)
            | ~ v4_tex_2(X1,X0) )
          & ( ( ! [X3] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | ~ m1_pre_topc(X1,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_tdlat_3(X3)
                  | v2_struct_0(X3) )
              & v1_tdlat_3(X1) )
            | v4_tex_2(X1,X0) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & v1_tdlat_3(X2)
                & ~ v2_struct_0(X2) )
            | ~ v1_tdlat_3(X1)
            | ~ v4_tex_2(X1,X0) )
          & ( ( ! [X2] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X2,X0)
                  | ~ v1_tdlat_3(X2)
                  | v2_struct_0(X2) )
              & v1_tdlat_3(X1) )
            | v4_tex_2(X1,X0) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & v1_tdlat_3(X2)
                & ~ v2_struct_0(X2) )
            | ~ v1_tdlat_3(X1)
            | ~ v4_tex_2(X1,X0) )
          & ( ( ! [X2] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X2,X0)
                  | ~ v1_tdlat_3(X2)
                  | v2_struct_0(X2) )
              & v1_tdlat_3(X1) )
            | v4_tex_2(X1,X0) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_tex_2(X1,X0)
          <~> ( ! [X2] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X2,X0)
                  | ~ v1_tdlat_3(X2)
                  | v2_struct_0(X2) )
              & v1_tdlat_3(X1) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_tex_2(X1,X0)
          <~> ( ! [X2] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X2,X0)
                  | ~ v1_tdlat_3(X2)
                  | v2_struct_0(X2) )
              & v1_tdlat_3(X1) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( v4_tex_2(X1,X0)
            <=> ( ! [X2] :
                    ( ( m1_pre_topc(X2,X0)
                      & v1_tdlat_3(X2)
                      & ~ v2_struct_0(X2) )
                   => ( m1_pre_topc(X1,X2)
                     => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) )
                & v1_tdlat_3(X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( v4_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & ~ v2_struct_0(X2) )
                 => ( m1_pre_topc(X1,X2)
                   => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) )
              & v1_tdlat_3(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tex_2)).

fof(f725,plain,
    ( l1_pre_topc(sK5(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl8_19 ),
    inference(resolution,[],[f255,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f255,plain,
    ( m1_pre_topc(sK5(sK0,u1_struct_0(sK1)),sK0)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f253])).

fof(f253,plain,
    ( spl8_19
  <=> m1_pre_topc(sK5(sK0,u1_struct_0(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f732,plain,
    ( m1_subset_1(u1_pre_topc(sK5(sK0,u1_struct_0(sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK5(sK0,u1_struct_0(sK1)))
    | ~ spl8_20 ),
    inference(superposition,[],[f82,f263])).

fof(f82,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f891,plain,
    ( ! [X6,X7] :
        ( sK5(sK0,u1_struct_0(sK1)) != g1_pre_topc(X6,X7)
        | u1_pre_topc(sK5(sK0,u1_struct_0(sK1))) = X7
        | ~ m1_subset_1(u1_pre_topc(sK5(sK0,u1_struct_0(sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
    | ~ spl8_20
    | ~ spl8_66 ),
    inference(superposition,[],[f109,f883])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f2996,plain,
    ( u1_pre_topc(sK2) = u1_pre_topc(sK5(sK0,u1_struct_0(sK1)))
    | ~ spl8_117
    | ~ spl8_165 ),
    inference(trivial_inequality_removal,[],[f2995])).

fof(f2995,plain,
    ( sK5(sK0,u1_struct_0(sK1)) != sK5(sK0,u1_struct_0(sK1))
    | u1_pre_topc(sK2) = u1_pre_topc(sK5(sK0,u1_struct_0(sK1)))
    | ~ spl8_117
    | ~ spl8_165 ),
    inference(superposition,[],[f1543,f2311])).

fof(f2311,plain,
    ( sK5(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
    | ~ spl8_165 ),
    inference(avatar_component_clause,[],[f2309])).

fof(f2309,plain,
    ( spl8_165
  <=> sK5(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_165])])).

fof(f1543,plain,
    ( ! [X6,X7] :
        ( sK5(sK0,u1_struct_0(sK1)) != g1_pre_topc(X6,X7)
        | u1_pre_topc(sK5(sK0,u1_struct_0(sK1))) = X7 )
    | ~ spl8_117 ),
    inference(avatar_component_clause,[],[f1542])).

fof(f1542,plain,
    ( spl8_117
  <=> ! [X7,X6] :
        ( sK5(sK0,u1_struct_0(sK1)) != g1_pre_topc(X6,X7)
        | u1_pre_topc(sK5(sK0,u1_struct_0(sK1))) = X7 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_117])])).

fof(f4607,plain,
    ( sK5(sK0,u1_struct_0(sK1)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
    | spl8_3
    | ~ spl8_20
    | ~ spl8_66
    | ~ spl8_106
    | ~ spl8_149 ),
    inference(backward_demodulation,[],[f2517,f1716])).

fof(f2517,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
    | spl8_3
    | ~ spl8_149 ),
    inference(backward_demodulation,[],[f129,f2143])).

fof(f2143,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl8_149 ),
    inference(avatar_component_clause,[],[f2141])).

fof(f2141,plain,
    ( spl8_149
  <=> u1_struct_0(sK1) = u1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_149])])).

fof(f129,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | spl8_3 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl8_3
  <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f4657,plain,
    ( ~ spl8_5
    | ~ spl8_19
    | ~ spl8_164 ),
    inference(avatar_contradiction_clause,[],[f4656])).

fof(f4656,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_19
    | ~ spl8_164 ),
    inference(subsumption_resolution,[],[f4655,f139])).

fof(f139,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl8_5
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f4655,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ spl8_19
    | ~ spl8_164 ),
    inference(subsumption_resolution,[],[f4653,f71])).

fof(f4653,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ spl8_19
    | ~ spl8_164 ),
    inference(resolution,[],[f2307,f255])).

fof(f2307,plain,
    ( ! [X27] :
        ( ~ m1_pre_topc(sK5(sK0,u1_struct_0(sK1)),X27)
        | ~ l1_pre_topc(X27)
        | ~ m1_pre_topc(sK2,X27) )
    | ~ spl8_164 ),
    inference(avatar_component_clause,[],[f2306])).

fof(f2306,plain,
    ( spl8_164
  <=> ! [X27] :
        ( ~ m1_pre_topc(sK2,X27)
        | ~ l1_pre_topc(X27)
        | ~ m1_pre_topc(sK5(sK0,u1_struct_0(sK1)),X27) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_164])])).

fof(f4385,plain,
    ( ~ spl8_15
    | ~ spl8_149
    | spl8_156 ),
    inference(avatar_contradiction_clause,[],[f4384])).

fof(f4384,plain,
    ( $false
    | ~ spl8_15
    | ~ spl8_149
    | spl8_156 ),
    inference(subsumption_resolution,[],[f4339,f227])).

fof(f227,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl8_15
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f4339,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl8_149
    | spl8_156 ),
    inference(backward_demodulation,[],[f2183,f2143])).

fof(f2183,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | spl8_156 ),
    inference(avatar_component_clause,[],[f2182])).

fof(f2182,plain,
    ( spl8_156
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_156])])).

fof(f4278,plain,
    ( ~ spl8_10
    | ~ spl8_139
    | spl8_149
    | ~ spl8_152 ),
    inference(avatar_contradiction_clause,[],[f4277])).

fof(f4277,plain,
    ( $false
    | ~ spl8_10
    | ~ spl8_139
    | spl8_149
    | ~ spl8_152 ),
    inference(subsumption_resolution,[],[f4276,f2142])).

fof(f2142,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK2)
    | spl8_149 ),
    inference(avatar_component_clause,[],[f2141])).

fof(f4276,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl8_10
    | ~ spl8_139
    | ~ spl8_152 ),
    inference(subsumption_resolution,[],[f4275,f195])).

fof(f195,plain,
    ( v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl8_10
  <=> v3_tex_2(u1_struct_0(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f4275,plain,
    ( ~ v3_tex_2(u1_struct_0(sK1),sK0)
    | u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl8_139
    | ~ spl8_152 ),
    inference(subsumption_resolution,[],[f4270,f2050])).

fof(f2050,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl8_139 ),
    inference(resolution,[],[f2017,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f2017,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl8_139 ),
    inference(avatar_component_clause,[],[f2015])).

fof(f2015,plain,
    ( spl8_139
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_139])])).

fof(f4270,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v3_tex_2(u1_struct_0(sK1),sK0)
    | u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl8_152 ),
    inference(resolution,[],[f2158,f161])).

fof(f161,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f157,f71])).

fof(f157,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f73,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f73,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f2158,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ v3_tex_2(X0,sK0)
        | u1_struct_0(sK2) = X0 )
    | ~ spl8_152 ),
    inference(avatar_component_clause,[],[f2157])).

fof(f2157,plain,
    ( spl8_152
  <=> ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_tex_2(X0,sK0)
        | u1_struct_0(sK2) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_152])])).

fof(f3736,plain,
    ( spl8_3
    | ~ spl8_5
    | ~ spl8_15
    | ~ spl8_149
    | ~ spl8_156 ),
    inference(avatar_contradiction_clause,[],[f3735])).

fof(f3735,plain,
    ( $false
    | spl8_3
    | ~ spl8_5
    | ~ spl8_15
    | ~ spl8_149
    | ~ spl8_156 ),
    inference(subsumption_resolution,[],[f3734,f71])).

fof(f3734,plain,
    ( ~ l1_pre_topc(sK0)
    | spl8_3
    | ~ spl8_5
    | ~ spl8_15
    | ~ spl8_149
    | ~ spl8_156 ),
    inference(subsumption_resolution,[],[f3729,f73])).

fof(f3729,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | spl8_3
    | ~ spl8_5
    | ~ spl8_15
    | ~ spl8_149
    | ~ spl8_156 ),
    inference(resolution,[],[f3728,f139])).

fof(f3728,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | spl8_3
    | ~ spl8_15
    | ~ spl8_149
    | ~ spl8_156 ),
    inference(subsumption_resolution,[],[f3717,f2245])).

fof(f2245,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
    | spl8_3
    | ~ spl8_15
    | ~ spl8_156 ),
    inference(backward_demodulation,[],[f129,f2239])).

fof(f2239,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl8_15
    | ~ spl8_156 ),
    inference(resolution,[],[f2184,f1590])).

fof(f1590,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | u1_struct_0(sK1) = X0 )
    | ~ spl8_15 ),
    inference(resolution,[],[f227,f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f2184,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl8_156 ),
    inference(avatar_component_clause,[],[f2182])).

fof(f3717,plain,
    ( ! [X0] :
        ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
        | ~ m1_pre_topc(sK1,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl8_149 ),
    inference(equality_resolution,[],[f2533])).

fof(f2533,plain,
    ( ! [X0,X1] :
        ( u1_struct_0(X0) != u1_struct_0(sK1)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK2,X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl8_149 ),
    inference(superposition,[],[f86,f2143])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(X1) != u1_struct_0(X2)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              | u1_struct_0(X1) != u1_struct_0(X2)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              | u1_struct_0(X1) != u1_struct_0(X2)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( u1_struct_0(X1) = u1_struct_0(X2)
               => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tsep_1)).

fof(f2609,plain,
    ( ~ spl8_42
    | spl8_43
    | ~ spl8_33 ),
    inference(avatar_split_clause,[],[f2608,f378,f498,f494])).

fof(f494,plain,
    ( spl8_42
  <=> l1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f498,plain,
    ( spl8_43
  <=> sK5(sK0,sK3(sK0,u1_struct_0(sK1))) = g1_pre_topc(u1_struct_0(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))),u1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).

fof(f378,plain,
    ( spl8_33
  <=> v1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f2608,plain,
    ( sK5(sK0,sK3(sK0,u1_struct_0(sK1))) = g1_pre_topc(u1_struct_0(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))),u1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))))
    | ~ l1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ spl8_33 ),
    inference(resolution,[],[f380,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f380,plain,
    ( v1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f378])).

fof(f2580,plain,
    ( spl8_164
    | spl8_165
    | ~ spl8_20
    | ~ spl8_66
    | ~ spl8_149 ),
    inference(avatar_split_clause,[],[f2559,f2141,f719,f261,f2309,f2306])).

fof(f2559,plain,
    ( ! [X27] :
        ( sK5(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
        | ~ m1_pre_topc(sK2,X27)
        | ~ m1_pre_topc(sK5(sK0,u1_struct_0(sK1)),X27)
        | ~ l1_pre_topc(X27) )
    | ~ spl8_20
    | ~ spl8_66
    | ~ spl8_149 ),
    inference(trivial_inequality_removal,[],[f2555])).

fof(f2555,plain,
    ( ! [X27] :
        ( u1_struct_0(sK1) != u1_struct_0(sK1)
        | sK5(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
        | ~ m1_pre_topc(sK2,X27)
        | ~ m1_pre_topc(sK5(sK0,u1_struct_0(sK1)),X27)
        | ~ l1_pre_topc(X27) )
    | ~ spl8_20
    | ~ spl8_66
    | ~ spl8_149 ),
    inference(superposition,[],[f1231,f2143])).

fof(f1231,plain,
    ( ! [X0,X1] :
        ( u1_struct_0(X0) != u1_struct_0(sK1)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = sK5(sK0,u1_struct_0(sK1))
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK5(sK0,u1_struct_0(sK1)),X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl8_20
    | ~ spl8_66 ),
    inference(forward_demodulation,[],[f733,f883])).

fof(f733,plain,
    ( ! [X0,X1] :
        ( u1_struct_0(X0) != u1_struct_0(sK1)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK5(sK0,u1_struct_0(sK1))))
        | ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(sK5(sK0,u1_struct_0(sK1)),X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl8_20 ),
    inference(superposition,[],[f86,f263])).

fof(f2238,plain,
    ( ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | spl8_151 ),
    inference(avatar_contradiction_clause,[],[f2237])).

fof(f2237,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7
    | spl8_151 ),
    inference(subsumption_resolution,[],[f2152,f2123])).

fof(f2123,plain,
    ( v2_tex_2(u1_struct_0(sK2),sK0)
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7 ),
    inference(subsumption_resolution,[],[f2122,f69])).

fof(f69,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f2122,plain,
    ( v2_tex_2(u1_struct_0(sK2),sK0)
    | v2_struct_0(sK0)
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7 ),
    inference(subsumption_resolution,[],[f2121,f71])).

fof(f2121,plain,
    ( v2_tex_2(u1_struct_0(sK2),sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_5
    | ~ spl8_6
    | spl8_7 ),
    inference(subsumption_resolution,[],[f2120,f149])).

fof(f149,plain,
    ( ~ v2_struct_0(sK2)
    | spl8_7 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl8_7
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f2120,plain,
    ( v2_tex_2(u1_struct_0(sK2),sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f2119,f139])).

fof(f2119,plain,
    ( v2_tex_2(u1_struct_0(sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_5
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f2103,f144])).

fof(f144,plain,
    ( v1_tdlat_3(sK2)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl8_6
  <=> v1_tdlat_3(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f2103,plain,
    ( ~ v1_tdlat_3(sK2)
    | v2_tex_2(u1_struct_0(sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_5 ),
    inference(resolution,[],[f2029,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_tex_2(X2,X0)
                  | ~ v1_tdlat_3(X1) )
                & ( v1_tdlat_3(X1)
                  | ~ v2_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tex_2)).

fof(f2029,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f2025,f71])).

fof(f2025,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl8_5 ),
    inference(resolution,[],[f139,f85])).

fof(f2152,plain,
    ( ~ v2_tex_2(u1_struct_0(sK2),sK0)
    | spl8_151 ),
    inference(avatar_component_clause,[],[f2151])).

fof(f2151,plain,
    ( spl8_151
  <=> v2_tex_2(u1_struct_0(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_151])])).

fof(f2159,plain,
    ( ~ spl8_151
    | spl8_152
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f2155,f137,f2157,f2151])).

fof(f2155,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ v2_tex_2(u1_struct_0(sK2),sK0)
        | u1_struct_0(sK2) = X0
        | ~ v3_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f2108,f71])).

fof(f2108,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,u1_struct_0(sK2))
        | ~ v2_tex_2(u1_struct_0(sK2),sK0)
        | u1_struct_0(sK2) = X0
        | ~ v3_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl8_5 ),
    inference(resolution,[],[f2029,f88])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X3)
      | ~ v2_tex_2(X3,X0)
      | X1 = X3
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK3(X0,X1) != X1
                & r1_tarski(X1,sK3(X0,X1))
                & v2_tex_2(sK3(X0,X1),X0)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f54,f55])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK3(X0,X1) != X1
        & r1_tarski(X1,sK3(X0,X1))
        & v2_tex_2(sK3(X0,X1),X0)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
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
    inference(rectify,[],[f53])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

fof(f2034,plain,
    ( ~ spl8_137
    | spl8_139
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f2022,f132,f2015,f2007])).

fof(f2007,plain,
    ( spl8_137
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_137])])).

fof(f132,plain,
    ( spl8_4
  <=> m1_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f2022,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ spl8_4 ),
    inference(resolution,[],[f134,f85])).

fof(f134,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f132])).

fof(f2032,plain,
    ( ~ spl8_5
    | spl8_137 ),
    inference(avatar_contradiction_clause,[],[f2031])).

fof(f2031,plain,
    ( $false
    | ~ spl8_5
    | spl8_137 ),
    inference(subsumption_resolution,[],[f2030,f71])).

fof(f2030,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl8_5
    | spl8_137 ),
    inference(subsumption_resolution,[],[f2026,f2009])).

fof(f2009,plain,
    ( ~ l1_pre_topc(sK2)
    | spl8_137 ),
    inference(avatar_component_clause,[],[f2007])).

fof(f2026,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ spl8_5 ),
    inference(resolution,[],[f139,f84])).

fof(f2020,plain,(
    spl8_2 ),
    inference(avatar_contradiction_clause,[],[f2019])).

fof(f2019,plain,
    ( $false
    | spl8_2 ),
    inference(subsumption_resolution,[],[f315,f125])).

fof(f125,plain,
    ( ~ v1_tdlat_3(sK1)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl8_2
  <=> v1_tdlat_3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f315,plain,(
    v1_tdlat_3(sK1) ),
    inference(global_subsumption,[],[f310,f314])).

fof(f314,plain,
    ( ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | v1_tdlat_3(sK1) ),
    inference(subsumption_resolution,[],[f313,f69])).

fof(f313,plain,
    ( ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | v1_tdlat_3(sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f312,f71])).

fof(f312,plain,
    ( ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | v1_tdlat_3(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f311,f72])).

fof(f72,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f311,plain,
    ( ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | v1_tdlat_3(sK1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f163,f73])).

fof(f163,plain,
    ( ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | v1_tdlat_3(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f161,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(u1_struct_0(X1),X0)
      | v1_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_tex_2(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f310,plain,(
    v2_tex_2(u1_struct_0(sK1),sK0) ),
    inference(global_subsumption,[],[f74,f188,f300,f309])).

fof(f309,plain,
    ( ~ v1_tdlat_3(sK1)
    | v2_tex_2(u1_struct_0(sK1),sK0) ),
    inference(subsumption_resolution,[],[f308,f69])).

fof(f308,plain,
    ( ~ v1_tdlat_3(sK1)
    | v2_tex_2(u1_struct_0(sK1),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f307,f71])).

fof(f307,plain,
    ( ~ v1_tdlat_3(sK1)
    | v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f306,f72])).

fof(f306,plain,
    ( ~ v1_tdlat_3(sK1)
    | v2_tex_2(u1_struct_0(sK1),sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f164,f73])).

fof(f164,plain,
    ( ~ v1_tdlat_3(sK1)
    | v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f161,f116])).

fof(f300,plain,
    ( ~ v4_tex_2(sK1,sK0)
    | v3_tex_2(u1_struct_0(sK1),sK0) ),
    inference(subsumption_resolution,[],[f299,f69])).

fof(f299,plain,
    ( ~ v4_tex_2(sK1,sK0)
    | v3_tex_2(u1_struct_0(sK1),sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f298,f71])).

fof(f298,plain,
    ( ~ v4_tex_2(sK1,sK0)
    | v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f166,f73])).

fof(f166,plain,
    ( ~ v4_tex_2(sK1,sK0)
    | v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f161,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_tex_2(X1,X0)
      | v3_tex_2(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( v3_tex_2(X2,X0)
      | ~ v4_tex_2(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tex_2(X2,X0)
                  | ~ v4_tex_2(X1,X0) )
                & ( v4_tex_2(X1,X0)
                  | ~ v3_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tex_2(X2,X0)
              <=> v4_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tex_2(X2,X0)
              <=> v4_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v3_tex_2(X2,X0)
                <=> v4_tex_2(X1,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_tex_2)).

fof(f188,plain,
    ( ~ v3_tex_2(u1_struct_0(sK1),sK0)
    | v2_tex_2(u1_struct_0(sK1),sK0) ),
    inference(subsumption_resolution,[],[f167,f71])).

fof(f167,plain,
    ( ~ v3_tex_2(u1_struct_0(sK1),sK0)
    | v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f161,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f74,plain,
    ( v1_tdlat_3(sK1)
    | v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f1994,plain,
    ( ~ spl8_8
    | ~ spl8_14
    | spl8_32
    | ~ spl8_34
    | ~ spl8_35
    | ~ spl8_36
    | spl8_37
    | ~ spl8_43 ),
    inference(avatar_contradiction_clause,[],[f1993])).

fof(f1993,plain,
    ( $false
    | ~ spl8_8
    | ~ spl8_14
    | spl8_32
    | ~ spl8_34
    | ~ spl8_35
    | ~ spl8_36
    | spl8_37
    | ~ spl8_43 ),
    inference(subsumption_resolution,[],[f1992,f414])).

fof(f414,plain,
    ( u1_struct_0(sK1) != sK3(sK0,u1_struct_0(sK1))
    | spl8_37 ),
    inference(avatar_component_clause,[],[f413])).

fof(f413,plain,
    ( spl8_37
  <=> u1_struct_0(sK1) = sK3(sK0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f1992,plain,
    ( u1_struct_0(sK1) = sK3(sK0,u1_struct_0(sK1))
    | ~ spl8_8
    | ~ spl8_14
    | spl8_32
    | ~ spl8_34
    | ~ spl8_35
    | ~ spl8_36
    | ~ spl8_43 ),
    inference(equality_resolution,[],[f1922])).

fof(f1922,plain,
    ( ! [X0,X1] :
        ( g1_pre_topc(X0,X1) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        | sK3(sK0,u1_struct_0(sK1)) = X0 )
    | ~ spl8_8
    | ~ spl8_14
    | spl8_32
    | ~ spl8_34
    | ~ spl8_35
    | ~ spl8_36
    | ~ spl8_43 ),
    inference(superposition,[],[f1074,f1894])).

fof(f1894,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK5(sK0,sK3(sK0,u1_struct_0(sK1)))
    | ~ spl8_8
    | ~ spl8_14
    | spl8_32
    | ~ spl8_34
    | ~ spl8_35
    | ~ spl8_36
    | ~ spl8_43 ),
    inference(backward_demodulation,[],[f969,f1876])).

fof(f1876,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(sK3(sK0,u1_struct_0(sK1)),u1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))))
    | ~ spl8_8
    | ~ spl8_14
    | spl8_32
    | ~ spl8_34
    | ~ spl8_35
    | ~ spl8_36 ),
    inference(forward_demodulation,[],[f1856,f407])).

fof(f407,plain,
    ( sK3(sK0,u1_struct_0(sK1)) = u1_struct_0(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f405])).

fof(f405,plain,
    ( spl8_36
  <=> sK3(sK0,u1_struct_0(sK1)) = u1_struct_0(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f1856,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))),u1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))))
    | ~ spl8_8
    | ~ spl8_14
    | spl8_32
    | ~ spl8_34
    | ~ spl8_35
    | ~ spl8_36 ),
    inference(subsumption_resolution,[],[f1855,f398])).

fof(f398,plain,
    ( m1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f396])).

fof(f396,plain,
    ( spl8_35
  <=> m1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f1855,plain,
    ( ~ m1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))),u1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))))
    | ~ spl8_8
    | ~ spl8_14
    | spl8_32
    | ~ spl8_34
    | ~ spl8_35
    | ~ spl8_36 ),
    inference(subsumption_resolution,[],[f1854,f389])).

fof(f389,plain,
    ( v1_tdlat_3(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f387])).

fof(f387,plain,
    ( spl8_34
  <=> v1_tdlat_3(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f1854,plain,
    ( ~ v1_tdlat_3(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))),u1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))))
    | ~ spl8_8
    | ~ spl8_14
    | spl8_32
    | ~ spl8_35
    | ~ spl8_36 ),
    inference(subsumption_resolution,[],[f1853,f371])).

fof(f371,plain,
    ( ~ v2_struct_0(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | spl8_32 ),
    inference(avatar_component_clause,[],[f369])).

fof(f369,plain,
    ( spl8_32
  <=> v2_struct_0(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f1853,plain,
    ( v2_struct_0(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ v1_tdlat_3(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))),u1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))))
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_35
    | ~ spl8_36 ),
    inference(subsumption_resolution,[],[f1852,f73])).

fof(f1852,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ v1_tdlat_3(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))),u1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))))
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_35
    | ~ spl8_36 ),
    inference(subsumption_resolution,[],[f1842,f219])).

fof(f219,plain,
    ( r1_tarski(u1_struct_0(sK1),sK3(sK0,u1_struct_0(sK1)))
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl8_14
  <=> r1_tarski(u1_struct_0(sK1),sK3(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f1842,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),sK3(sK0,u1_struct_0(sK1)))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ v1_tdlat_3(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))),u1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))))
    | ~ spl8_8
    | ~ spl8_35
    | ~ spl8_36 ),
    inference(resolution,[],[f1388,f153])).

fof(f153,plain,
    ( ! [X3] :
        ( ~ m1_pre_topc(sK1,X3)
        | v2_struct_0(X3)
        | ~ v1_tdlat_3(X3)
        | ~ m1_pre_topc(X3,sK0)
        | g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) )
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl8_8
  <=> ! [X3] :
        ( g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        | v2_struct_0(X3)
        | ~ v1_tdlat_3(X3)
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(sK1,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f1388,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
        | ~ r1_tarski(u1_struct_0(X0),sK3(sK0,u1_struct_0(sK1)))
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl8_35
    | ~ spl8_36 ),
    inference(subsumption_resolution,[],[f1387,f70])).

fof(f70,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f1387,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
        | ~ r1_tarski(u1_struct_0(X0),sK3(sK0,u1_struct_0(sK1)))
        | ~ m1_pre_topc(X0,sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl8_35
    | ~ spl8_36 ),
    inference(subsumption_resolution,[],[f1383,f71])).

fof(f1383,plain,
    ( ! [X0] :
        ( m1_pre_topc(X0,sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
        | ~ r1_tarski(u1_struct_0(X0),sK3(sK0,u1_struct_0(sK1)))
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl8_35
    | ~ spl8_36 ),
    inference(resolution,[],[f847,f398])).

fof(f847,plain,
    ( ! [X17,X18] :
        ( ~ m1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1))),X18)
        | m1_pre_topc(X17,sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
        | ~ r1_tarski(u1_struct_0(X17),sK3(sK0,u1_struct_0(sK1)))
        | ~ m1_pre_topc(X17,X18)
        | ~ l1_pre_topc(X18)
        | ~ v2_pre_topc(X18) )
    | ~ spl8_36 ),
    inference(superposition,[],[f103,f407])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f969,plain,
    ( sK5(sK0,sK3(sK0,u1_struct_0(sK1))) = g1_pre_topc(sK3(sK0,u1_struct_0(sK1)),u1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))))
    | ~ spl8_36
    | ~ spl8_43 ),
    inference(forward_demodulation,[],[f500,f407])).

fof(f500,plain,
    ( sK5(sK0,sK3(sK0,u1_struct_0(sK1))) = g1_pre_topc(u1_struct_0(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))),u1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))))
    | ~ spl8_43 ),
    inference(avatar_component_clause,[],[f498])).

fof(f1074,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(X2,X3) != sK5(sK0,sK3(sK0,u1_struct_0(sK1)))
        | sK3(sK0,u1_struct_0(sK1)) = X2 )
    | ~ spl8_35
    | ~ spl8_36
    | ~ spl8_43 ),
    inference(subsumption_resolution,[],[f1061,f858])).

fof(f858,plain,
    ( m1_subset_1(u1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))),k1_zfmisc_1(k1_zfmisc_1(sK3(sK0,u1_struct_0(sK1)))))
    | ~ spl8_35
    | ~ spl8_36 ),
    inference(subsumption_resolution,[],[f833,f513])).

fof(f513,plain,
    ( l1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ spl8_35 ),
    inference(subsumption_resolution,[],[f506,f71])).

fof(f506,plain,
    ( l1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ spl8_35 ),
    inference(resolution,[],[f398,f84])).

fof(f833,plain,
    ( m1_subset_1(u1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))),k1_zfmisc_1(k1_zfmisc_1(sK3(sK0,u1_struct_0(sK1)))))
    | ~ l1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ spl8_36 ),
    inference(superposition,[],[f82,f407])).

fof(f1061,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(X2,X3) != sK5(sK0,sK3(sK0,u1_struct_0(sK1)))
        | sK3(sK0,u1_struct_0(sK1)) = X2
        | ~ m1_subset_1(u1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))),k1_zfmisc_1(k1_zfmisc_1(sK3(sK0,u1_struct_0(sK1))))) )
    | ~ spl8_36
    | ~ spl8_43 ),
    inference(superposition,[],[f108,f969])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1589,plain,
    ( ~ spl8_65
    | spl8_116
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f732,f261,f1538,f715])).

fof(f715,plain,
    ( spl8_65
  <=> l1_pre_topc(sK5(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_65])])).

fof(f1538,plain,
    ( spl8_116
  <=> m1_subset_1(u1_pre_topc(sK5(sK0,u1_struct_0(sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_116])])).

fof(f1544,plain,
    ( ~ spl8_116
    | spl8_117
    | ~ spl8_20
    | ~ spl8_66 ),
    inference(avatar_split_clause,[],[f891,f719,f261,f1542,f1538])).

fof(f1524,plain,
    ( ~ spl8_9
    | spl8_10
    | ~ spl8_37 ),
    inference(avatar_contradiction_clause,[],[f1523])).

fof(f1523,plain,
    ( $false
    | ~ spl8_9
    | spl8_10
    | ~ spl8_37 ),
    inference(subsumption_resolution,[],[f1522,f71])).

fof(f1522,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl8_9
    | spl8_10
    | ~ spl8_37 ),
    inference(subsumption_resolution,[],[f1521,f161])).

fof(f1521,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl8_9
    | spl8_10
    | ~ spl8_37 ),
    inference(subsumption_resolution,[],[f1520,f192])).

fof(f192,plain,
    ( v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl8_9
  <=> v2_tex_2(u1_struct_0(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f1520,plain,
    ( ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl8_10
    | ~ spl8_37 ),
    inference(subsumption_resolution,[],[f1492,f196])).

fof(f196,plain,
    ( ~ v3_tex_2(u1_struct_0(sK1),sK0)
    | spl8_10 ),
    inference(avatar_component_clause,[],[f194])).

fof(f1492,plain,
    ( v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl8_37 ),
    inference(trivial_inequality_removal,[],[f1491])).

fof(f1491,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK1)
    | v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl8_37 ),
    inference(superposition,[],[f92,f415])).

fof(f415,plain,
    ( u1_struct_0(sK1) = sK3(sK0,u1_struct_0(sK1))
    | ~ spl8_37 ),
    inference(avatar_component_clause,[],[f413])).

fof(f92,plain,(
    ! [X0,X1] :
      ( sK3(X0,X1) != X1
      | v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f1440,plain,
    ( ~ spl8_8
    | ~ spl8_14
    | ~ spl8_19
    | ~ spl8_20
    | spl8_32
    | ~ spl8_34
    | ~ spl8_35
    | ~ spl8_36
    | spl8_37
    | ~ spl8_66
    | ~ spl8_92 ),
    inference(avatar_contradiction_clause,[],[f1439])).

fof(f1439,plain,
    ( $false
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_19
    | ~ spl8_20
    | spl8_32
    | ~ spl8_34
    | ~ spl8_35
    | ~ spl8_36
    | spl8_37
    | ~ spl8_66
    | ~ spl8_92 ),
    inference(subsumption_resolution,[],[f1434,f414])).

fof(f1434,plain,
    ( u1_struct_0(sK1) = sK3(sK0,u1_struct_0(sK1))
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_19
    | ~ spl8_20
    | spl8_32
    | ~ spl8_34
    | ~ spl8_35
    | ~ spl8_36
    | ~ spl8_66
    | ~ spl8_92 ),
    inference(trivial_inequality_removal,[],[f1427])).

fof(f1427,plain,
    ( sK5(sK0,u1_struct_0(sK1)) != sK5(sK0,u1_struct_0(sK1))
    | u1_struct_0(sK1) = sK3(sK0,u1_struct_0(sK1))
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_19
    | ~ spl8_20
    | spl8_32
    | ~ spl8_34
    | ~ spl8_35
    | ~ spl8_36
    | ~ spl8_66
    | ~ spl8_92 ),
    inference(superposition,[],[f892,f1413])).

fof(f1413,plain,
    ( sK5(sK0,u1_struct_0(sK1)) = g1_pre_topc(sK3(sK0,u1_struct_0(sK1)),u1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))))
    | ~ spl8_8
    | ~ spl8_14
    | spl8_32
    | ~ spl8_34
    | ~ spl8_35
    | ~ spl8_36
    | ~ spl8_92 ),
    inference(forward_demodulation,[],[f1412,f407])).

fof(f1412,plain,
    ( sK5(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))),u1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))))
    | ~ spl8_8
    | ~ spl8_14
    | spl8_32
    | ~ spl8_34
    | ~ spl8_35
    | ~ spl8_36
    | ~ spl8_92 ),
    inference(subsumption_resolution,[],[f1411,f398])).

fof(f1411,plain,
    ( sK5(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))),u1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))))
    | ~ m1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | ~ spl8_8
    | ~ spl8_14
    | spl8_32
    | ~ spl8_34
    | ~ spl8_35
    | ~ spl8_36
    | ~ spl8_92 ),
    inference(subsumption_resolution,[],[f1410,f389])).

fof(f1410,plain,
    ( sK5(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))),u1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))))
    | ~ v1_tdlat_3(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | ~ spl8_8
    | ~ spl8_14
    | spl8_32
    | ~ spl8_35
    | ~ spl8_36
    | ~ spl8_92 ),
    inference(subsumption_resolution,[],[f1409,f371])).

fof(f1409,plain,
    ( sK5(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))),u1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))))
    | v2_struct_0(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ v1_tdlat_3(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_35
    | ~ spl8_36
    | ~ spl8_92 ),
    inference(subsumption_resolution,[],[f1408,f73])).

fof(f1408,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | sK5(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))),u1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))))
    | v2_struct_0(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ v1_tdlat_3(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | ~ spl8_8
    | ~ spl8_14
    | ~ spl8_35
    | ~ spl8_36
    | ~ spl8_92 ),
    inference(subsumption_resolution,[],[f1394,f219])).

fof(f1394,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),sK3(sK0,u1_struct_0(sK1)))
    | ~ m1_pre_topc(sK1,sK0)
    | sK5(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))),u1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1)))))
    | v2_struct_0(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ v1_tdlat_3(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | ~ m1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | ~ spl8_8
    | ~ spl8_35
    | ~ spl8_36
    | ~ spl8_92 ),
    inference(resolution,[],[f1388,f1263])).

fof(f1263,plain,
    ( ! [X3] :
        ( ~ m1_pre_topc(sK1,X3)
        | g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = sK5(sK0,u1_struct_0(sK1))
        | v2_struct_0(X3)
        | ~ v1_tdlat_3(X3)
        | ~ m1_pre_topc(X3,sK0) )
    | ~ spl8_8
    | ~ spl8_92 ),
    inference(backward_demodulation,[],[f153,f1051])).

fof(f892,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(X2,X3) != sK5(sK0,u1_struct_0(sK1))
        | u1_struct_0(sK1) = X2 )
    | ~ spl8_19
    | ~ spl8_20
    | ~ spl8_66 ),
    inference(subsumption_resolution,[],[f889,f755])).

fof(f889,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(X2,X3) != sK5(sK0,u1_struct_0(sK1))
        | u1_struct_0(sK1) = X2
        | ~ m1_subset_1(u1_pre_topc(sK5(sK0,u1_struct_0(sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
    | ~ spl8_20
    | ~ spl8_66 ),
    inference(superposition,[],[f108,f883])).

fof(f1281,plain,(
    spl8_105 ),
    inference(avatar_contradiction_clause,[],[f1280])).

fof(f1280,plain,
    ( $false
    | spl8_105 ),
    inference(subsumption_resolution,[],[f1279,f162])).

fof(f162,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f158,f71])).

fof(f158,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f73,f84])).

fof(f1279,plain,
    ( ~ l1_pre_topc(sK1)
    | spl8_105 ),
    inference(resolution,[],[f1274,f82])).

fof(f1274,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | spl8_105 ),
    inference(avatar_component_clause,[],[f1272])).

fof(f1272,plain,
    ( spl8_105
  <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_105])])).

fof(f1278,plain,
    ( ~ spl8_105
    | spl8_106
    | ~ spl8_92 ),
    inference(avatar_split_clause,[],[f1266,f1049,f1276,f1272])).

fof(f1266,plain,
    ( ! [X4,X5] :
        ( sK5(sK0,u1_struct_0(sK1)) != g1_pre_topc(X4,X5)
        | u1_pre_topc(sK1) = X5
        | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
    | ~ spl8_92 ),
    inference(superposition,[],[f109,f1051])).

fof(f1254,plain,
    ( ~ spl8_19
    | ~ spl8_104 ),
    inference(avatar_contradiction_clause,[],[f1253])).

fof(f1253,plain,
    ( $false
    | ~ spl8_19
    | ~ spl8_104 ),
    inference(subsumption_resolution,[],[f1252,f73])).

fof(f1252,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ spl8_19
    | ~ spl8_104 ),
    inference(subsumption_resolution,[],[f1247,f71])).

fof(f1247,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl8_19
    | ~ spl8_104 ),
    inference(resolution,[],[f1245,f255])).

fof(f1245,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK5(sK0,u1_struct_0(sK1)),X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0) )
    | ~ spl8_104 ),
    inference(avatar_component_clause,[],[f1244])).

fof(f1244,plain,
    ( spl8_104
  <=> ! [X0] :
        ( ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK5(sK0,u1_struct_0(sK1)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_104])])).

fof(f1246,plain,
    ( spl8_104
    | spl8_92
    | ~ spl8_20
    | ~ spl8_66 ),
    inference(avatar_split_clause,[],[f1234,f719,f261,f1049,f1244])).

fof(f1234,plain,
    ( ! [X0] :
        ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK5(sK0,u1_struct_0(sK1))
        | ~ m1_pre_topc(sK1,X0)
        | ~ m1_pre_topc(sK5(sK0,u1_struct_0(sK1)),X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl8_20
    | ~ spl8_66 ),
    inference(equality_resolution,[],[f1231])).

fof(f731,plain,
    ( ~ spl8_19
    | spl8_65 ),
    inference(avatar_contradiction_clause,[],[f730])).

fof(f730,plain,
    ( $false
    | ~ spl8_19
    | spl8_65 ),
    inference(subsumption_resolution,[],[f729,f717])).

fof(f717,plain,
    ( ~ l1_pre_topc(sK5(sK0,u1_struct_0(sK1)))
    | spl8_65 ),
    inference(avatar_component_clause,[],[f715])).

fof(f722,plain,
    ( ~ spl8_65
    | spl8_66
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f713,f237,f719,f715])).

fof(f237,plain,
    ( spl8_17
  <=> v1_pre_topc(sK5(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f713,plain,
    ( sK5(sK0,u1_struct_0(sK1)) = g1_pre_topc(u1_struct_0(sK5(sK0,u1_struct_0(sK1))),u1_pre_topc(sK5(sK0,u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK5(sK0,u1_struct_0(sK1)))
    | ~ spl8_17 ),
    inference(resolution,[],[f239,f83])).

fof(f239,plain,
    ( v1_pre_topc(sK5(sK0,u1_struct_0(sK1)))
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f237])).

fof(f712,plain,
    ( ~ spl8_31
    | spl8_15
    | ~ spl8_14 ),
    inference(avatar_split_clause,[],[f503,f217,f225,f365])).

fof(f365,plain,
    ( spl8_31
  <=> v1_xboole_0(sK3(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f503,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | ~ spl8_14 ),
    inference(resolution,[],[f320,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f320,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(sK3(sK0,u1_struct_0(sK1))))
    | ~ spl8_14 ),
    inference(resolution,[],[f219,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f512,plain,
    ( ~ spl8_35
    | spl8_42 ),
    inference(avatar_contradiction_clause,[],[f511])).

fof(f511,plain,
    ( $false
    | ~ spl8_35
    | spl8_42 ),
    inference(subsumption_resolution,[],[f510,f71])).

fof(f510,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl8_35
    | spl8_42 ),
    inference(subsumption_resolution,[],[f506,f496])).

fof(f496,plain,
    ( ~ l1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | spl8_42 ),
    inference(avatar_component_clause,[],[f494])).

fof(f491,plain,
    ( spl8_31
    | spl8_36
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f490,f211,f205,f405,f365])).

fof(f205,plain,
    ( spl8_12
  <=> m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f211,plain,
    ( spl8_13
  <=> v2_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f490,plain,
    ( sK3(sK0,u1_struct_0(sK1)) = u1_struct_0(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f489,f69])).

fof(f489,plain,
    ( sK3(sK0,u1_struct_0(sK1)) = u1_struct_0(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f488,f70])).

fof(f488,plain,
    ( sK3(sK0,u1_struct_0(sK1)) = u1_struct_0(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f487,f71])).

fof(f487,plain,
    ( sK3(sK0,u1_struct_0(sK1)) = u1_struct_0(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f465,f213])).

fof(f213,plain,
    ( v2_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f211])).

fof(f465,plain,
    ( ~ v2_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0)
    | sK3(sK0,u1_struct_0(sK1)) = u1_struct_0(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12 ),
    inference(resolution,[],[f207,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | u1_struct_0(sK5(X0,X1)) = X1
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK5(X0,X1)) = X1
            & m1_pre_topc(sK5(X0,X1),X0)
            & v1_tdlat_3(sK5(X0,X1))
            & v1_pre_topc(sK5(X0,X1))
            & ~ v2_struct_0(sK5(X0,X1)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f59])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_tdlat_3(X2)
          & v1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK5(X0,X1)) = X1
        & m1_pre_topc(sK5(X0,X1),X0)
        & v1_tdlat_3(sK5(X0,X1))
        & v1_pre_topc(sK5(X0,X1))
        & ~ v2_struct_0(sK5(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tex_2)).

fof(f207,plain,
    ( m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f205])).

fof(f486,plain,
    ( spl8_31
    | spl8_35
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f485,f211,f205,f396,f365])).

fof(f485,plain,
    ( m1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f484,f69])).

fof(f484,plain,
    ( m1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f483,f70])).

fof(f483,plain,
    ( m1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f482,f71])).

fof(f482,plain,
    ( m1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f464,f213])).

fof(f464,plain,
    ( ~ v2_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0)
    | m1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1))),sK0)
    | v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12 ),
    inference(resolution,[],[f207,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | m1_pre_topc(sK5(X0,X1),X0)
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f481,plain,
    ( spl8_31
    | spl8_34
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f480,f211,f205,f387,f365])).

fof(f480,plain,
    ( v1_tdlat_3(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f479,f69])).

fof(f479,plain,
    ( v1_tdlat_3(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f478,f70])).

fof(f478,plain,
    ( v1_tdlat_3(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f477,f71])).

fof(f477,plain,
    ( v1_tdlat_3(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f463,f213])).

fof(f463,plain,
    ( ~ v2_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0)
    | v1_tdlat_3(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12 ),
    inference(resolution,[],[f207,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v1_tdlat_3(sK5(X0,X1))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f476,plain,
    ( spl8_31
    | spl8_33
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f475,f211,f205,f378,f365])).

fof(f475,plain,
    ( v1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f474,f69])).

fof(f474,plain,
    ( v1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f473,f70])).

fof(f473,plain,
    ( v1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f472,f71])).

fof(f472,plain,
    ( v1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f462,f213])).

fof(f462,plain,
    ( ~ v2_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0)
    | v1_pre_topc(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12 ),
    inference(resolution,[],[f207,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v1_pre_topc(sK5(X0,X1))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f452,plain,
    ( ~ spl8_9
    | spl8_10
    | ~ spl8_15
    | ~ spl8_31 ),
    inference(avatar_contradiction_clause,[],[f451])).

fof(f451,plain,
    ( $false
    | ~ spl8_9
    | spl8_10
    | ~ spl8_15
    | ~ spl8_31 ),
    inference(subsumption_resolution,[],[f450,f71])).

fof(f450,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl8_9
    | spl8_10
    | ~ spl8_15
    | ~ spl8_31 ),
    inference(subsumption_resolution,[],[f449,f161])).

fof(f449,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl8_9
    | spl8_10
    | ~ spl8_15
    | ~ spl8_31 ),
    inference(subsumption_resolution,[],[f448,f192])).

fof(f448,plain,
    ( ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl8_10
    | ~ spl8_15
    | ~ spl8_31 ),
    inference(subsumption_resolution,[],[f445,f196])).

fof(f445,plain,
    ( v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl8_15
    | ~ spl8_31 ),
    inference(trivial_inequality_removal,[],[f444])).

fof(f444,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK1)
    | v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl8_15
    | ~ spl8_31 ),
    inference(superposition,[],[f92,f434])).

fof(f434,plain,
    ( u1_struct_0(sK1) = sK3(sK0,u1_struct_0(sK1))
    | ~ spl8_15
    | ~ spl8_31 ),
    inference(resolution,[],[f367,f316])).

fof(f316,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | u1_struct_0(sK1) = X0 )
    | ~ spl8_15 ),
    inference(resolution,[],[f227,f112])).

fof(f367,plain,
    ( v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f365])).

fof(f372,plain,
    ( spl8_31
    | ~ spl8_32
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f363,f211,f205,f369,f365])).

fof(f363,plain,
    ( ~ v2_struct_0(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f362,f69])).

fof(f362,plain,
    ( ~ v2_struct_0(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f361,f70])).

fof(f361,plain,
    ( ~ v2_struct_0(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f360,f71])).

fof(f360,plain,
    ( ~ v2_struct_0(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f326,f213])).

fof(f326,plain,
    ( ~ v2_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0)
    | ~ v2_struct_0(sK5(sK0,sK3(sK0,u1_struct_0(sK1))))
    | v1_xboole_0(sK3(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_12 ),
    inference(resolution,[],[f207,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ v2_struct_0(sK5(X0,X1))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f305,plain,
    ( spl8_1
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f304,f194,f119])).

fof(f119,plain,
    ( spl8_1
  <=> v4_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f304,plain,
    ( ~ v3_tex_2(u1_struct_0(sK1),sK0)
    | v4_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f303,f69])).

fof(f303,plain,
    ( ~ v3_tex_2(u1_struct_0(sK1),sK0)
    | v4_tex_2(sK1,sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f302,f71])).

fof(f302,plain,
    ( ~ v3_tex_2(u1_struct_0(sK1),sK0)
    | v4_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f165,f73])).

fof(f165,plain,
    ( ~ v3_tex_2(u1_struct_0(sK1),sK0)
    | v4_tex_2(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f161,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(u1_struct_0(X1),X0)
      | v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( v4_tex_2(X1,X0)
      | ~ v3_tex_2(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f301,plain,
    ( spl8_10
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f300,f119,f194])).

fof(f297,plain,
    ( ~ spl8_2
    | spl8_9 ),
    inference(avatar_contradiction_clause,[],[f296])).

fof(f296,plain,
    ( $false
    | ~ spl8_2
    | spl8_9 ),
    inference(subsumption_resolution,[],[f191,f183])).

fof(f183,plain,
    ( v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f182,f69])).

fof(f182,plain,
    ( v2_tex_2(u1_struct_0(sK1),sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f181,f71])).

fof(f181,plain,
    ( v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f180,f72])).

fof(f180,plain,
    ( v2_tex_2(u1_struct_0(sK1),sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f179,f73])).

fof(f179,plain,
    ( v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f164,f124])).

fof(f124,plain,
    ( v1_tdlat_3(sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f123])).

fof(f191,plain,
    ( ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | spl8_9 ),
    inference(avatar_component_clause,[],[f190])).

fof(f264,plain,
    ( spl8_15
    | spl8_20
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f259,f190,f261,f225])).

fof(f259,plain,
    ( ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | u1_struct_0(sK1) = u1_struct_0(sK5(sK0,u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f258,f69])).

fof(f258,plain,
    ( ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | u1_struct_0(sK1) = u1_struct_0(sK5(sK0,u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f257,f70])).

fof(f257,plain,
    ( ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | u1_struct_0(sK1) = u1_struct_0(sK5(sK0,u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f176,f71])).

fof(f176,plain,
    ( ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | u1_struct_0(sK1) = u1_struct_0(sK5(sK0,u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f161,f98])).

fof(f256,plain,
    ( spl8_15
    | spl8_19
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f251,f190,f253,f225])).

fof(f251,plain,
    ( ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | m1_pre_topc(sK5(sK0,u1_struct_0(sK1)),sK0)
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f250,f69])).

fof(f250,plain,
    ( ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | m1_pre_topc(sK5(sK0,u1_struct_0(sK1)),sK0)
    | v1_xboole_0(u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f249,f70])).

fof(f249,plain,
    ( ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | m1_pre_topc(sK5(sK0,u1_struct_0(sK1)),sK0)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f175,f71])).

fof(f175,plain,
    ( ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | m1_pre_topc(sK5(sK0,u1_struct_0(sK1)),sK0)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f161,f97])).

fof(f240,plain,
    ( spl8_15
    | spl8_17
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f235,f190,f237,f225])).

fof(f235,plain,
    ( ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | v1_pre_topc(sK5(sK0,u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f234,f69])).

fof(f234,plain,
    ( ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | v1_pre_topc(sK5(sK0,u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f233,f70])).

fof(f233,plain,
    ( ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | v1_pre_topc(sK5(sK0,u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f173,f71])).

fof(f173,plain,
    ( ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | v1_pre_topc(sK5(sK0,u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f161,f95])).

fof(f220,plain,
    ( spl8_10
    | ~ spl8_9
    | spl8_14 ),
    inference(avatar_split_clause,[],[f215,f217,f190,f194])).

fof(f215,plain,
    ( r1_tarski(u1_struct_0(sK1),sK3(sK0,u1_struct_0(sK1)))
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | v3_tex_2(u1_struct_0(sK1),sK0) ),
    inference(subsumption_resolution,[],[f171,f71])).

fof(f171,plain,
    ( r1_tarski(u1_struct_0(sK1),sK3(sK0,u1_struct_0(sK1)))
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f161,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,sK3(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f214,plain,
    ( spl8_10
    | ~ spl8_9
    | spl8_13 ),
    inference(avatar_split_clause,[],[f209,f211,f190,f194])).

fof(f209,plain,
    ( v2_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0)
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | v3_tex_2(u1_struct_0(sK1),sK0) ),
    inference(subsumption_resolution,[],[f170,f71])).

fof(f170,plain,
    ( v2_tex_2(sK3(sK0,u1_struct_0(sK1)),sK0)
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f161,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(sK3(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f208,plain,
    ( spl8_10
    | ~ spl8_9
    | spl8_12 ),
    inference(avatar_split_clause,[],[f203,f205,f190,f194])).

fof(f203,plain,
    ( m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | v3_tex_2(u1_struct_0(sK1),sK0) ),
    inference(subsumption_resolution,[],[f169,f71])).

fof(f169,plain,
    ( m1_subset_1(sK3(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f161,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f154,plain,
    ( spl8_1
    | spl8_8 ),
    inference(avatar_split_clause,[],[f75,f152,f119])).

fof(f75,plain,(
    ! [X3] :
      ( g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
      | ~ m1_pre_topc(sK1,X3)
      | ~ m1_pre_topc(X3,sK0)
      | ~ v1_tdlat_3(X3)
      | v2_struct_0(X3)
      | v4_tex_2(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f150,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f76,f147,f123,f119])).

fof(f76,plain,
    ( ~ v2_struct_0(sK2)
    | ~ v1_tdlat_3(sK1)
    | ~ v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f145,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | spl8_6 ),
    inference(avatar_split_clause,[],[f77,f142,f123,f119])).

fof(f77,plain,
    ( v1_tdlat_3(sK2)
    | ~ v1_tdlat_3(sK1)
    | ~ v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f140,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | spl8_5 ),
    inference(avatar_split_clause,[],[f78,f137,f123,f119])).

fof(f78,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ v1_tdlat_3(sK1)
    | ~ v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f135,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | spl8_4 ),
    inference(avatar_split_clause,[],[f79,f132,f123,f119])).

fof(f79,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ v1_tdlat_3(sK1)
    | ~ v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f130,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f80,f127,f123,f119])).

fof(f80,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ v1_tdlat_3(sK1)
    | ~ v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

%------------------------------------------------------------------------------
