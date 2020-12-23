%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : orders_2__t39_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:20 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  202 ( 534 expanded)
%              Number of leaves         :   32 ( 216 expanded)
%              Depth                    :   15
%              Number of atoms          :  945 (2672 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f879,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f92,f96,f100,f104,f133,f144,f154,f171,f215,f220,f224,f242,f332,f346,f469,f470,f487,f552,f556,f560,f605,f756,f769,f794,f811,f836,f873,f878])).

fof(f878,plain,
    ( spl8_68
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_58 ),
    inference(avatar_split_clause,[],[f877,f344,f102,f98,f94,f86,f534])).

fof(f534,plain,
    ( spl8_68
  <=> v6_orders_2(sK5(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_68])])).

fof(f86,plain,
    ( spl8_0
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f94,plain,
    ( spl8_4
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f98,plain,
    ( spl8_6
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f102,plain,
    ( spl8_8
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f344,plain,
    ( spl8_58
  <=> r1_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_58])])).

fof(f877,plain,
    ( v6_orders_2(sK5(sK0,sK1,sK2),sK0)
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_58 ),
    inference(subsumption_resolution,[],[f876,f87])).

fof(f87,plain,
    ( v3_orders_2(sK0)
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f86])).

fof(f876,plain,
    ( ~ v3_orders_2(sK0)
    | v6_orders_2(sK5(sK0,sK1,sK2),sK0)
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_58 ),
    inference(subsumption_resolution,[],[f875,f99])).

fof(f99,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f875,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | v6_orders_2(sK5(sK0,sK1,sK2),sK0)
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_58 ),
    inference(subsumption_resolution,[],[f874,f103])).

fof(f103,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f102])).

fof(f874,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | v6_orders_2(sK5(sK0,sK1,sK2),sK0)
    | ~ spl8_4
    | ~ spl8_58 ),
    inference(subsumption_resolution,[],[f776,f95])).

fof(f95,plain,
    ( l1_orders_2(sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f776,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | v6_orders_2(sK5(sK0,sK1,sK2),sK0)
    | ~ spl8_58 ),
    inference(resolution,[],[f345,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | v6_orders_2(sK5(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ? [X3] :
                      ( r2_hidden(X2,X3)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v6_orders_2(X3,X0) )
                  | ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2) ) )
                & ( r1_orders_2(X0,X2,X1)
                  | r1_orders_2(X0,X1,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X2,X4)
                      | ~ r2_hidden(X1,X4)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X4,X0) ) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ? [X3] :
                      ( r2_hidden(X2,X3)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v6_orders_2(X3,X0) )
                  | ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2) ) )
                & ( r1_orders_2(X0,X2,X1)
                  | r1_orders_2(X0,X1,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X2,X4)
                      | ~ r2_hidden(X1,X4)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X4,X0) ) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & v6_orders_2(X3,X0) )
                       => ~ ( r2_hidden(X2,X3)
                            & r2_hidden(X1,X3) ) )
                    & ( r1_orders_2(X0,X2,X1)
                      | r1_orders_2(X0,X1,X2) ) )
                & ~ ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2)
                    & ? [X4] :
                        ( r2_hidden(X2,X4)
                        & r2_hidden(X1,X4)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                        & v6_orders_2(X4,X0) ) ) ) ) ) ) ),
    inference(rectify,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & v6_orders_2(X3,X0) )
                       => ~ ( r2_hidden(X2,X3)
                            & r2_hidden(X1,X3) ) )
                    & ( r1_orders_2(X0,X2,X1)
                      | r1_orders_2(X0,X1,X2) ) )
                & ~ ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2)
                    & ? [X3] :
                        ( r2_hidden(X2,X3)
                        & r2_hidden(X1,X3)
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & v6_orders_2(X3,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t39_orders_2.p',t38_orders_2)).

fof(f345,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl8_58 ),
    inference(avatar_component_clause,[],[f344])).

fof(f873,plain,
    ( spl8_88
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_58 ),
    inference(avatar_split_clause,[],[f815,f344,f102,f98,f94,f86,f595])).

fof(f595,plain,
    ( spl8_88
  <=> m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_88])])).

fof(f815,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_58 ),
    inference(subsumption_resolution,[],[f814,f87])).

fof(f814,plain,
    ( ~ v3_orders_2(sK0)
    | m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_58 ),
    inference(subsumption_resolution,[],[f813,f99])).

fof(f813,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_58 ),
    inference(subsumption_resolution,[],[f812,f103])).

fof(f812,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_4
    | ~ spl8_58 ),
    inference(subsumption_resolution,[],[f777,f95])).

fof(f777,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_58 ),
    inference(resolution,[],[f345,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f836,plain,
    ( ~ spl8_14
    | ~ spl8_76
    | ~ spl8_78
    | ~ spl8_80
    | ~ spl8_92 ),
    inference(avatar_contradiction_clause,[],[f835])).

fof(f835,plain,
    ( $false
    | ~ spl8_14
    | ~ spl8_76
    | ~ spl8_78
    | ~ spl8_80
    | ~ spl8_92 ),
    inference(subsumption_resolution,[],[f833,f126])).

fof(f126,plain,
    ( ! [X3] : ~ sP4(X3,sK2,sK1,sK0)
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl8_14
  <=> ! [X3] : ~ sP4(X3,sK2,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f833,plain,
    ( sP4(sK5(sK0,sK2,sK1),sK2,sK1,sK0)
    | ~ spl8_76
    | ~ spl8_78
    | ~ spl8_80
    | ~ spl8_92 ),
    inference(resolution,[],[f718,f555])).

fof(f555,plain,
    ( r2_hidden(sK2,sK5(sK0,sK2,sK1))
    | ~ spl8_78 ),
    inference(avatar_component_clause,[],[f554])).

fof(f554,plain,
    ( spl8_78
  <=> r2_hidden(sK2,sK5(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_78])])).

fof(f718,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK5(sK0,sK2,sK1))
        | sP4(sK5(sK0,sK2,sK1),X1,sK1,sK0) )
    | ~ spl8_76
    | ~ spl8_80
    | ~ spl8_92 ),
    inference(resolution,[],[f632,f559])).

fof(f559,plain,
    ( r2_hidden(sK1,sK5(sK0,sK2,sK1))
    | ~ spl8_80 ),
    inference(avatar_component_clause,[],[f558])).

fof(f558,plain,
    ( spl8_80
  <=> r2_hidden(sK1,sK5(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_80])])).

fof(f632,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,sK5(sK0,sK2,sK1))
        | ~ r2_hidden(X3,sK5(sK0,sK2,sK1))
        | sP4(sK5(sK0,sK2,sK1),X3,X2,sK0) )
    | ~ spl8_76
    | ~ spl8_92 ),
    inference(subsumption_resolution,[],[f626,f551])).

fof(f551,plain,
    ( v6_orders_2(sK5(sK0,sK2,sK1),sK0)
    | ~ spl8_76 ),
    inference(avatar_component_clause,[],[f550])).

fof(f550,plain,
    ( spl8_76
  <=> v6_orders_2(sK5(sK0,sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_76])])).

fof(f626,plain,
    ( ! [X2,X3] :
        ( ~ v6_orders_2(sK5(sK0,sK2,sK1),sK0)
        | ~ r2_hidden(X2,sK5(sK0,sK2,sK1))
        | ~ r2_hidden(X3,sK5(sK0,sK2,sK1))
        | sP4(sK5(sK0,sK2,sK1),X3,X2,sK0) )
    | ~ spl8_92 ),
    inference(resolution,[],[f604,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v6_orders_2(X3,X0)
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X2,X3)
      | sP4(X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(X3,X0) )
              <~> ( r2_orders_2(X0,X1,X2)
                <=> ~ r1_orders_2(X0,X2,X1) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(X3,X0) )
              <~> ( r2_orders_2(X0,X1,X2)
                <=> ~ r1_orders_2(X0,X2,X1) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ? [X3] :
                      ( r2_hidden(X2,X3)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v6_orders_2(X3,X0) )
                <=> ( r2_orders_2(X0,X1,X2)
                  <=> ~ r1_orders_2(X0,X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ? [X3] :
                    ( r2_hidden(X2,X3)
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(X3,X0) )
              <=> ( r2_orders_2(X0,X1,X2)
                <=> ~ r1_orders_2(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t39_orders_2.p',t39_orders_2)).

fof(f604,plain,
    ( m1_subset_1(sK5(sK0,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_92 ),
    inference(avatar_component_clause,[],[f603])).

fof(f603,plain,
    ( spl8_92
  <=> m1_subset_1(sK5(sK0,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_92])])).

fof(f811,plain,
    ( spl8_72
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_58 ),
    inference(avatar_split_clause,[],[f799,f344,f102,f98,f94,f86,f542])).

fof(f542,plain,
    ( spl8_72
  <=> r2_hidden(sK1,sK5(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_72])])).

fof(f799,plain,
    ( r2_hidden(sK1,sK5(sK0,sK1,sK2))
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_58 ),
    inference(subsumption_resolution,[],[f798,f87])).

fof(f798,plain,
    ( ~ v3_orders_2(sK0)
    | r2_hidden(sK1,sK5(sK0,sK1,sK2))
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_58 ),
    inference(subsumption_resolution,[],[f797,f99])).

fof(f797,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | r2_hidden(sK1,sK5(sK0,sK1,sK2))
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_58 ),
    inference(subsumption_resolution,[],[f796,f103])).

fof(f796,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | r2_hidden(sK1,sK5(sK0,sK1,sK2))
    | ~ spl8_4
    | ~ spl8_58 ),
    inference(subsumption_resolution,[],[f778,f95])).

fof(f778,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | r2_hidden(sK1,sK5(sK0,sK1,sK2))
    | ~ spl8_58 ),
    inference(resolution,[],[f345,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | r2_hidden(X1,sK5(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f794,plain,
    ( spl8_74
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_58 ),
    inference(avatar_split_clause,[],[f785,f344,f102,f98,f94,f86,f546])).

fof(f546,plain,
    ( spl8_74
  <=> r2_hidden(sK2,sK5(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_74])])).

fof(f785,plain,
    ( r2_hidden(sK2,sK5(sK0,sK1,sK2))
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_58 ),
    inference(subsumption_resolution,[],[f784,f87])).

fof(f784,plain,
    ( ~ v3_orders_2(sK0)
    | r2_hidden(sK2,sK5(sK0,sK1,sK2))
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_58 ),
    inference(subsumption_resolution,[],[f783,f99])).

fof(f783,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | r2_hidden(sK2,sK5(sK0,sK1,sK2))
    | ~ spl8_4
    | ~ spl8_8
    | ~ spl8_58 ),
    inference(subsumption_resolution,[],[f782,f103])).

fof(f782,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | r2_hidden(sK2,sK5(sK0,sK1,sK2))
    | ~ spl8_4
    | ~ spl8_58 ),
    inference(subsumption_resolution,[],[f779,f95])).

fof(f779,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | r2_hidden(sK2,sK5(sK0,sK1,sK2))
    | ~ spl8_58 ),
    inference(resolution,[],[f345,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | r2_hidden(X2,sK5(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f769,plain,
    ( spl8_58
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f150,f128,f102,f98,f94,f344])).

fof(f128,plain,
    ( spl8_16
  <=> r2_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f150,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f149,f95])).

fof(f149,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f148,f99])).

fof(f148,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ spl8_8
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f147,f103])).

fof(f147,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ spl8_16 ),
    inference(resolution,[],[f129,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t39_orders_2.p',d10_orders_2)).

fof(f129,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f128])).

fof(f756,plain,
    ( ~ spl8_14
    | ~ spl8_68
    | ~ spl8_72
    | ~ spl8_74
    | ~ spl8_88 ),
    inference(avatar_contradiction_clause,[],[f755])).

fof(f755,plain,
    ( $false
    | ~ spl8_14
    | ~ spl8_68
    | ~ spl8_72
    | ~ spl8_74
    | ~ spl8_88 ),
    inference(subsumption_resolution,[],[f754,f126])).

fof(f754,plain,
    ( sP4(sK5(sK0,sK1,sK2),sK2,sK1,sK0)
    | ~ spl8_68
    | ~ spl8_72
    | ~ spl8_74
    | ~ spl8_88 ),
    inference(resolution,[],[f711,f547])).

fof(f547,plain,
    ( r2_hidden(sK2,sK5(sK0,sK1,sK2))
    | ~ spl8_74 ),
    inference(avatar_component_clause,[],[f546])).

fof(f711,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK5(sK0,sK1,sK2))
        | sP4(sK5(sK0,sK1,sK2),X0,sK1,sK0) )
    | ~ spl8_68
    | ~ spl8_72
    | ~ spl8_88 ),
    inference(resolution,[],[f618,f543])).

fof(f543,plain,
    ( r2_hidden(sK1,sK5(sK0,sK1,sK2))
    | ~ spl8_72 ),
    inference(avatar_component_clause,[],[f542])).

fof(f618,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,sK5(sK0,sK1,sK2))
        | ~ r2_hidden(X3,sK5(sK0,sK1,sK2))
        | sP4(sK5(sK0,sK1,sK2),X3,X2,sK0) )
    | ~ spl8_68
    | ~ spl8_88 ),
    inference(subsumption_resolution,[],[f612,f535])).

fof(f535,plain,
    ( v6_orders_2(sK5(sK0,sK1,sK2),sK0)
    | ~ spl8_68 ),
    inference(avatar_component_clause,[],[f534])).

fof(f612,plain,
    ( ! [X2,X3] :
        ( ~ v6_orders_2(sK5(sK0,sK1,sK2),sK0)
        | ~ r2_hidden(X2,sK5(sK0,sK1,sK2))
        | ~ r2_hidden(X3,sK5(sK0,sK1,sK2))
        | sP4(sK5(sK0,sK1,sK2),X3,X2,sK0) )
    | ~ spl8_88 ),
    inference(resolution,[],[f596,f45])).

fof(f596,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_88 ),
    inference(avatar_component_clause,[],[f595])).

fof(f605,plain,
    ( spl8_92
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f521,f152,f102,f98,f94,f86,f603])).

fof(f152,plain,
    ( spl8_18
  <=> r1_orders_2(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f521,plain,
    ( m1_subset_1(sK5(sK0,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f520,f87])).

fof(f520,plain,
    ( ~ v3_orders_2(sK0)
    | m1_subset_1(sK5(sK0,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f519,f103])).

fof(f519,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | m1_subset_1(sK5(sK0,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f518,f99])).

fof(f518,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | m1_subset_1(sK5(sK0,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_4
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f494,f95])).

fof(f494,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | m1_subset_1(sK5(sK0,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_18 ),
    inference(resolution,[],[f153,f65])).

fof(f153,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f152])).

fof(f560,plain,
    ( spl8_80
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f529,f152,f102,f98,f94,f86,f558])).

fof(f529,plain,
    ( r2_hidden(sK1,sK5(sK0,sK2,sK1))
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f528,f87])).

fof(f528,plain,
    ( ~ v3_orders_2(sK0)
    | r2_hidden(sK1,sK5(sK0,sK2,sK1))
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f527,f103])).

fof(f527,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | r2_hidden(sK1,sK5(sK0,sK2,sK1))
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f526,f99])).

fof(f526,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | r2_hidden(sK1,sK5(sK0,sK2,sK1))
    | ~ spl8_4
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f496,f95])).

fof(f496,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | r2_hidden(sK1,sK5(sK0,sK2,sK1))
    | ~ spl8_18 ),
    inference(resolution,[],[f153,f67])).

fof(f556,plain,
    ( spl8_78
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f525,f152,f102,f98,f94,f86,f554])).

fof(f525,plain,
    ( r2_hidden(sK2,sK5(sK0,sK2,sK1))
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f524,f87])).

fof(f524,plain,
    ( ~ v3_orders_2(sK0)
    | r2_hidden(sK2,sK5(sK0,sK2,sK1))
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f523,f103])).

fof(f523,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | r2_hidden(sK2,sK5(sK0,sK2,sK1))
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f522,f99])).

fof(f522,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | r2_hidden(sK2,sK5(sK0,sK2,sK1))
    | ~ spl8_4
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f495,f95])).

fof(f495,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | r2_hidden(sK2,sK5(sK0,sK2,sK1))
    | ~ spl8_18 ),
    inference(resolution,[],[f153,f66])).

fof(f552,plain,
    ( spl8_76
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f517,f152,f102,f98,f94,f86,f550])).

fof(f517,plain,
    ( v6_orders_2(sK5(sK0,sK2,sK1),sK0)
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f516,f87])).

fof(f516,plain,
    ( ~ v3_orders_2(sK0)
    | v6_orders_2(sK5(sK0,sK2,sK1),sK0)
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f515,f103])).

fof(f515,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | v6_orders_2(sK5(sK0,sK2,sK1),sK0)
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f514,f99])).

fof(f514,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | v6_orders_2(sK5(sK0,sK2,sK1),sK0)
    | ~ spl8_4
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f493,f95])).

fof(f493,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_orders_2(sK0)
    | v6_orders_2(sK5(sK0,sK2,sK1),sK0)
    | ~ spl8_18 ),
    inference(resolution,[],[f153,f64])).

fof(f487,plain,
    ( ~ spl8_14
    | ~ spl8_20 ),
    inference(avatar_contradiction_clause,[],[f486])).

fof(f486,plain,
    ( $false
    | ~ spl8_14
    | ~ spl8_20 ),
    inference(subsumption_resolution,[],[f143,f126])).

fof(f143,plain,
    ( sP4(sK3,sK2,sK1,sK0)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl8_20
  <=> sP4(sK3,sK2,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f470,plain,
    ( sK1 != sK2
    | r1_orders_2(sK0,sK2,sK1)
    | ~ r1_orders_2(sK0,sK2,sK2) ),
    introduced(theory_axiom,[])).

fof(f469,plain,
    ( spl8_66
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | spl8_17
    | ~ spl8_58 ),
    inference(avatar_split_clause,[],[f436,f344,f137,f102,f98,f94,f467])).

fof(f467,plain,
    ( spl8_66
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_66])])).

fof(f137,plain,
    ( spl8_17
  <=> ~ r2_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f436,plain,
    ( sK1 = sK2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_17
    | ~ spl8_58 ),
    inference(subsumption_resolution,[],[f435,f138])).

fof(f138,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f137])).

fof(f435,plain,
    ( sK1 = sK2
    | r2_orders_2(sK0,sK1,sK2)
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_58 ),
    inference(subsumption_resolution,[],[f434,f95])).

fof(f434,plain,
    ( ~ l1_orders_2(sK0)
    | sK1 = sK2
    | r2_orders_2(sK0,sK1,sK2)
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_58 ),
    inference(subsumption_resolution,[],[f433,f99])).

fof(f433,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | sK1 = sK2
    | r2_orders_2(sK0,sK1,sK2)
    | ~ spl8_8
    | ~ spl8_58 ),
    inference(subsumption_resolution,[],[f396,f103])).

fof(f396,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | sK1 = sK2
    | r2_orders_2(sK0,sK1,sK2)
    | ~ spl8_58 ),
    inference(resolution,[],[f345,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | X1 = X2
      | r2_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f346,plain,
    ( spl8_58
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_6
    | spl8_19
    | ~ spl8_22
    | ~ spl8_24
    | ~ spl8_26
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f325,f240,f222,f218,f213,f131,f98,f94,f86,f344])).

fof(f131,plain,
    ( spl8_19
  <=> ~ r1_orders_2(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f213,plain,
    ( spl8_22
  <=> r2_hidden(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f218,plain,
    ( spl8_24
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f222,plain,
    ( spl8_26
  <=> v6_orders_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f240,plain,
    ( spl8_30
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f325,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_19
    | ~ spl8_22
    | ~ spl8_24
    | ~ spl8_26
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f323,f132])).

fof(f132,plain,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f131])).

fof(f323,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_22
    | ~ spl8_24
    | ~ spl8_26
    | ~ spl8_30 ),
    inference(resolution,[],[f257,f219])).

fof(f219,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f218])).

fof(f257,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | r1_orders_2(sK0,sK2,X0)
        | r1_orders_2(sK0,X0,sK2) )
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_22
    | ~ spl8_26
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f256,f214])).

fof(f214,plain,
    ( r2_hidden(sK2,sK3)
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f213])).

fof(f256,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2,sK3)
        | ~ r2_hidden(X0,sK3)
        | r1_orders_2(sK0,sK2,X0)
        | r1_orders_2(sK0,X0,sK2) )
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_26
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f254,f223])).

fof(f223,plain,
    ( v6_orders_2(sK3,sK0)
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f222])).

fof(f254,plain,
    ( ! [X0] :
        ( ~ v6_orders_2(sK3,sK0)
        | ~ r2_hidden(sK2,sK3)
        | ~ r2_hidden(X0,sK3)
        | r1_orders_2(sK0,sK2,X0)
        | r1_orders_2(sK0,X0,sK2) )
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_30 ),
    inference(resolution,[],[f109,f241])).

fof(f241,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f240])).

fof(f109,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v6_orders_2(X1,sK0)
        | ~ r2_hidden(sK2,X1)
        | ~ r2_hidden(X0,X1)
        | r1_orders_2(sK0,sK2,X0)
        | r1_orders_2(sK0,X0,sK2) )
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f108,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t39_orders_2.p',t4_subset)).

fof(f108,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v6_orders_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK2,X1)
        | ~ r2_hidden(X0,X1)
        | r1_orders_2(sK0,sK2,X0)
        | r1_orders_2(sK0,X0,sK2) )
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f107,f87])).

fof(f107,plain,
    ( ! [X0,X1] :
        ( ~ v3_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v6_orders_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK2,X1)
        | ~ r2_hidden(X0,X1)
        | r1_orders_2(sK0,sK2,X0)
        | r1_orders_2(sK0,X0,sK2) )
    | ~ spl8_4
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f105,f95])).

fof(f105,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v6_orders_2(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK2,X1)
        | ~ r2_hidden(X0,X1)
        | r1_orders_2(sK0,sK2,X0)
        | r1_orders_2(sK0,X0,sK2) )
    | ~ spl8_6 ),
    inference(resolution,[],[f99,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v6_orders_2(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,X4)
      | ~ r2_hidden(X2,X4)
      | r1_orders_2(X0,X1,X2)
      | r1_orders_2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f332,plain,
    ( spl8_50
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_22
    | ~ spl8_26
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f324,f240,f222,f213,f98,f94,f86,f330])).

fof(f330,plain,
    ( spl8_50
  <=> r1_orders_2(sK0,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f324,plain,
    ( r1_orders_2(sK0,sK2,sK2)
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_22
    | ~ spl8_26
    | ~ spl8_30 ),
    inference(duplicate_literal_removal,[],[f322])).

fof(f322,plain,
    ( r1_orders_2(sK0,sK2,sK2)
    | r1_orders_2(sK0,sK2,sK2)
    | ~ spl8_0
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_22
    | ~ spl8_26
    | ~ spl8_30 ),
    inference(resolution,[],[f257,f214])).

fof(f242,plain,
    ( spl8_30
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f208,f142,f240])).

fof(f208,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_20 ),
    inference(resolution,[],[f143,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP4(X3,X2,X1,X0)
      | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f224,plain,
    ( spl8_26
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f211,f142,f222])).

fof(f211,plain,
    ( v6_orders_2(sK3,sK0)
    | ~ spl8_20 ),
    inference(resolution,[],[f143,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP4(X3,X2,X1,X0)
      | v6_orders_2(X3,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f220,plain,
    ( spl8_24
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f210,f142,f218])).

fof(f210,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl8_20 ),
    inference(resolution,[],[f143,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP4(X3,X2,X1,X0)
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f215,plain,
    ( spl8_22
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f209,f142,f213])).

fof(f209,plain,
    ( r2_hidden(sK2,sK3)
    | ~ spl8_20 ),
    inference(resolution,[],[f143,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP4(X3,X2,X1,X0)
      | r2_hidden(X2,X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f171,plain,
    ( ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_16
    | ~ spl8_18 ),
    inference(avatar_contradiction_clause,[],[f170])).

fof(f170,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_16
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f169,f129])).

fof(f169,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | ~ spl8_2
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f168,f91])).

fof(f91,plain,
    ( v5_orders_2(sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl8_2
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f168,plain,
    ( ~ v5_orders_2(sK0)
    | ~ r2_orders_2(sK0,sK1,sK2)
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f167,f103])).

fof(f167,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ r2_orders_2(sK0,sK1,sK2)
    | ~ spl8_4
    | ~ spl8_6
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f166,f99])).

fof(f166,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ r2_orders_2(sK0,sK1,sK2)
    | ~ spl8_4
    | ~ spl8_18 ),
    inference(subsumption_resolution,[],[f156,f95])).

fof(f156,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v5_orders_2(sK0)
    | ~ r2_orders_2(sK0,sK1,sK2)
    | ~ spl8_18 ),
    inference(resolution,[],[f153,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ r2_orders_2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( r2_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t39_orders_2.p',t30_orders_2)).

fof(f154,plain,
    ( spl8_14
    | spl8_18
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f145,f128,f152,f125])).

fof(f145,plain,
    ( ! [X3] :
        ( r1_orders_2(sK0,sK2,sK1)
        | ~ sP4(X3,sK2,sK1,sK0) )
    | ~ spl8_16 ),
    inference(subsumption_resolution,[],[f51,f129])).

fof(f51,plain,(
    ! [X3] :
      ( r1_orders_2(sK0,sK2,sK1)
      | ~ r2_orders_2(sK0,sK1,sK2)
      | ~ sP4(X3,sK2,sK1,sK0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f144,plain,
    ( spl8_20
    | spl8_17
    | spl8_19 ),
    inference(avatar_split_clause,[],[f140,f131,f137,f142])).

fof(f140,plain,
    ( sP4(sK3,sK2,sK1,sK0)
    | ~ spl8_17
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f135,f138])).

fof(f135,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | sP4(sK3,sK2,sK1,sK0)
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f52,f132])).

fof(f52,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r2_orders_2(sK0,sK1,sK2)
    | sP4(sK3,sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f133,plain,
    ( spl8_14
    | spl8_16
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f50,f131,f128,f125])).

fof(f50,plain,(
    ! [X3] :
      ( ~ r1_orders_2(sK0,sK2,sK1)
      | r2_orders_2(sK0,sK1,sK2)
      | ~ sP4(X3,sK2,sK1,sK0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f104,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f55,f102])).

fof(f55,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f100,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f54,f98])).

fof(f54,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f96,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f58,f94])).

fof(f58,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f92,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f57,f90])).

fof(f57,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f88,plain,(
    spl8_0 ),
    inference(avatar_split_clause,[],[f56,f86])).

fof(f56,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
