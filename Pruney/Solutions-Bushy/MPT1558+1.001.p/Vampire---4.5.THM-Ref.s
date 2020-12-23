%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1558+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:05 EST 2020

% Result     : Theorem 7.82s
% Output     : Refutation 7.82s
% Verified   : 
% Statistics : Number of formulae       :  501 (3401 expanded)
%              Number of leaves         :  133 (1423 expanded)
%              Depth                    :   16
%              Number of atoms          : 1969 (13829 expanded)
%              Number of equality atoms :   65 ( 549 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7909,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f96,f101,f106,f111,f116,f127,f159,f164,f169,f174,f179,f188,f193,f208,f213,f234,f239,f266,f271,f304,f314,f319,f324,f329,f401,f406,f430,f443,f448,f466,f502,f513,f518,f568,f573,f580,f585,f719,f751,f758,f763,f768,f773,f778,f790,f795,f800,f2065,f2070,f2075,f2082,f2087,f2092,f2097,f2102,f2109,f2114,f3438,f3443,f3448,f3839,f3844,f3855,f3860,f3865,f3870,f3875,f3893,f3898,f3903,f3982,f3987,f4028,f4053,f4075,f4080,f5557,f5562,f5567,f5572,f5587,f5592,f5597,f5602,f5607,f5620,f5625,f5630,f5635,f5640,f5653,f5658,f5663,f5668,f5673,f5678,f5683,f5688,f5693,f5698,f5703,f5708,f5713,f5718,f5723,f5728,f5733,f5738,f5743,f5748,f5753,f5758,f5763,f5768,f5773,f5778,f7093,f7888,f7901,f7903,f7905,f7908])).

fof(f7908,plain,
    ( ~ spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | spl7_7
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_61
    | ~ spl7_118
    | ~ spl7_119 ),
    inference(avatar_contradiction_clause,[],[f7907])).

fof(f7907,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | spl7_7
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_61
    | ~ spl7_118
    | ~ spl7_119 ),
    inference(subsumption_resolution,[],[f7906,f5329])).

fof(f5329,plain,
    ( ~ r2_lattice3(sK2,k2_xboole_0(sK3,sK4),sK6(k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k1_yellow_0(sK2,sK4),k1_yellow_0(sK2,sK3)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | spl7_7
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_61 ),
    inference(unit_resulting_resolution,[],[f115,f121,f121,f168,f173,f126,f3447,f3457])).

fof(f3457,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK6(k1_yellow_0(sK2,X1),sK2,X2,X0),u1_struct_0(sK2))
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | k1_yellow_0(sK2,X1) = k10_lattice3(sK2,X0,X2)
        | ~ r1_orders_2(sK2,X2,k1_yellow_0(sK2,X1))
        | ~ r1_orders_2(sK2,X0,k1_yellow_0(sK2,X1))
        | ~ r1_yellow_0(sK2,X1)
        | ~ r2_lattice3(sK2,X1,sK6(k1_yellow_0(sK2,X1),sK2,X2,X0)) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f3450,f121])).

fof(f3450,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK2,X0,k1_yellow_0(sK2,X1))
        | ~ m1_subset_1(k1_yellow_0(sK2,X1),u1_struct_0(sK2))
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | k1_yellow_0(sK2,X1) = k10_lattice3(sK2,X0,X2)
        | ~ r1_orders_2(sK2,X2,k1_yellow_0(sK2,X1))
        | ~ m1_subset_1(sK6(k1_yellow_0(sK2,X1),sK2,X2,X0),u1_struct_0(sK2))
        | ~ r1_yellow_0(sK2,X1)
        | ~ r2_lattice3(sK2,X1,sK6(k1_yellow_0(sK2,X1),sK2,X2,X0)) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f2077,f438])).

fof(f438,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK2,k1_yellow_0(sK2,X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r1_yellow_0(sK2,X0)
        | ~ r2_lattice3(sK2,X0,X1) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f437,f100])).

fof(f100,plain,
    ( l1_orders_2(sK2)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl7_3
  <=> l1_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f437,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK2,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r1_yellow_0(sK2,X0)
        | ~ l1_orders_2(sK2)
        | r1_orders_2(sK2,k1_yellow_0(sK2,X0),X1) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f436,f121])).

fof(f436,plain,
    ( ! [X0,X1] :
        ( ~ r2_lattice3(sK2,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r1_yellow_0(sK2,X0)
        | ~ m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK2))
        | ~ l1_orders_2(sK2)
        | r1_orders_2(sK2,k1_yellow_0(sK2,X0),X1) )
    | ~ spl7_2 ),
    inference(resolution,[],[f82,f95])).

fof(f95,plain,
    ( v5_orders_2(sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl7_2
  <=> v5_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f82,plain,(
    ! [X2,X0,X3] :
      ( ~ v5_orders_2(X0)
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X2)
      | ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,k1_yellow_0(X0,X2),X3) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | ~ r2_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X2)
      | k1_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP0(X2,X0,X1)
              & ( ( ! [X3] :
                      ( r1_orders_2(X0,X1,X3)
                      | ~ r2_lattice3(X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP0(X2,X0,X1)
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(definition_folding,[],[f24,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ( r1_yellow_0(X0,X2)
        & k1_yellow_0(X0,X2) = X1 )
      | ? [X3] :
          ( ~ r1_orders_2(X0,X1,X3)
          & r2_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ r2_lattice3(X0,X2,X1)
      | ~ sP0(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X1,X4) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_yellow_0)).

fof(f2077,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK2,X1,sK6(X1,sK2,X0,X2))
        | ~ r1_orders_2(sK2,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | k10_lattice3(sK2,X2,X0) = X1
        | ~ r1_orders_2(sK2,X0,X1) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f678,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | ~ r1_orders_2(X1,X0,sK6(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ~ r1_orders_2(X1,X0,sK6(X0,X1,X2,X3))
        & r1_orders_2(X1,X2,sK6(X0,X1,X2,X3))
        & r1_orders_2(X1,X3,sK6(X0,X1,X2,X3))
        & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X1)) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f44])).

fof(f44,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X1,X0,X4)
          & r1_orders_2(X1,X2,X4)
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,X0,sK6(X0,X1,X2,X3))
        & r1_orders_2(X1,X2,sK6(X0,X1,X2,X3))
        & r1_orders_2(X1,X3,sK6(X0,X1,X2,X3))
        & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ r1_orders_2(X1,X0,X4)
          & r1_orders_2(X1,X2,X4)
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X3,X0,X2,X1] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
      | ~ sP1(X3,X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X3,X0,X2,X1] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
      | ~ sP1(X3,X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f678,plain,
    ( ! [X2,X0,X1] :
        ( sP1(X0,sK2,X1,X2)
        | ~ r1_orders_2(sK2,X1,X0)
        | ~ r1_orders_2(sK2,X2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | k10_lattice3(sK2,X2,X1) = X0 )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f677,f100])).

fof(f677,plain,
    ( ! [X2,X0,X1] :
        ( sP1(X0,sK2,X1,X2)
        | ~ r1_orders_2(sK2,X1,X0)
        | ~ r1_orders_2(sK2,X2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | ~ l1_orders_2(sK2)
        | k10_lattice3(sK2,X2,X1) = X0 )
    | ~ spl7_2 ),
    inference(resolution,[],[f75,f95])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | sP1(X3,X0,X2,X1)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k10_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                      | sP1(X3,X0,X2,X1)
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                      | sP1(X3,X0,X2,X1)
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(definition_folding,[],[f26,f32])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X4)
                                & r1_orders_2(X0,X1,X4) )
                             => r1_orders_2(X0,X3,X4) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                     => ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 ) )
                    & ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X5)
                                & r1_orders_2(X0,X1,X5) )
                             => r1_orders_2(X0,X3,X5) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X4)
                                & r1_orders_2(X0,X1,X4) )
                             => r1_orders_2(X0,X3,X4) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                     => ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 ) )
                    & ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                     => ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X4)
                                & r1_orders_2(X0,X1,X4) )
                             => r1_orders_2(X0,X3,X4) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow_0)).

fof(f3447,plain,
    ( m1_subset_1(sK6(k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k1_yellow_0(sK2,sK4),k1_yellow_0(sK2,sK3)),u1_struct_0(sK2))
    | ~ spl7_61 ),
    inference(avatar_component_clause,[],[f3445])).

fof(f3445,plain,
    ( spl7_61
  <=> m1_subset_1(sK6(k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k1_yellow_0(sK2,sK4),k1_yellow_0(sK2,sK3)),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).

fof(f126,plain,
    ( k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)) != k10_lattice3(sK2,k1_yellow_0(sK2,sK3),k1_yellow_0(sK2,sK4))
    | spl7_7 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl7_7
  <=> k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)) = k10_lattice3(sK2,k1_yellow_0(sK2,sK3),k1_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f173,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,sK4),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl7_11
  <=> r1_orders_2(sK2,k1_yellow_0(sK2,sK4),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f168,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,sK3),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl7_10
  <=> r1_orders_2(sK2,k1_yellow_0(sK2,sK3),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f121,plain,
    ( ! [X0] : m1_subset_1(k1_yellow_0(sK2,X0),u1_struct_0(sK2))
    | ~ spl7_3 ),
    inference(unit_resulting_resolution,[],[f100,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f115,plain,
    ( r1_yellow_0(sK2,k2_xboole_0(sK3,sK4))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl7_6
  <=> r1_yellow_0(sK2,k2_xboole_0(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f7906,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,sK4),sK6(k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k1_yellow_0(sK2,sK4),k1_yellow_0(sK2,sK3)))
    | ~ spl7_3
    | ~ spl7_61
    | ~ spl7_118
    | ~ spl7_119 ),
    inference(forward_demodulation,[],[f7889,f79])).

fof(f79,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f7889,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,sK3),sK6(k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k1_yellow_0(sK2,sK4),k1_yellow_0(sK2,sK3)))
    | ~ spl7_3
    | ~ spl7_61
    | ~ spl7_118
    | ~ spl7_119 ),
    inference(unit_resulting_resolution,[],[f7092,f3447,f7887,f183])).

fof(f183,plain,
    ( ! [X2,X0,X1] :
        ( r2_lattice3(sK2,k2_xboole_0(X2,X0),X1)
        | ~ r2_lattice3(sK2,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r2_lattice3(sK2,X0,X1) )
    | ~ spl7_3 ),
    inference(resolution,[],[f56,f100])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_lattice3(X0,X2,X3)
      | ~ r2_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r2_lattice3(X0,k2_xboole_0(X1,X2),X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2,X3] :
          ( ( ( r2_lattice3(X0,k2_xboole_0(X1,X2),X3)
              | ~ r2_lattice3(X0,X2,X3)
              | ~ r2_lattice3(X0,X1,X3) )
            & ( r1_lattice3(X0,k2_xboole_0(X1,X2),X3)
              | ~ r1_lattice3(X0,X2,X3)
              | ~ r1_lattice3(X0,X1,X3) ) )
          | ~ m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2,X3] :
          ( ( ( r2_lattice3(X0,k2_xboole_0(X1,X2),X3)
              | ~ r2_lattice3(X0,X2,X3)
              | ~ r2_lattice3(X0,X1,X3) )
            & ( r1_lattice3(X0,k2_xboole_0(X1,X2),X3)
              | ~ r1_lattice3(X0,X2,X3)
              | ~ r1_lattice3(X0,X1,X3) ) )
          | ~ m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X0))
         => ( ( ( r2_lattice3(X0,X2,X3)
                & r2_lattice3(X0,X1,X3) )
             => r2_lattice3(X0,k2_xboole_0(X1,X2),X3) )
            & ( ( r1_lattice3(X0,X2,X3)
                & r1_lattice3(X0,X1,X3) )
             => r1_lattice3(X0,k2_xboole_0(X1,X2),X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_yellow_0)).

fof(f7887,plain,
    ( r2_lattice3(sK2,sK3,sK6(k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k1_yellow_0(sK2,sK4),k1_yellow_0(sK2,sK3)))
    | ~ spl7_119 ),
    inference(avatar_component_clause,[],[f7885])).

fof(f7885,plain,
    ( spl7_119
  <=> r2_lattice3(sK2,sK3,sK6(k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k1_yellow_0(sK2,sK4),k1_yellow_0(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_119])])).

fof(f7092,plain,
    ( r2_lattice3(sK2,sK4,sK6(k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k1_yellow_0(sK2,sK4),k1_yellow_0(sK2,sK3)))
    | ~ spl7_118 ),
    inference(avatar_component_clause,[],[f7090])).

fof(f7090,plain,
    ( spl7_118
  <=> r2_lattice3(sK2,sK4,sK6(k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k1_yellow_0(sK2,sK4),k1_yellow_0(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_118])])).

fof(f7905,plain,
    ( ~ spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | spl7_7
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_61
    | ~ spl7_118
    | ~ spl7_119 ),
    inference(avatar_contradiction_clause,[],[f7904])).

fof(f7904,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | spl7_7
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_61
    | ~ spl7_118
    | ~ spl7_119 ),
    inference(subsumption_resolution,[],[f7891,f5329])).

fof(f7891,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,sK4),sK6(k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k1_yellow_0(sK2,sK4),k1_yellow_0(sK2,sK3)))
    | ~ spl7_3
    | ~ spl7_61
    | ~ spl7_118
    | ~ spl7_119 ),
    inference(unit_resulting_resolution,[],[f7092,f3447,f7887,f183])).

fof(f7903,plain,
    ( ~ spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | spl7_7
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_61
    | ~ spl7_118
    | ~ spl7_119 ),
    inference(avatar_contradiction_clause,[],[f7902])).

fof(f7902,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | spl7_7
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_61
    | ~ spl7_118
    | ~ spl7_119 ),
    inference(subsumption_resolution,[],[f7894,f5329])).

fof(f7894,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,sK4),sK6(k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k1_yellow_0(sK2,sK4),k1_yellow_0(sK2,sK3)))
    | ~ spl7_3
    | ~ spl7_61
    | ~ spl7_118
    | ~ spl7_119 ),
    inference(unit_resulting_resolution,[],[f100,f7092,f3447,f7887,f56])).

fof(f7901,plain,
    ( ~ spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | spl7_7
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_61
    | ~ spl7_118
    | ~ spl7_119 ),
    inference(avatar_contradiction_clause,[],[f7900])).

fof(f7900,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | spl7_7
    | ~ spl7_10
    | ~ spl7_11
    | ~ spl7_61
    | ~ spl7_118
    | ~ spl7_119 ),
    inference(subsumption_resolution,[],[f7899,f5329])).

fof(f7899,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,sK4),sK6(k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k1_yellow_0(sK2,sK4),k1_yellow_0(sK2,sK3)))
    | ~ spl7_3
    | ~ spl7_61
    | ~ spl7_118
    | ~ spl7_119 ),
    inference(forward_demodulation,[],[f7896,f79])).

fof(f7896,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,sK3),sK6(k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k1_yellow_0(sK2,sK4),k1_yellow_0(sK2,sK3)))
    | ~ spl7_3
    | ~ spl7_61
    | ~ spl7_118
    | ~ spl7_119 ),
    inference(unit_resulting_resolution,[],[f100,f7092,f3447,f7887,f56])).

fof(f7888,plain,
    ( spl7_119
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_61
    | ~ spl7_109 ),
    inference(avatar_split_clause,[],[f7871,f5735,f3445,f156,f98,f88,f7885])).

fof(f88,plain,
    ( spl7_1
  <=> v4_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f156,plain,
    ( spl7_8
  <=> r2_lattice3(sK2,sK3,k1_yellow_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f5735,plain,
    ( spl7_109
  <=> r1_orders_2(sK2,k1_yellow_0(sK2,sK3),sK6(k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k1_yellow_0(sK2,sK4),k1_yellow_0(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_109])])).

fof(f7871,plain,
    ( r2_lattice3(sK2,sK3,sK6(k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k1_yellow_0(sK2,sK4),k1_yellow_0(sK2,sK3)))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_61
    | ~ spl7_109 ),
    inference(unit_resulting_resolution,[],[f90,f100,f158,f121,f3447,f5737,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,X3,X2)
      | ~ r2_lattice3(X0,X3,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_lattice3(X0,X3,X2)
                    | ~ r2_lattice3(X0,X3,X1) )
                  & ( r1_lattice3(X0,X3,X1)
                    | ~ r1_lattice3(X0,X3,X2) ) )
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_lattice3(X0,X3,X2)
                    | ~ r2_lattice3(X0,X3,X1) )
                  & ( r1_lattice3(X0,X3,X1)
                    | ~ r1_lattice3(X0,X3,X2) ) )
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
               => ! [X3] :
                    ( ( r2_lattice3(X0,X3,X1)
                     => r2_lattice3(X0,X3,X2) )
                    & ( r1_lattice3(X0,X3,X2)
                     => r1_lattice3(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_0)).

fof(f5737,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,sK3),sK6(k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k1_yellow_0(sK2,sK4),k1_yellow_0(sK2,sK3)))
    | ~ spl7_109 ),
    inference(avatar_component_clause,[],[f5735])).

fof(f158,plain,
    ( r2_lattice3(sK2,sK3,k1_yellow_0(sK2,sK3))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f156])).

fof(f90,plain,
    ( v4_orders_2(sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f7093,plain,
    ( spl7_118
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_61
    | ~ spl7_103 ),
    inference(avatar_split_clause,[],[f7077,f5705,f3445,f161,f98,f88,f7090])).

fof(f161,plain,
    ( spl7_9
  <=> r2_lattice3(sK2,sK4,k1_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f5705,plain,
    ( spl7_103
  <=> r1_orders_2(sK2,k1_yellow_0(sK2,sK4),sK6(k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k1_yellow_0(sK2,sK4),k1_yellow_0(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_103])])).

fof(f7077,plain,
    ( r2_lattice3(sK2,sK4,sK6(k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k1_yellow_0(sK2,sK4),k1_yellow_0(sK2,sK3)))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_61
    | ~ spl7_103 ),
    inference(unit_resulting_resolution,[],[f90,f100,f163,f121,f3447,f5707,f58])).

fof(f5707,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,sK4),sK6(k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k1_yellow_0(sK2,sK4),k1_yellow_0(sK2,sK3)))
    | ~ spl7_103 ),
    inference(avatar_component_clause,[],[f5705])).

fof(f163,plain,
    ( r2_lattice3(sK2,sK4,k1_yellow_0(sK2,sK4))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f161])).

fof(f5778,plain,
    ( spl7_117
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_48 ),
    inference(avatar_split_clause,[],[f2000,f797,f403,f98,f5775])).

fof(f5775,plain,
    ( spl7_117
  <=> r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK3,sK4)))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_117])])).

fof(f403,plain,
    ( spl7_27
  <=> r2_lattice3(sK2,sK4,k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f797,plain,
    ( spl7_48
  <=> r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK3,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f2000,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK3,sK4)))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_48 ),
    inference(unit_resulting_resolution,[],[f100,f405,f121,f799,f56])).

fof(f799,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK3,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_48 ),
    inference(avatar_component_clause,[],[f797])).

fof(f405,plain,
    ( r2_lattice3(sK2,sK4,k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f403])).

fof(f5773,plain,
    ( spl7_116
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_48 ),
    inference(avatar_split_clause,[],[f1999,f797,f398,f98,f5770])).

fof(f5770,plain,
    ( spl7_116
  <=> r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK3,sK4)))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_116])])).

fof(f398,plain,
    ( spl7_26
  <=> r2_lattice3(sK2,sK3,k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f1999,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK3,sK4)))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_48 ),
    inference(unit_resulting_resolution,[],[f100,f400,f121,f799,f56])).

fof(f400,plain,
    ( r2_lattice3(sK2,sK3,k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f398])).

fof(f5768,plain,
    ( spl7_115
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f3960,f499,f98,f93,f5765])).

fof(f5765,plain,
    ( spl7_115
  <=> k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)) = k10_lattice3(sK2,k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_115])])).

fof(f499,plain,
    ( spl7_32
  <=> r1_orders_2(sK2,k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f3960,plain,
    ( k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)) = k10_lattice3(sK2,k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f121,f501,f501,f121,f3458])).

fof(f3458,plain,
    ( ! [X8,X7] :
        ( ~ r1_orders_2(sK2,X7,X7)
        | ~ m1_subset_1(X7,u1_struct_0(sK2))
        | ~ m1_subset_1(X8,u1_struct_0(sK2))
        | k10_lattice3(sK2,X7,X8) = X7
        | ~ r1_orders_2(sK2,X8,X7) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f3455,f678])).

fof(f3455,plain,
    ( ! [X8,X7] :
        ( ~ r1_orders_2(sK2,X7,X7)
        | ~ m1_subset_1(X7,u1_struct_0(sK2))
        | ~ m1_subset_1(X8,u1_struct_0(sK2))
        | k10_lattice3(sK2,X7,X8) = X7
        | ~ r1_orders_2(sK2,X8,X7)
        | ~ sP1(X7,sK2,X8,X7) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(duplicate_literal_removal,[],[f3452])).

fof(f3452,plain,
    ( ! [X8,X7] :
        ( ~ r1_orders_2(sK2,X7,X7)
        | ~ m1_subset_1(X7,u1_struct_0(sK2))
        | ~ m1_subset_1(X8,u1_struct_0(sK2))
        | ~ m1_subset_1(X7,u1_struct_0(sK2))
        | k10_lattice3(sK2,X7,X8) = X7
        | ~ r1_orders_2(sK2,X8,X7)
        | ~ sP1(X7,sK2,X8,X7) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f2077,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X1,X3,sK6(X0,X1,X2,X3))
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f501,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f499])).

fof(f5763,plain,
    ( spl7_114
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_47 ),
    inference(avatar_split_clause,[],[f1878,f792,f403,f98,f5760])).

fof(f5760,plain,
    ( spl7_114
  <=> r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK4,k2_xboole_0(sK3,sK4)))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_114])])).

fof(f792,plain,
    ( spl7_47
  <=> r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK4,k2_xboole_0(sK3,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f1878,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK4,k2_xboole_0(sK3,sK4)))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_47 ),
    inference(unit_resulting_resolution,[],[f100,f405,f121,f794,f56])).

fof(f794,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK4,k2_xboole_0(sK3,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_47 ),
    inference(avatar_component_clause,[],[f792])).

fof(f5758,plain,
    ( spl7_113
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_47 ),
    inference(avatar_split_clause,[],[f1877,f792,f398,f98,f5755])).

fof(f5755,plain,
    ( spl7_113
  <=> r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK4,k2_xboole_0(sK3,sK4)))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_113])])).

fof(f1877,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK4,k2_xboole_0(sK3,sK4)))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_47 ),
    inference(unit_resulting_resolution,[],[f100,f400,f121,f794,f56])).

fof(f5753,plain,
    ( spl7_112
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_46 ),
    inference(avatar_split_clause,[],[f1761,f787,f403,f98,f5750])).

fof(f5750,plain,
    ( spl7_112
  <=> r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK3,sK4)))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_112])])).

fof(f787,plain,
    ( spl7_46
  <=> r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK3,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f1761,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK3,sK4)))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_46 ),
    inference(unit_resulting_resolution,[],[f100,f405,f121,f789,f56])).

fof(f789,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK3,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f787])).

fof(f5748,plain,
    ( spl7_111
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_46 ),
    inference(avatar_split_clause,[],[f1760,f787,f398,f98,f5745])).

fof(f5745,plain,
    ( spl7_111
  <=> r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK3,sK4)))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_111])])).

fof(f1760,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK3,sK4)))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_46 ),
    inference(unit_resulting_resolution,[],[f100,f400,f121,f789,f56])).

fof(f5743,plain,
    ( spl7_110
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_45 ),
    inference(avatar_split_clause,[],[f1651,f775,f403,f98,f5740])).

fof(f5740,plain,
    ( spl7_110
  <=> r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,sK4)))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_110])])).

fof(f775,plain,
    ( spl7_45
  <=> r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f1651,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,sK4)))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_45 ),
    inference(unit_resulting_resolution,[],[f100,f405,f121,f777,f56])).

fof(f777,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_45 ),
    inference(avatar_component_clause,[],[f775])).

fof(f5738,plain,
    ( spl7_109
    | ~ spl7_39 ),
    inference(avatar_split_clause,[],[f722,f716,f5735])).

fof(f716,plain,
    ( spl7_39
  <=> sP1(k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k1_yellow_0(sK2,sK4),k1_yellow_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f722,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,sK3),sK6(k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k1_yellow_0(sK2,sK4),k1_yellow_0(sK2,sK3)))
    | ~ spl7_39 ),
    inference(unit_resulting_resolution,[],[f718,f69])).

fof(f718,plain,
    ( sP1(k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k1_yellow_0(sK2,sK4),k1_yellow_0(sK2,sK3))
    | ~ spl7_39 ),
    inference(avatar_component_clause,[],[f716])).

fof(f5733,plain,
    ( spl7_108
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_45 ),
    inference(avatar_split_clause,[],[f1650,f775,f398,f98,f5730])).

fof(f5730,plain,
    ( spl7_108
  <=> r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,sK4)))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_108])])).

fof(f1650,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,sK4)))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_45 ),
    inference(unit_resulting_resolution,[],[f100,f400,f121,f777,f56])).

fof(f5728,plain,
    ( spl7_107
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f1547,f770,f403,f98,f5725])).

fof(f5725,plain,
    ( spl7_107
  <=> r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_107])])).

fof(f770,plain,
    ( spl7_44
  <=> r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK4,sK4)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f1547,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_44 ),
    inference(unit_resulting_resolution,[],[f100,f405,f121,f772,f56])).

fof(f772,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK4,sK4)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f770])).

fof(f5723,plain,
    ( spl7_106
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f1546,f770,f398,f98,f5720])).

fof(f5720,plain,
    ( spl7_106
  <=> r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_106])])).

fof(f1546,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_44 ),
    inference(unit_resulting_resolution,[],[f100,f400,f121,f772,f56])).

fof(f5718,plain,
    ( spl7_105
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_43 ),
    inference(avatar_split_clause,[],[f1449,f765,f403,f98,f5715])).

fof(f5715,plain,
    ( spl7_105
  <=> r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_105])])).

fof(f765,plain,
    ( spl7_43
  <=> r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK4,sK4)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f1449,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_43 ),
    inference(unit_resulting_resolution,[],[f100,f405,f121,f767,f56])).

fof(f767,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK4,sK4)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_43 ),
    inference(avatar_component_clause,[],[f765])).

fof(f5713,plain,
    ( spl7_104
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_43 ),
    inference(avatar_split_clause,[],[f1448,f765,f398,f98,f5710])).

fof(f5710,plain,
    ( spl7_104
  <=> r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_104])])).

fof(f1448,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_43 ),
    inference(unit_resulting_resolution,[],[f100,f400,f121,f767,f56])).

fof(f5708,plain,
    ( spl7_103
    | ~ spl7_39 ),
    inference(avatar_split_clause,[],[f721,f716,f5705])).

fof(f721,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,sK4),sK6(k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k1_yellow_0(sK2,sK4),k1_yellow_0(sK2,sK3)))
    | ~ spl7_39 ),
    inference(unit_resulting_resolution,[],[f718,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X1,X2,sK6(X0,X1,X2,X3))
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f5703,plain,
    ( spl7_102
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f1357,f760,f403,f98,f5700])).

fof(f5700,plain,
    ( spl7_102
  <=> r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_102])])).

fof(f760,plain,
    ( spl7_42
  <=> r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK4)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f1357,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_42 ),
    inference(unit_resulting_resolution,[],[f100,f405,f121,f762,f56])).

fof(f762,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK4)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f760])).

fof(f5698,plain,
    ( spl7_101
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f1356,f760,f398,f98,f5695])).

fof(f5695,plain,
    ( spl7_101
  <=> r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_101])])).

fof(f1356,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_42 ),
    inference(unit_resulting_resolution,[],[f100,f400,f121,f762,f56])).

fof(f5693,plain,
    ( spl7_100
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_41 ),
    inference(avatar_split_clause,[],[f854,f755,f398,f98,f5690])).

fof(f5690,plain,
    ( spl7_100
  <=> r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_100])])).

fof(f755,plain,
    ( spl7_41
  <=> r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,sK4)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f854,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_41 ),
    inference(unit_resulting_resolution,[],[f100,f400,f121,f757,f56])).

fof(f757,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,sK4)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f755])).

fof(f5688,plain,
    ( spl7_99
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_40 ),
    inference(avatar_split_clause,[],[f815,f748,f403,f98,f5685])).

fof(f5685,plain,
    ( spl7_99
  <=> r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_99])])).

fof(f748,plain,
    ( spl7_40
  <=> r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK3)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f815,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_40 ),
    inference(unit_resulting_resolution,[],[f100,f405,f121,f750,f56])).

fof(f750,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK3)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_40 ),
    inference(avatar_component_clause,[],[f748])).

fof(f5683,plain,
    ( spl7_98
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_11
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f739,f326,f171,f98,f88,f5680])).

fof(f5680,plain,
    ( spl7_98
  <=> r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_98])])).

fof(f326,plain,
    ( spl7_25
  <=> r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f739,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_11
    | ~ spl7_25 ),
    inference(unit_resulting_resolution,[],[f90,f100,f121,f173,f121,f328,f58])).

fof(f328,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,sK4))
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f326])).

fof(f5678,plain,
    ( spl7_97
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f307,f301,f176,f98,f5675])).

fof(f5675,plain,
    ( spl7_97
  <=> r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_97])])).

fof(f176,plain,
    ( spl7_12
  <=> r2_lattice3(sK2,k2_xboole_0(sK3,sK4),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f301,plain,
    ( spl7_21
  <=> r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK4)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f307,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_21 ),
    inference(unit_resulting_resolution,[],[f100,f178,f121,f303,f56])).

fof(f303,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK4)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f301])).

fof(f178,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,sK4),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f176])).

fof(f5673,plain,
    ( spl7_96
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f732,f326,f161,f98,f5670])).

fof(f5670,plain,
    ( spl7_96
  <=> r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,sK4)))),k1_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_96])])).

fof(f732,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,sK4)))),k1_yellow_0(sK2,sK4))
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_25 ),
    inference(unit_resulting_resolution,[],[f100,f163,f121,f328,f56])).

fof(f5668,plain,
    ( spl7_95
    | ~ spl7_3
    | ~ spl7_31
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f698,f582,f463,f98,f5665])).

fof(f5665,plain,
    ( spl7_95
  <=> r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK3,k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_95])])).

fof(f463,plain,
    ( spl7_31
  <=> r2_lattice3(sK2,k2_xboole_0(sK4,sK4),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f582,plain,
    ( spl7_38
  <=> r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK4,sK4)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f698,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK3,k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_31
    | ~ spl7_38 ),
    inference(unit_resulting_resolution,[],[f100,f465,f121,f584,f56])).

fof(f584,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK4,sK4)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f582])).

fof(f465,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,sK4),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f463])).

fof(f5663,plain,
    ( spl7_94
    | ~ spl7_3
    | ~ spl7_28
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f694,f582,f427,f98,f5660])).

fof(f5660,plain,
    ( spl7_94
  <=> r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_94])])).

fof(f427,plain,
    ( spl7_28
  <=> r2_lattice3(sK2,k2_xboole_0(sK3,sK3),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f694,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_28
    | ~ spl7_38 ),
    inference(unit_resulting_resolution,[],[f100,f429,f121,f584,f56])).

fof(f429,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,sK3),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f427])).

fof(f5658,plain,
    ( spl7_93
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f693,f582,f176,f98,f5655])).

fof(f5655,plain,
    ( spl7_93
  <=> r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_93])])).

fof(f693,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_38 ),
    inference(unit_resulting_resolution,[],[f100,f178,f121,f584,f56])).

fof(f5653,plain,
    ( spl7_92
    | ~ spl7_3
    | ~ spl7_31
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f660,f577,f463,f98,f5650])).

fof(f5650,plain,
    ( spl7_92
  <=> r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_92])])).

fof(f577,plain,
    ( spl7_37
  <=> r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK3,sK3)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f660,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_31
    | ~ spl7_37 ),
    inference(unit_resulting_resolution,[],[f100,f465,f121,f579,f56])).

fof(f579,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK3,sK3)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f577])).

fof(f5640,plain,
    ( spl7_91
    | ~ spl7_3
    | ~ spl7_28
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f657,f577,f427,f98,f5637])).

fof(f5637,plain,
    ( spl7_91
  <=> r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK4,k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_91])])).

fof(f657,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK4,k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_28
    | ~ spl7_37 ),
    inference(unit_resulting_resolution,[],[f100,f429,f121,f579,f56])).

fof(f5635,plain,
    ( spl7_90
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f656,f577,f176,f98,f5632])).

fof(f5632,plain,
    ( spl7_90
  <=> r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK4,k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_90])])).

fof(f656,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK4,k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_37 ),
    inference(unit_resulting_resolution,[],[f100,f178,f121,f579,f56])).

fof(f5630,plain,
    ( spl7_89
    | ~ spl7_3
    | ~ spl7_28
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f626,f570,f427,f98,f5627])).

fof(f5627,plain,
    ( spl7_89
  <=> r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK4,k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_89])])).

fof(f570,plain,
    ( spl7_36
  <=> r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,sK4)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f626,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK4,k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_28
    | ~ spl7_36 ),
    inference(unit_resulting_resolution,[],[f100,f429,f121,f572,f56])).

fof(f572,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,sK4)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f570])).

fof(f5625,plain,
    ( spl7_88
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f625,f570,f176,f98,f5622])).

fof(f5622,plain,
    ( spl7_88
  <=> r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK4,k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_88])])).

fof(f625,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK4,k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_36 ),
    inference(unit_resulting_resolution,[],[f100,f178,f121,f572,f56])).

fof(f5620,plain,
    ( spl7_87
    | ~ spl7_3
    | ~ spl7_31
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f601,f565,f463,f98,f5617])).

fof(f5617,plain,
    ( spl7_87
  <=> r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK3,k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_87])])).

fof(f565,plain,
    ( spl7_35
  <=> r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,sK3)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f601,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK3,k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_31
    | ~ spl7_35 ),
    inference(unit_resulting_resolution,[],[f100,f465,f121,f567,f56])).

fof(f567,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,sK3)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f565])).

fof(f5607,plain,
    ( spl7_86
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f597,f565,f176,f98,f5604])).

fof(f5604,plain,
    ( spl7_86
  <=> r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_86])])).

fof(f597,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_35 ),
    inference(unit_resulting_resolution,[],[f100,f178,f121,f567,f56])).

fof(f5602,plain,
    ( spl7_85
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_11
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f396,f316,f171,f98,f88,f5599])).

fof(f5599,plain,
    ( spl7_85
  <=> r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_85])])).

fof(f316,plain,
    ( spl7_23
  <=> r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f396,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_11
    | ~ spl7_23 ),
    inference(unit_resulting_resolution,[],[f90,f100,f318,f121,f173,f121,f58])).

fof(f318,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,sK4))
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f316])).

fof(f5597,plain,
    ( spl7_84
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f390,f311,f166,f98,f88,f5594])).

fof(f5594,plain,
    ( spl7_84
  <=> r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_84])])).

fof(f311,plain,
    ( spl7_22
  <=> r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f390,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_22 ),
    inference(unit_resulting_resolution,[],[f90,f100,f313,f121,f168,f121,f58])).

fof(f313,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,sK3))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f311])).

fof(f5592,plain,
    ( spl7_83
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f388,f321,f166,f98,f88,f5589])).

fof(f5589,plain,
    ( spl7_83
  <=> r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_83])])).

fof(f321,plain,
    ( spl7_24
  <=> r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f388,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_24 ),
    inference(unit_resulting_resolution,[],[f90,f100,f323,f121,f168,f121,f58])).

fof(f323,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,sK3))
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f321])).

fof(f5587,plain,
    ( spl7_82
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f371,f321,f156,f98,f5584])).

fof(f5584,plain,
    ( spl7_82
  <=> r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK3)))),k1_yellow_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_82])])).

fof(f371,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK3)))),k1_yellow_0(sK2,sK3))
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_24 ),
    inference(unit_resulting_resolution,[],[f100,f158,f121,f323,f56])).

fof(f5572,plain,
    ( spl7_81
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f353,f316,f161,f98,f5569])).

fof(f5569,plain,
    ( spl7_81
  <=> r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,k2_xboole_0(sK4,sK4)))),k1_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_81])])).

fof(f353,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,k2_xboole_0(sK4,sK4)))),k1_yellow_0(sK2,sK4))
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_23 ),
    inference(unit_resulting_resolution,[],[f100,f163,f121,f318,f56])).

fof(f5567,plain,
    ( spl7_80
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f336,f311,f156,f98,f5564])).

fof(f5564,plain,
    ( spl7_80
  <=> r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,k2_xboole_0(sK3,sK3)))),k1_yellow_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_80])])).

fof(f336,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,k2_xboole_0(sK3,sK3)))),k1_yellow_0(sK2,sK3))
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_22 ),
    inference(unit_resulting_resolution,[],[f100,f158,f121,f313,f56])).

fof(f5562,plain,
    ( spl7_79
    | ~ spl7_3
    | ~ spl7_14
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f292,f268,f190,f98,f5559])).

fof(f5559,plain,
    ( spl7_79
  <=> r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK4,sK4)))),k1_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_79])])).

fof(f190,plain,
    ( spl7_14
  <=> r2_lattice3(sK2,k2_xboole_0(sK4,sK4),k1_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f268,plain,
    ( spl7_20
  <=> r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f292,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK4,sK4)))),k1_yellow_0(sK2,sK4))
    | ~ spl7_3
    | ~ spl7_14
    | ~ spl7_20 ),
    inference(unit_resulting_resolution,[],[f100,f192,f121,f270,f56])).

fof(f270,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,sK4))
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f268])).

fof(f192,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,sK4),k1_yellow_0(sK2,sK4))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f190])).

fof(f5557,plain,
    ( spl7_78
    | ~ spl7_3
    | ~ spl7_13
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f278,f263,f185,f98,f5554])).

fof(f5554,plain,
    ( spl7_78
  <=> r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,sK3)))),k1_yellow_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).

fof(f185,plain,
    ( spl7_13
  <=> r2_lattice3(sK2,k2_xboole_0(sK3,sK3),k1_yellow_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f263,plain,
    ( spl7_19
  <=> r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f278,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,sK3)))),k1_yellow_0(sK2,sK3))
    | ~ spl7_3
    | ~ spl7_13
    | ~ spl7_19 ),
    inference(unit_resulting_resolution,[],[f100,f187,f121,f265,f56])).

fof(f265,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,sK3))
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f263])).

fof(f187,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,sK3),k1_yellow_0(sK2,sK3))
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f185])).

fof(f4080,plain,
    ( spl7_77
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_11
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f4030,f499,f171,f98,f93,f4077])).

fof(f4077,plain,
    ( spl7_77
  <=> k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)) = k10_lattice3(sK2,k1_yellow_0(sK2,sK4),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_77])])).

fof(f4030,plain,
    ( k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)) = k10_lattice3(sK2,k1_yellow_0(sK2,sK4),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_11
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f121,f173,f501,f121,f3459])).

fof(f3459,plain,
    ( ! [X10,X9] :
        ( ~ r1_orders_2(sK2,X10,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK2))
        | ~ m1_subset_1(X9,u1_struct_0(sK2))
        | k10_lattice3(sK2,X9,X10) = X10
        | ~ r1_orders_2(sK2,X9,X10) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f3454,f678])).

fof(f3454,plain,
    ( ! [X10,X9] :
        ( ~ r1_orders_2(sK2,X9,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK2))
        | ~ m1_subset_1(X9,u1_struct_0(sK2))
        | k10_lattice3(sK2,X9,X10) = X10
        | ~ r1_orders_2(sK2,X10,X10)
        | ~ sP1(X10,sK2,X10,X9) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(duplicate_literal_removal,[],[f3453])).

fof(f3453,plain,
    ( ! [X10,X9] :
        ( ~ r1_orders_2(sK2,X9,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK2))
        | ~ m1_subset_1(X10,u1_struct_0(sK2))
        | ~ m1_subset_1(X9,u1_struct_0(sK2))
        | k10_lattice3(sK2,X9,X10) = X10
        | ~ r1_orders_2(sK2,X10,X10)
        | ~ sP1(X10,sK2,X10,X9) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f2077,f70])).

fof(f4075,plain,
    ( spl7_76
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f4029,f499,f166,f98,f93,f4072])).

fof(f4072,plain,
    ( spl7_76
  <=> k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)) = k10_lattice3(sK2,k1_yellow_0(sK2,sK3),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_76])])).

fof(f4029,plain,
    ( k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)) = k10_lattice3(sK2,k1_yellow_0(sK2,sK3),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f121,f168,f501,f121,f3459])).

fof(f4053,plain,
    ( spl7_75
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_11
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f3959,f499,f171,f98,f93,f4050])).

fof(f4050,plain,
    ( spl7_75
  <=> k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)) = k10_lattice3(sK2,k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)),k1_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).

fof(f3959,plain,
    ( k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)) = k10_lattice3(sK2,k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)),k1_yellow_0(sK2,sK4))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_11
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f121,f173,f501,f121,f3458])).

fof(f4028,plain,
    ( spl7_74
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f3958,f499,f166,f98,f93,f4025])).

fof(f4025,plain,
    ( spl7_74
  <=> k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)) = k10_lattice3(sK2,k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)),k1_yellow_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_74])])).

fof(f3958,plain,
    ( k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)) = k10_lattice3(sK2,k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)),k1_yellow_0(sK2,sK3))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f121,f168,f501,f121,f3458])).

fof(f3987,plain,
    ( spl7_73
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f3962,f445,f98,f93,f3984])).

fof(f3984,plain,
    ( spl7_73
  <=> k1_yellow_0(sK2,sK4) = k10_lattice3(sK2,k1_yellow_0(sK2,sK4),k1_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_73])])).

fof(f445,plain,
    ( spl7_30
  <=> r1_orders_2(sK2,k1_yellow_0(sK2,sK4),k1_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f3962,plain,
    ( k1_yellow_0(sK2,sK4) = k10_lattice3(sK2,k1_yellow_0(sK2,sK4),k1_yellow_0(sK2,sK4))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_30 ),
    inference(unit_resulting_resolution,[],[f121,f447,f447,f121,f3458])).

fof(f447,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,sK4),k1_yellow_0(sK2,sK4))
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f445])).

fof(f3982,plain,
    ( spl7_72
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_29 ),
    inference(avatar_split_clause,[],[f3961,f440,f98,f93,f3979])).

fof(f3979,plain,
    ( spl7_72
  <=> k1_yellow_0(sK2,sK3) = k10_lattice3(sK2,k1_yellow_0(sK2,sK3),k1_yellow_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).

fof(f440,plain,
    ( spl7_29
  <=> r1_orders_2(sK2,k1_yellow_0(sK2,sK3),k1_yellow_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f3961,plain,
    ( k1_yellow_0(sK2,sK3) = k10_lattice3(sK2,k1_yellow_0(sK2,sK3),k1_yellow_0(sK2,sK3))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_29 ),
    inference(unit_resulting_resolution,[],[f121,f442,f442,f121,f3458])).

fof(f442,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,sK3),k1_yellow_0(sK2,sK3))
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f440])).

fof(f3903,plain,
    ( spl7_71
    | ~ spl7_3
    | ~ spl7_31
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f553,f515,f463,f98,f3900])).

fof(f3900,plain,
    ( spl7_71
  <=> r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,k2_xboole_0(sK3,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_71])])).

fof(f515,plain,
    ( spl7_34
  <=> r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK3,sK4)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f553,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,k2_xboole_0(sK3,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_31
    | ~ spl7_34 ),
    inference(unit_resulting_resolution,[],[f100,f465,f121,f517,f56])).

fof(f517,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK3,sK4)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f515])).

fof(f3898,plain,
    ( spl7_70
    | ~ spl7_3
    | ~ spl7_28
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f551,f515,f427,f98,f3895])).

fof(f3895,plain,
    ( spl7_70
  <=> r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK4,k2_xboole_0(sK3,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).

fof(f551,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK4,k2_xboole_0(sK3,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_28
    | ~ spl7_34 ),
    inference(unit_resulting_resolution,[],[f100,f429,f121,f517,f56])).

fof(f3893,plain,
    ( spl7_69
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f550,f515,f176,f98,f3890])).

fof(f3890,plain,
    ( spl7_69
  <=> r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK4,k2_xboole_0(sK3,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_69])])).

fof(f550,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK4,k2_xboole_0(sK3,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_34 ),
    inference(unit_resulting_resolution,[],[f100,f178,f121,f517,f56])).

fof(f3875,plain,
    ( spl7_68
    | ~ spl7_3
    | ~ spl7_31
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f531,f510,f463,f98,f3872])).

fof(f3872,plain,
    ( spl7_68
  <=> r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK3,k2_xboole_0(sK3,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).

fof(f510,plain,
    ( spl7_33
  <=> r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,sK4)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f531,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK3,k2_xboole_0(sK3,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_31
    | ~ spl7_33 ),
    inference(unit_resulting_resolution,[],[f100,f465,f121,f512,f56])).

fof(f512,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,sK4)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f510])).

fof(f3870,plain,
    ( spl7_67
    | ~ spl7_3
    | ~ spl7_28
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f529,f510,f427,f98,f3867])).

fof(f3867,plain,
    ( spl7_67
  <=> r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,k2_xboole_0(sK3,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).

fof(f529,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,k2_xboole_0(sK3,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_28
    | ~ spl7_33 ),
    inference(unit_resulting_resolution,[],[f100,f429,f121,f512,f56])).

fof(f3865,plain,
    ( spl7_66
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f528,f510,f176,f98,f3862])).

fof(f3862,plain,
    ( spl7_66
  <=> r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,k2_xboole_0(sK3,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).

fof(f528,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,k2_xboole_0(sK3,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_33 ),
    inference(unit_resulting_resolution,[],[f100,f178,f121,f512,f56])).

fof(f3860,plain,
    ( spl7_65
    | ~ spl7_3
    | ~ spl7_14
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f256,f236,f190,f98,f3857])).

fof(f3857,plain,
    ( spl7_65
  <=> r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).

fof(f236,plain,
    ( spl7_18
  <=> r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,sK4)),k1_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f256,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,sK4))
    | ~ spl7_3
    | ~ spl7_14
    | ~ spl7_18 ),
    inference(unit_resulting_resolution,[],[f100,f192,f121,f238,f56])).

fof(f238,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,sK4)),k1_yellow_0(sK2,sK4))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f236])).

fof(f3855,plain,
    ( spl7_64
    | ~ spl7_3
    | ~ spl7_13
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f245,f231,f185,f98,f3852])).

fof(f3852,plain,
    ( spl7_64
  <=> r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f231,plain,
    ( spl7_17
  <=> r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK3)),k1_yellow_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f245,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,sK3))
    | ~ spl7_3
    | ~ spl7_13
    | ~ spl7_17 ),
    inference(unit_resulting_resolution,[],[f100,f187,f121,f233,f56])).

fof(f233,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK3)),k1_yellow_0(sK2,sK3))
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f231])).

fof(f3844,plain,
    ( spl7_63
    | ~ spl7_3
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f227,f210,f98,f3841])).

fof(f3841,plain,
    ( spl7_63
  <=> r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,k2_xboole_0(sK4,sK4)),k2_xboole_0(sK4,k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).

fof(f210,plain,
    ( spl7_16
  <=> r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,sK4)),k1_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f227,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,k2_xboole_0(sK4,sK4)),k2_xboole_0(sK4,k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,sK4))
    | ~ spl7_3
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f100,f212,f121,f212,f56])).

fof(f212,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,sK4)),k1_yellow_0(sK2,sK4))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f210])).

fof(f3839,plain,
    ( spl7_62
    | ~ spl7_3
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f219,f205,f98,f3836])).

fof(f3836,plain,
    ( spl7_62
  <=> r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK3,sK3)),k2_xboole_0(sK3,k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f205,plain,
    ( spl7_15
  <=> r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,sK3)),k1_yellow_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f219,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK3,sK3)),k2_xboole_0(sK3,k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,sK3))
    | ~ spl7_3
    | ~ spl7_15 ),
    inference(unit_resulting_resolution,[],[f100,f207,f121,f207,f56])).

fof(f207,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,sK3)),k1_yellow_0(sK2,sK3))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f205])).

fof(f3448,plain,
    ( spl7_61
    | ~ spl7_39 ),
    inference(avatar_split_clause,[],[f723,f716,f3445])).

fof(f723,plain,
    ( m1_subset_1(sK6(k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k1_yellow_0(sK2,sK4),k1_yellow_0(sK2,sK3)),u1_struct_0(sK2))
    | ~ spl7_39 ),
    inference(unit_resulting_resolution,[],[f718,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f3443,plain,
    ( spl7_60
    | ~ spl7_3
    | ~ spl7_21
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f423,f403,f301,f98,f3440])).

fof(f3440,plain,
    ( spl7_60
  <=> r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f423,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_21
    | ~ spl7_27 ),
    inference(forward_demodulation,[],[f422,f79])).

fof(f422,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK4)),sK4),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_21
    | ~ spl7_27 ),
    inference(unit_resulting_resolution,[],[f100,f303,f121,f405,f56])).

fof(f3438,plain,
    ( spl7_59
    | ~ spl7_3
    | ~ spl7_21
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f413,f398,f301,f98,f3435])).

fof(f3435,plain,
    ( spl7_59
  <=> r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).

fof(f413,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_21
    | ~ spl7_26 ),
    inference(forward_demodulation,[],[f412,f79])).

fof(f412,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK4)),sK3),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_21
    | ~ spl7_26 ),
    inference(unit_resulting_resolution,[],[f100,f303,f121,f400,f56])).

fof(f2114,plain,
    ( spl7_58
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f692,f582,f403,f98,f2111])).

fof(f2111,plain,
    ( spl7_58
  <=> r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).

fof(f692,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_38 ),
    inference(unit_resulting_resolution,[],[f100,f405,f121,f584,f56])).

fof(f2109,plain,
    ( spl7_57
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f691,f582,f398,f98,f2106])).

fof(f2106,plain,
    ( spl7_57
  <=> r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).

fof(f691,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_38 ),
    inference(unit_resulting_resolution,[],[f100,f400,f121,f584,f56])).

fof(f2102,plain,
    ( spl7_56
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f655,f577,f403,f98,f2099])).

fof(f2099,plain,
    ( spl7_56
  <=> r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f655,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_37 ),
    inference(unit_resulting_resolution,[],[f100,f405,f121,f579,f56])).

fof(f2097,plain,
    ( spl7_55
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f654,f577,f398,f98,f2094])).

fof(f2094,plain,
    ( spl7_55
  <=> r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK4,k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).

fof(f654,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK4,k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_37 ),
    inference(unit_resulting_resolution,[],[f100,f400,f121,f579,f56])).

fof(f2092,plain,
    ( spl7_54
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f623,f570,f398,f98,f2089])).

fof(f2089,plain,
    ( spl7_54
  <=> r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK4,k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).

fof(f623,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK4,k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_36 ),
    inference(unit_resulting_resolution,[],[f100,f400,f121,f572,f56])).

fof(f2087,plain,
    ( spl7_53
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f596,f565,f403,f98,f2084])).

fof(f2084,plain,
    ( spl7_53
  <=> r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f596,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_35 ),
    inference(unit_resulting_resolution,[],[f100,f405,f121,f567,f56])).

fof(f2082,plain,
    ( spl7_52
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_11
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f394,f268,f171,f98,f88,f2079])).

fof(f2079,plain,
    ( spl7_52
  <=> r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f394,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_11
    | ~ spl7_20 ),
    inference(unit_resulting_resolution,[],[f90,f100,f270,f121,f173,f121,f58])).

fof(f2075,plain,
    ( spl7_51
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f387,f263,f166,f98,f88,f2072])).

fof(f2072,plain,
    ( spl7_51
  <=> r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).

fof(f387,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_19 ),
    inference(unit_resulting_resolution,[],[f90,f100,f265,f121,f168,f121,f58])).

fof(f2070,plain,
    ( spl7_50
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f291,f268,f161,f98,f2067])).

fof(f2067,plain,
    ( spl7_50
  <=> r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK4,sK4)))),k1_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f291,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK4,sK4)))),k1_yellow_0(sK2,sK4))
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_20 ),
    inference(unit_resulting_resolution,[],[f100,f163,f121,f270,f56])).

fof(f2065,plain,
    ( spl7_49
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f277,f263,f156,f98,f2062])).

fof(f2062,plain,
    ( spl7_49
  <=> r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,sK3)))),k1_yellow_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).

fof(f277,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,sK3)))),k1_yellow_0(sK2,sK3))
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_19 ),
    inference(unit_resulting_resolution,[],[f100,f158,f121,f265,f56])).

fof(f800,plain,
    ( spl7_48
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f549,f515,f403,f98,f797])).

fof(f549,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK3,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_34 ),
    inference(unit_resulting_resolution,[],[f100,f405,f121,f517,f56])).

fof(f795,plain,
    ( spl7_47
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f548,f515,f398,f98,f792])).

fof(f548,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK4,k2_xboole_0(sK3,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_34 ),
    inference(unit_resulting_resolution,[],[f100,f400,f121,f517,f56])).

fof(f790,plain,
    ( spl7_46
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f527,f510,f403,f98,f787])).

fof(f527,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK3,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_33 ),
    inference(unit_resulting_resolution,[],[f100,f405,f121,f512,f56])).

fof(f778,plain,
    ( spl7_45
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f526,f510,f398,f98,f775])).

fof(f526,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,sK4))),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_33 ),
    inference(unit_resulting_resolution,[],[f100,f400,f121,f512,f56])).

fof(f773,plain,
    ( spl7_44
    | ~ spl7_3
    | ~ spl7_28
    | ~ spl7_31 ),
    inference(avatar_split_clause,[],[f490,f463,f427,f98,f770])).

fof(f490,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK4,sK4)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_28
    | ~ spl7_31 ),
    inference(unit_resulting_resolution,[],[f100,f429,f121,f465,f56])).

fof(f768,plain,
    ( spl7_43
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_31 ),
    inference(avatar_split_clause,[],[f489,f463,f176,f98,f765])).

fof(f489,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK4,sK4)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_31 ),
    inference(unit_resulting_resolution,[],[f100,f178,f121,f465,f56])).

fof(f763,plain,
    ( spl7_42
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f478,f427,f176,f98,f760])).

fof(f478,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK4)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_28 ),
    inference(forward_demodulation,[],[f474,f79])).

fof(f474,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK3)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_28 ),
    inference(unit_resulting_resolution,[],[f100,f178,f121,f429,f56])).

fof(f758,plain,
    ( spl7_41
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_11
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f395,f236,f171,f98,f88,f755])).

fof(f395,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,sK4)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_11
    | ~ spl7_18 ),
    inference(unit_resulting_resolution,[],[f90,f100,f238,f121,f173,f121,f58])).

fof(f751,plain,
    ( spl7_40
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f389,f231,f166,f98,f88,f748])).

fof(f389,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK3)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_17 ),
    inference(unit_resulting_resolution,[],[f90,f100,f233,f121,f168,f121,f58])).

fof(f719,plain,
    ( spl7_39
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f676,f171,f166,f124,f98,f93,f716])).

fof(f676,plain,
    ( sP1(k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k1_yellow_0(sK2,sK4),k1_yellow_0(sK2,sK3))
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(unit_resulting_resolution,[],[f95,f100,f121,f121,f173,f168,f126,f121,f75])).

fof(f585,plain,
    ( spl7_38
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_31 ),
    inference(avatar_split_clause,[],[f487,f463,f398,f98,f582])).

fof(f487,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK4,sK4)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_31 ),
    inference(unit_resulting_resolution,[],[f100,f400,f121,f465,f56])).

fof(f580,plain,
    ( spl7_37
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f473,f427,f403,f98,f577])).

fof(f473,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK3,sK3)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_28 ),
    inference(unit_resulting_resolution,[],[f100,f405,f121,f429,f56])).

fof(f573,plain,
    ( spl7_36
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_11
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f393,f210,f171,f98,f88,f570])).

fof(f393,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,sK4)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_11
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f90,f100,f212,f121,f173,f121,f58])).

fof(f568,plain,
    ( spl7_35
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f386,f205,f166,f98,f88,f565])).

fof(f386,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,sK3)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_15 ),
    inference(unit_resulting_resolution,[],[f90,f100,f207,f121,f168,f121,f58])).

fof(f518,plain,
    ( spl7_34
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f424,f403,f176,f98,f515])).

fof(f424,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK3,sK4)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_27 ),
    inference(forward_demodulation,[],[f421,f79])).

fof(f421,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),sK4),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_27 ),
    inference(unit_resulting_resolution,[],[f100,f178,f121,f405,f56])).

fof(f513,plain,
    ( spl7_33
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f414,f398,f176,f98,f510])).

fof(f414,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,sK4)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_26 ),
    inference(forward_demodulation,[],[f411,f79])).

fof(f411,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),sK3),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_26 ),
    inference(unit_resulting_resolution,[],[f100,f178,f121,f400,f56])).

fof(f502,plain,
    ( spl7_32
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f435,f176,f113,f98,f93,f499])).

fof(f435,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f95,f100,f115,f178,f121,f121,f82])).

fof(f466,plain,
    ( spl7_31
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_11
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f392,f190,f171,f98,f88,f463])).

fof(f392,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,sK4),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_11
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f90,f100,f192,f121,f173,f121,f58])).

fof(f448,plain,
    ( spl7_30
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f433,f161,f108,f98,f93,f445])).

fof(f108,plain,
    ( spl7_5
  <=> r1_yellow_0(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f433,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,sK4),k1_yellow_0(sK2,sK4))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_9 ),
    inference(unit_resulting_resolution,[],[f95,f100,f110,f163,f121,f121,f82])).

fof(f110,plain,
    ( r1_yellow_0(sK2,sK4)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f108])).

fof(f443,plain,
    ( spl7_29
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f431,f156,f103,f98,f93,f440])).

fof(f103,plain,
    ( spl7_4
  <=> r1_yellow_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f431,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,sK3),k1_yellow_0(sK2,sK3))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f95,f100,f105,f158,f121,f121,f82])).

fof(f105,plain,
    ( r1_yellow_0(sK2,sK3)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f430,plain,
    ( spl7_28
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f385,f185,f166,f98,f88,f427])).

fof(f385,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,sK3),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f90,f100,f187,f121,f168,f121,f58])).

fof(f406,plain,
    ( spl7_27
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f391,f171,f161,f98,f88,f403])).

fof(f391,plain,
    ( r2_lattice3(sK2,sK4,k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_11 ),
    inference(unit_resulting_resolution,[],[f90,f100,f163,f121,f173,f121,f58])).

fof(f401,plain,
    ( spl7_26
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f384,f166,f156,f98,f88,f398])).

fof(f384,plain,
    ( r2_lattice3(sK2,sK3,k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f90,f100,f158,f121,f168,f121,f58])).

fof(f329,plain,
    ( spl7_25
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f255,f236,f161,f98,f326])).

fof(f255,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,sK4))
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_18 ),
    inference(unit_resulting_resolution,[],[f100,f163,f121,f238,f56])).

fof(f324,plain,
    ( spl7_24
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f244,f231,f156,f98,f321])).

fof(f244,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,sK3))
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_17 ),
    inference(unit_resulting_resolution,[],[f100,f158,f121,f233,f56])).

fof(f319,plain,
    ( spl7_23
    | ~ spl7_3
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f226,f210,f190,f98,f316])).

fof(f226,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,sK4))
    | ~ spl7_3
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f100,f192,f121,f212,f56])).

fof(f314,plain,
    ( spl7_22
    | ~ spl7_3
    | ~ spl7_13
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f218,f205,f185,f98,f311])).

fof(f218,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,sK3))
    | ~ spl7_3
    | ~ spl7_13
    | ~ spl7_15 ),
    inference(unit_resulting_resolution,[],[f100,f187,f121,f207,f56])).

fof(f304,plain,
    ( spl7_21
    | ~ spl7_3
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f182,f176,f98,f301])).

fof(f182,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK4)),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f100,f178,f178,f121,f56])).

fof(f271,plain,
    ( spl7_20
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f225,f210,f161,f98,f268])).

fof(f225,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK4,sK4))),k1_yellow_0(sK2,sK4))
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f100,f163,f121,f212,f56])).

fof(f266,plain,
    ( spl7_19
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f217,f205,f156,f98,f263])).

fof(f217,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,sK3))),k1_yellow_0(sK2,sK3))
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_15 ),
    inference(unit_resulting_resolution,[],[f100,f158,f121,f207,f56])).

fof(f239,plain,
    ( spl7_18
    | ~ spl7_3
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f202,f190,f98,f236])).

fof(f202,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,sK4)),k1_yellow_0(sK2,sK4))
    | ~ spl7_3
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f100,f192,f121,f192,f56])).

fof(f234,plain,
    ( spl7_17
    | ~ spl7_3
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f197,f185,f98,f231])).

fof(f197,plain,
    ( r2_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK3)),k1_yellow_0(sK2,sK3))
    | ~ spl7_3
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f100,f187,f121,f187,f56])).

fof(f213,plain,
    ( spl7_16
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f201,f190,f161,f98,f210])).

fof(f201,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,sK4)),k1_yellow_0(sK2,sK4))
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f100,f163,f121,f192,f56])).

fof(f208,plain,
    ( spl7_15
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f196,f185,f156,f98,f205])).

fof(f196,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,sK3)),k1_yellow_0(sK2,sK3))
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f100,f158,f121,f187,f56])).

fof(f193,plain,
    ( spl7_14
    | ~ spl7_3
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f181,f161,f98,f190])).

fof(f181,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK4,sK4),k1_yellow_0(sK2,sK4))
    | ~ spl7_3
    | ~ spl7_9 ),
    inference(unit_resulting_resolution,[],[f100,f163,f163,f121,f56])).

fof(f188,plain,
    ( spl7_13
    | ~ spl7_3
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f180,f156,f98,f185])).

fof(f180,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,sK3),k1_yellow_0(sK2,sK3))
    | ~ spl7_3
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f100,f158,f158,f121,f56])).

fof(f179,plain,
    ( spl7_12
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f154,f113,f98,f93,f176])).

fof(f154,plain,
    ( r2_lattice3(sK2,k2_xboole_0(sK3,sK4),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f95,f100,f115,f121,f83])).

fof(f83,plain,(
    ! [X2,X0] :
      ( r2_lattice3(X0,X2,k1_yellow_0(X0,X2))
      | ~ r1_yellow_0(X0,X2)
      | ~ m1_subset_1(k1_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X2,X1)
      | ~ r1_yellow_0(X0,X2)
      | k1_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f174,plain,
    ( spl7_11
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f151,f113,f108,f98,f171])).

fof(f151,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,sK4),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f100,f110,f117,f115,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
      | ~ r1_yellow_0(X0,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          | ~ r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,X2)
            & r1_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
         => r1_orders_2(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_yellow_0)).

fof(f117,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f77,f79])).

fof(f77,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f169,plain,
    ( spl7_10
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f150,f113,f103,f98,f166])).

fof(f150,plain,
    ( r1_orders_2(sK2,k1_yellow_0(sK2,sK3),k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f100,f105,f77,f115,f54])).

fof(f164,plain,
    ( spl7_9
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f153,f108,f98,f93,f161])).

fof(f153,plain,
    ( r2_lattice3(sK2,sK4,k1_yellow_0(sK2,sK4))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f95,f100,f110,f121,f83])).

fof(f159,plain,
    ( spl7_8
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f152,f103,f98,f93,f156])).

fof(f152,plain,
    ( r2_lattice3(sK2,sK3,k1_yellow_0(sK2,sK3))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f95,f100,f105,f121,f83])).

fof(f127,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f53,f124])).

fof(f53,plain,(
    k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)) != k10_lattice3(sK2,k1_yellow_0(sK2,sK3),k1_yellow_0(sK2,sK4)) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)) != k10_lattice3(sK2,k1_yellow_0(sK2,sK3),k1_yellow_0(sK2,sK4))
    & r1_yellow_0(sK2,k2_xboole_0(sK3,sK4))
    & r1_yellow_0(sK2,sK4)
    & r1_yellow_0(sK2,sK3)
    & l1_orders_2(sK2)
    & v5_orders_2(sK2)
    & v4_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f16,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k1_yellow_0(X0,k2_xboole_0(X1,X2)) != k10_lattice3(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
            & r1_yellow_0(X0,k2_xboole_0(X1,X2))
            & r1_yellow_0(X0,X2)
            & r1_yellow_0(X0,X1) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
   => ( ? [X2,X1] :
          ( k1_yellow_0(sK2,k2_xboole_0(X1,X2)) != k10_lattice3(sK2,k1_yellow_0(sK2,X1),k1_yellow_0(sK2,X2))
          & r1_yellow_0(sK2,k2_xboole_0(X1,X2))
          & r1_yellow_0(sK2,X2)
          & r1_yellow_0(sK2,X1) )
      & l1_orders_2(sK2)
      & v5_orders_2(sK2)
      & v4_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2,X1] :
        ( k1_yellow_0(sK2,k2_xboole_0(X1,X2)) != k10_lattice3(sK2,k1_yellow_0(sK2,X1),k1_yellow_0(sK2,X2))
        & r1_yellow_0(sK2,k2_xboole_0(X1,X2))
        & r1_yellow_0(sK2,X2)
        & r1_yellow_0(sK2,X1) )
   => ( k1_yellow_0(sK2,k2_xboole_0(sK3,sK4)) != k10_lattice3(sK2,k1_yellow_0(sK2,sK3),k1_yellow_0(sK2,sK4))
      & r1_yellow_0(sK2,k2_xboole_0(sK3,sK4))
      & r1_yellow_0(sK2,sK4)
      & r1_yellow_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k1_yellow_0(X0,k2_xboole_0(X1,X2)) != k10_lattice3(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          & r1_yellow_0(X0,k2_xboole_0(X1,X2))
          & r1_yellow_0(X0,X2)
          & r1_yellow_0(X0,X1) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k1_yellow_0(X0,k2_xboole_0(X1,X2)) != k10_lattice3(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2))
          & r1_yellow_0(X0,k2_xboole_0(X1,X2))
          & r1_yellow_0(X0,X2)
          & r1_yellow_0(X0,X1) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0) )
       => ! [X1,X2] :
            ( ( r1_yellow_0(X0,k2_xboole_0(X1,X2))
              & r1_yellow_0(X0,X2)
              & r1_yellow_0(X0,X1) )
           => k1_yellow_0(X0,k2_xboole_0(X1,X2)) = k10_lattice3(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,k2_xboole_0(X1,X2))
            & r1_yellow_0(X0,X2)
            & r1_yellow_0(X0,X1) )
         => k1_yellow_0(X0,k2_xboole_0(X1,X2)) = k10_lattice3(X0,k1_yellow_0(X0,X1),k1_yellow_0(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_yellow_0)).

fof(f116,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f52,f113])).

fof(f52,plain,(
    r1_yellow_0(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f36])).

fof(f111,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f51,f108])).

fof(f51,plain,(
    r1_yellow_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f106,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f50,f103])).

fof(f50,plain,(
    r1_yellow_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f101,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f49,f98])).

fof(f49,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f96,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f48,f93])).

fof(f48,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f91,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f47,f88])).

fof(f47,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f36])).

%------------------------------------------------------------------------------
