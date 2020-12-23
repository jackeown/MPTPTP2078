%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1559+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:06 EST 2020

% Result     : Theorem 7.94s
% Output     : Refutation 7.94s
% Verified   : 
% Statistics : Number of formulae       :  501 (3383 expanded)
%              Number of leaves         :  133 (1415 expanded)
%              Depth                    :   16
%              Number of atoms          : 1965 (13779 expanded)
%              Number of equality atoms :   65 ( 549 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8510,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f96,f101,f106,f111,f116,f127,f159,f164,f169,f177,f182,f197,f202,f209,f214,f235,f240,f267,f272,f305,f315,f320,f335,f340,f364,f369,f405,f410,f423,f428,f443,f499,f504,f509,f514,f647,f652,f698,f708,f713,f718,f725,f730,f735,f740,f745,f757,f2066,f2071,f2076,f2083,f2088,f2093,f2098,f2103,f2110,f2115,f3439,f3444,f3449,f3840,f3845,f3856,f3861,f3866,f3871,f3876,f3894,f3899,f3904,f3983,f3988,f4029,f4054,f4076,f4081,f5558,f5563,f5568,f5573,f5588,f5593,f5598,f5603,f5608,f5621,f5626,f5631,f5636,f5641,f5654,f5659,f5664,f5669,f5674,f5679,f5684,f5689,f5694,f5699,f5704,f5709,f5714,f5719,f5724,f5729,f5734,f5739,f5744,f5749,f5754,f5759,f5764,f5769,f5774,f5779,f7642,f8489,f8502,f8504,f8506,f8509])).

fof(f8509,plain,
    ( ~ spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | spl7_7
    | ~ spl7_10
    | ~ spl7_13
    | ~ spl7_61
    | ~ spl7_118
    | ~ spl7_119 ),
    inference(avatar_contradiction_clause,[],[f8508])).

fof(f8508,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | spl7_7
    | ~ spl7_10
    | ~ spl7_13
    | ~ spl7_61
    | ~ spl7_118
    | ~ spl7_119 ),
    inference(subsumption_resolution,[],[f8507,f5330])).

fof(f5330,plain,
    ( ~ r1_lattice3(sK2,k2_xboole_0(sK3,sK4),sK6(k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | spl7_7
    | ~ spl7_10
    | ~ spl7_13
    | ~ spl7_61 ),
    inference(unit_resulting_resolution,[],[f115,f121,f121,f168,f196,f126,f3448,f3458])).

fof(f3458,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK6(k2_yellow_0(sK2,X0),sK2,X2,X1),u1_struct_0(sK2))
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | k2_yellow_0(sK2,X0) = k11_lattice3(sK2,X1,X2)
        | ~ r1_orders_2(sK2,k2_yellow_0(sK2,X0),X2)
        | ~ r1_orders_2(sK2,k2_yellow_0(sK2,X0),X1)
        | ~ r2_yellow_0(sK2,X0)
        | ~ r1_lattice3(sK2,X0,sK6(k2_yellow_0(sK2,X0),sK2,X2,X1)) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f3451,f121])).

fof(f3451,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK2,k2_yellow_0(sK2,X0),X1)
        | ~ m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2))
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | k2_yellow_0(sK2,X0) = k11_lattice3(sK2,X1,X2)
        | ~ r1_orders_2(sK2,k2_yellow_0(sK2,X0),X2)
        | ~ m1_subset_1(sK6(k2_yellow_0(sK2,X0),sK2,X2,X1),u1_struct_0(sK2))
        | ~ r2_yellow_0(sK2,X0)
        | ~ r1_lattice3(sK2,X0,sK6(k2_yellow_0(sK2,X0),sK2,X2,X1)) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f2078,f418])).

fof(f418,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK2,X1,k2_yellow_0(sK2,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r2_yellow_0(sK2,X0)
        | ~ r1_lattice3(sK2,X0,X1) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f417,f100])).

fof(f100,plain,
    ( l1_orders_2(sK2)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl7_3
  <=> l1_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f417,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice3(sK2,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r2_yellow_0(sK2,X0)
        | ~ l1_orders_2(sK2)
        | r1_orders_2(sK2,X1,k2_yellow_0(sK2,X0)) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f416,f121])).

fof(f416,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice3(sK2,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r2_yellow_0(sK2,X0)
        | ~ m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2))
        | ~ l1_orders_2(sK2)
        | r1_orders_2(sK2,X1,k2_yellow_0(sK2,X0)) )
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
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X3,k2_yellow_0(X0,X2)) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X1)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X2)
      | k2_yellow_0(X0,X2) != X1
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
                      ( r1_orders_2(X0,X3,X1)
                      | ~ r1_lattice3(X0,X2,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
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
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(definition_folding,[],[f24,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ( r2_yellow_0(X0,X2)
        & k2_yellow_0(X0,X2) = X1 )
      | ? [X3] :
          ( ~ r1_orders_2(X0,X3,X1)
          & r1_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ r1_lattice3(X0,X2,X1)
      | ~ sP0(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X1)
                    & r1_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X4,X1)
                      | ~ r1_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r1_lattice3(X0,X2,X1) )
                | ~ r2_yellow_0(X0,X2)
                | k2_yellow_0(X0,X2) != X1 ) )
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
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) )
               => ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 ) )
              & ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X4,X1) ) )
                  & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
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
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) )
               => ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 ) )
              & ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X3,X1) ) )
                  & r1_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_yellow_0)).

fof(f2078,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK2,sK6(X0,sK2,X1,X2),X0)
        | ~ r1_orders_2(sK2,X0,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | k11_lattice3(sK2,X2,X1) = X0
        | ~ r1_orders_2(sK2,X0,X1) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f693,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | ~ r1_orders_2(X1,sK6(X0,X1,X2,X3),X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ~ r1_orders_2(X1,sK6(X0,X1,X2,X3),X0)
        & r1_orders_2(X1,sK6(X0,X1,X2,X3),X2)
        & r1_orders_2(X1,sK6(X0,X1,X2,X3),X3)
        & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X1)) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f44])).

fof(f44,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X1,X4,X0)
          & r1_orders_2(X1,X4,X2)
          & r1_orders_2(X1,X4,X3)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,sK6(X0,X1,X2,X3),X0)
        & r1_orders_2(X1,sK6(X0,X1,X2,X3),X2)
        & r1_orders_2(X1,sK6(X0,X1,X2,X3),X3)
        & m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ r1_orders_2(X1,X4,X0)
          & r1_orders_2(X1,X4,X2)
          & r1_orders_2(X1,X4,X3)
          & m1_subset_1(X4,u1_struct_0(X1)) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X3,X0,X2,X1] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
      | ~ sP1(X3,X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X3,X0,X2,X1] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
      | ~ sP1(X3,X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f693,plain,
    ( ! [X2,X0,X1] :
        ( sP1(X0,sK2,X1,X2)
        | ~ r1_orders_2(sK2,X0,X1)
        | ~ r1_orders_2(sK2,X0,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | k11_lattice3(sK2,X2,X1) = X0 )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f692,f100])).

fof(f692,plain,
    ( ! [X2,X0,X1] :
        ( sP1(X0,sK2,X1,X2)
        | ~ r1_orders_2(sK2,X0,X1)
        | ~ r1_orders_2(sK2,X0,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ m1_subset_1(X2,u1_struct_0(sK2))
        | ~ l1_orders_2(sK2)
        | k11_lattice3(sK2,X2,X1) = X0 )
    | ~ spl7_2 ),
    inference(resolution,[],[f75,f95])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_orders_2(X0)
      | sP1(X3,X0,X2,X1)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k11_lattice3(X0,X1,X2) = X3 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( r2_yellow_0(X0,k2_tarski(X1,X2))
                        & k11_lattice3(X0,X1,X2) = X3 )
                      | sP1(X3,X0,X2,X1)
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                      | k11_lattice3(X0,X1,X2) != X3 ) )
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
                  ( ( ( ( r2_yellow_0(X0,k2_tarski(X1,X2))
                        & k11_lattice3(X0,X1,X2) = X3 )
                      | sP1(X3,X0,X2,X1)
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                      | k11_lattice3(X0,X1,X2) != X3 ) )
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
                  ( ( ( ( r2_yellow_0(X0,k2_tarski(X1,X2))
                        & k11_lattice3(X0,X1,X2) = X3 )
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                      | k11_lattice3(X0,X1,X2) != X3 ) )
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
                  ( ( ( ( r2_yellow_0(X0,k2_tarski(X1,X2))
                        & k11_lattice3(X0,X1,X2) = X3 )
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
                      | k11_lattice3(X0,X1,X2) != X3 ) )
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
                           => ( ( r1_orders_2(X0,X4,X2)
                                & r1_orders_2(X0,X4,X1) )
                             => r1_orders_2(X0,X4,X3) ) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                     => ( r2_yellow_0(X0,k2_tarski(X1,X2))
                        & k11_lattice3(X0,X1,X2) = X3 ) )
                    & ( ( r2_yellow_0(X0,k2_tarski(X1,X2))
                        & k11_lattice3(X0,X1,X2) = X3 )
                     => ( ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X5,X2)
                                & r1_orders_2(X0,X5,X1) )
                             => r1_orders_2(X0,X5,X3) ) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ) ),
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
                           => ( ( r1_orders_2(X0,X4,X2)
                                & r1_orders_2(X0,X4,X1) )
                             => r1_orders_2(X0,X4,X3) ) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                     => ( r2_yellow_0(X0,k2_tarski(X1,X2))
                        & k11_lattice3(X0,X1,X2) = X3 ) )
                    & ( ( r2_yellow_0(X0,k2_tarski(X1,X2))
                        & k11_lattice3(X0,X1,X2) = X3 )
                     => ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X4,X2)
                                & r1_orders_2(X0,X4,X1) )
                             => r1_orders_2(X0,X4,X3) ) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_yellow_0)).

fof(f3448,plain,
    ( m1_subset_1(sK6(k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3)),u1_struct_0(sK2))
    | ~ spl7_61 ),
    inference(avatar_component_clause,[],[f3446])).

fof(f3446,plain,
    ( spl7_61
  <=> m1_subset_1(sK6(k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3)),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).

fof(f126,plain,
    ( k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)) != k11_lattice3(sK2,k2_yellow_0(sK2,sK3),k2_yellow_0(sK2,sK4))
    | spl7_7 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl7_7
  <=> k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)) = k11_lattice3(sK2,k2_yellow_0(sK2,sK3),k2_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f196,plain,
    ( r1_orders_2(sK2,k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),k2_yellow_0(sK2,sK4))
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl7_13
  <=> r1_orders_2(sK2,k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),k2_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f168,plain,
    ( r1_orders_2(sK2,k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),k2_yellow_0(sK2,sK3))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f166])).

fof(f166,plain,
    ( spl7_10
  <=> r1_orders_2(sK2,k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),k2_yellow_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f121,plain,
    ( ! [X0] : m1_subset_1(k2_yellow_0(sK2,X0),u1_struct_0(sK2))
    | ~ spl7_3 ),
    inference(unit_resulting_resolution,[],[f100,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_0)).

fof(f115,plain,
    ( r2_yellow_0(sK2,k2_xboole_0(sK3,sK4))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl7_6
  <=> r2_yellow_0(sK2,k2_xboole_0(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f8507,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,sK4),sK6(k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3)))
    | ~ spl7_3
    | ~ spl7_61
    | ~ spl7_118
    | ~ spl7_119 ),
    inference(forward_demodulation,[],[f8490,f79])).

fof(f79,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f8490,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,sK3),sK6(k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3)))
    | ~ spl7_3
    | ~ spl7_61
    | ~ spl7_118
    | ~ spl7_119 ),
    inference(unit_resulting_resolution,[],[f7641,f3448,f8488,f172])).

fof(f172,plain,
    ( ! [X2,X0,X1] :
        ( r1_lattice3(sK2,k2_xboole_0(X2,X0),X1)
        | ~ r1_lattice3(sK2,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ r1_lattice3(sK2,X0,X1) )
    | ~ spl7_3 ),
    inference(resolution,[],[f55,f100])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_lattice3(X0,X2,X3)
      | ~ r1_lattice3(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | r1_lattice3(X0,k2_xboole_0(X1,X2),X3) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_yellow_0)).

fof(f8488,plain,
    ( r1_lattice3(sK2,sK3,sK6(k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3)))
    | ~ spl7_119 ),
    inference(avatar_component_clause,[],[f8486])).

fof(f8486,plain,
    ( spl7_119
  <=> r1_lattice3(sK2,sK3,sK6(k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_119])])).

fof(f7641,plain,
    ( r1_lattice3(sK2,sK4,sK6(k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3)))
    | ~ spl7_118 ),
    inference(avatar_component_clause,[],[f7639])).

fof(f7639,plain,
    ( spl7_118
  <=> r1_lattice3(sK2,sK4,sK6(k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_118])])).

fof(f8506,plain,
    ( ~ spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | spl7_7
    | ~ spl7_10
    | ~ spl7_13
    | ~ spl7_61
    | ~ spl7_118
    | ~ spl7_119 ),
    inference(avatar_contradiction_clause,[],[f8505])).

fof(f8505,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | spl7_7
    | ~ spl7_10
    | ~ spl7_13
    | ~ spl7_61
    | ~ spl7_118
    | ~ spl7_119 ),
    inference(subsumption_resolution,[],[f8492,f5330])).

fof(f8492,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,sK4),sK6(k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3)))
    | ~ spl7_3
    | ~ spl7_61
    | ~ spl7_118
    | ~ spl7_119 ),
    inference(unit_resulting_resolution,[],[f7641,f3448,f8488,f172])).

fof(f8504,plain,
    ( ~ spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | spl7_7
    | ~ spl7_10
    | ~ spl7_13
    | ~ spl7_61
    | ~ spl7_118
    | ~ spl7_119 ),
    inference(avatar_contradiction_clause,[],[f8503])).

fof(f8503,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | spl7_7
    | ~ spl7_10
    | ~ spl7_13
    | ~ spl7_61
    | ~ spl7_118
    | ~ spl7_119 ),
    inference(subsumption_resolution,[],[f8495,f5330])).

fof(f8495,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,sK4),sK6(k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3)))
    | ~ spl7_3
    | ~ spl7_61
    | ~ spl7_118
    | ~ spl7_119 ),
    inference(unit_resulting_resolution,[],[f100,f7641,f3448,f8488,f55])).

fof(f8502,plain,
    ( ~ spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | spl7_7
    | ~ spl7_10
    | ~ spl7_13
    | ~ spl7_61
    | ~ spl7_118
    | ~ spl7_119 ),
    inference(avatar_contradiction_clause,[],[f8501])).

fof(f8501,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | spl7_7
    | ~ spl7_10
    | ~ spl7_13
    | ~ spl7_61
    | ~ spl7_118
    | ~ spl7_119 ),
    inference(subsumption_resolution,[],[f8500,f5330])).

fof(f8500,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,sK4),sK6(k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3)))
    | ~ spl7_3
    | ~ spl7_61
    | ~ spl7_118
    | ~ spl7_119 ),
    inference(forward_demodulation,[],[f8497,f79])).

fof(f8497,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,sK3),sK6(k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3)))
    | ~ spl7_3
    | ~ spl7_61
    | ~ spl7_118
    | ~ spl7_119 ),
    inference(unit_resulting_resolution,[],[f100,f7641,f3448,f8488,f55])).

fof(f8489,plain,
    ( spl7_119
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_61
    | ~ spl7_109 ),
    inference(avatar_split_clause,[],[f8474,f5736,f3446,f156,f98,f88,f8486])).

fof(f88,plain,
    ( spl7_1
  <=> v4_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f156,plain,
    ( spl7_8
  <=> r1_lattice3(sK2,sK3,k2_yellow_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f5736,plain,
    ( spl7_109
  <=> r1_orders_2(sK2,sK6(k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3)),k2_yellow_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_109])])).

fof(f8474,plain,
    ( r1_lattice3(sK2,sK3,sK6(k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3)))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_61
    | ~ spl7_109 ),
    inference(unit_resulting_resolution,[],[f90,f100,f158,f121,f3448,f5738,f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,X3,X1)
      | ~ r1_lattice3(X0,X3,X2)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_0)).

fof(f5738,plain,
    ( r1_orders_2(sK2,sK6(k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3)),k2_yellow_0(sK2,sK3))
    | ~ spl7_109 ),
    inference(avatar_component_clause,[],[f5736])).

fof(f158,plain,
    ( r1_lattice3(sK2,sK3,k2_yellow_0(sK2,sK3))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f156])).

fof(f90,plain,
    ( v4_orders_2(sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f7642,plain,
    ( spl7_118
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_61
    | ~ spl7_103 ),
    inference(avatar_split_clause,[],[f7627,f5706,f3446,f161,f98,f88,f7639])).

fof(f161,plain,
    ( spl7_9
  <=> r1_lattice3(sK2,sK4,k2_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f5706,plain,
    ( spl7_103
  <=> r1_orders_2(sK2,sK6(k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3)),k2_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_103])])).

fof(f7627,plain,
    ( r1_lattice3(sK2,sK4,sK6(k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3)))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_61
    | ~ spl7_103 ),
    inference(unit_resulting_resolution,[],[f90,f100,f163,f121,f3448,f5708,f57])).

fof(f5708,plain,
    ( r1_orders_2(sK2,sK6(k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3)),k2_yellow_0(sK2,sK4))
    | ~ spl7_103 ),
    inference(avatar_component_clause,[],[f5706])).

fof(f163,plain,
    ( r1_lattice3(sK2,sK4,k2_yellow_0(sK2,sK4))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f161])).

fof(f5779,plain,
    ( spl7_117
    | ~ spl7_3
    | ~ spl7_25
    | ~ spl7_48 ),
    inference(avatar_split_clause,[],[f2001,f754,f337,f98,f5776])).

fof(f5776,plain,
    ( spl7_117
  <=> r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK3,sK4)))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_117])])).

fof(f337,plain,
    ( spl7_25
  <=> r1_lattice3(sK2,sK4,k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f754,plain,
    ( spl7_48
  <=> r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK3,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f2001,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK3,sK4)))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_25
    | ~ spl7_48 ),
    inference(unit_resulting_resolution,[],[f100,f339,f121,f756,f55])).

fof(f756,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK3,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_48 ),
    inference(avatar_component_clause,[],[f754])).

fof(f339,plain,
    ( r1_lattice3(sK2,sK4,k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f337])).

fof(f5774,plain,
    ( spl7_116
    | ~ spl7_3
    | ~ spl7_24
    | ~ spl7_48 ),
    inference(avatar_split_clause,[],[f2000,f754,f332,f98,f5771])).

fof(f5771,plain,
    ( spl7_116
  <=> r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK3,sK4)))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_116])])).

fof(f332,plain,
    ( spl7_24
  <=> r1_lattice3(sK2,sK3,k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f2000,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK3,sK4)))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_24
    | ~ spl7_48 ),
    inference(unit_resulting_resolution,[],[f100,f334,f121,f756,f55])).

fof(f334,plain,
    ( r1_lattice3(sK2,sK3,k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f332])).

fof(f5769,plain,
    ( spl7_115
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f3961,f440,f98,f93,f5766])).

fof(f5766,plain,
    ( spl7_115
  <=> k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)) = k11_lattice3(sK2,k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_115])])).

fof(f440,plain,
    ( spl7_32
  <=> r1_orders_2(sK2,k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f3961,plain,
    ( k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)) = k11_lattice3(sK2,k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f121,f442,f442,f121,f3459])).

fof(f3459,plain,
    ( ! [X8,X7] :
        ( ~ r1_orders_2(sK2,X7,X7)
        | ~ m1_subset_1(X7,u1_struct_0(sK2))
        | ~ m1_subset_1(X8,u1_struct_0(sK2))
        | k11_lattice3(sK2,X7,X8) = X7
        | ~ r1_orders_2(sK2,X7,X8) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f3456,f693])).

fof(f3456,plain,
    ( ! [X8,X7] :
        ( ~ r1_orders_2(sK2,X7,X7)
        | ~ m1_subset_1(X7,u1_struct_0(sK2))
        | ~ m1_subset_1(X8,u1_struct_0(sK2))
        | k11_lattice3(sK2,X7,X8) = X7
        | ~ r1_orders_2(sK2,X7,X8)
        | ~ sP1(X7,sK2,X8,X7) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(duplicate_literal_removal,[],[f3453])).

fof(f3453,plain,
    ( ! [X8,X7] :
        ( ~ r1_orders_2(sK2,X7,X7)
        | ~ m1_subset_1(X7,u1_struct_0(sK2))
        | ~ m1_subset_1(X8,u1_struct_0(sK2))
        | ~ m1_subset_1(X7,u1_struct_0(sK2))
        | k11_lattice3(sK2,X7,X8) = X7
        | ~ r1_orders_2(sK2,X7,X8)
        | ~ sP1(X7,sK2,X8,X7) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f2078,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X1,sK6(X0,X1,X2,X3),X3)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f442,plain,
    ( r1_orders_2(sK2,k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f440])).

fof(f5764,plain,
    ( spl7_114
    | ~ spl7_3
    | ~ spl7_25
    | ~ spl7_47 ),
    inference(avatar_split_clause,[],[f1879,f742,f337,f98,f5761])).

fof(f5761,plain,
    ( spl7_114
  <=> r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK4,k2_xboole_0(sK3,sK4)))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_114])])).

fof(f742,plain,
    ( spl7_47
  <=> r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK4,k2_xboole_0(sK3,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f1879,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK4,k2_xboole_0(sK3,sK4)))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_25
    | ~ spl7_47 ),
    inference(unit_resulting_resolution,[],[f100,f339,f121,f744,f55])).

fof(f744,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK4,k2_xboole_0(sK3,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_47 ),
    inference(avatar_component_clause,[],[f742])).

fof(f5759,plain,
    ( spl7_113
    | ~ spl7_3
    | ~ spl7_24
    | ~ spl7_47 ),
    inference(avatar_split_clause,[],[f1878,f742,f332,f98,f5756])).

fof(f5756,plain,
    ( spl7_113
  <=> r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK4,k2_xboole_0(sK3,sK4)))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_113])])).

fof(f1878,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK4,k2_xboole_0(sK3,sK4)))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_24
    | ~ spl7_47 ),
    inference(unit_resulting_resolution,[],[f100,f334,f121,f744,f55])).

fof(f5754,plain,
    ( spl7_112
    | ~ spl7_3
    | ~ spl7_25
    | ~ spl7_46 ),
    inference(avatar_split_clause,[],[f1762,f737,f337,f98,f5751])).

fof(f5751,plain,
    ( spl7_112
  <=> r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK3,sK4)))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_112])])).

fof(f737,plain,
    ( spl7_46
  <=> r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK3,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f1762,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK3,sK4)))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_25
    | ~ spl7_46 ),
    inference(unit_resulting_resolution,[],[f100,f339,f121,f739,f55])).

fof(f739,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK3,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f737])).

fof(f5749,plain,
    ( spl7_111
    | ~ spl7_3
    | ~ spl7_24
    | ~ spl7_46 ),
    inference(avatar_split_clause,[],[f1761,f737,f332,f98,f5746])).

fof(f5746,plain,
    ( spl7_111
  <=> r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK3,sK4)))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_111])])).

fof(f1761,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK3,sK4)))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_24
    | ~ spl7_46 ),
    inference(unit_resulting_resolution,[],[f100,f334,f121,f739,f55])).

fof(f5744,plain,
    ( spl7_110
    | ~ spl7_3
    | ~ spl7_25
    | ~ spl7_45 ),
    inference(avatar_split_clause,[],[f1652,f732,f337,f98,f5741])).

fof(f5741,plain,
    ( spl7_110
  <=> r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,sK4)))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_110])])).

fof(f732,plain,
    ( spl7_45
  <=> r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f1652,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,sK4)))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_25
    | ~ spl7_45 ),
    inference(unit_resulting_resolution,[],[f100,f339,f121,f734,f55])).

fof(f734,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_45 ),
    inference(avatar_component_clause,[],[f732])).

fof(f5739,plain,
    ( spl7_109
    | ~ spl7_39 ),
    inference(avatar_split_clause,[],[f701,f695,f5736])).

fof(f695,plain,
    ( spl7_39
  <=> sP1(k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f701,plain,
    ( r1_orders_2(sK2,sK6(k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3)),k2_yellow_0(sK2,sK3))
    | ~ spl7_39 ),
    inference(unit_resulting_resolution,[],[f697,f69])).

fof(f697,plain,
    ( sP1(k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3))
    | ~ spl7_39 ),
    inference(avatar_component_clause,[],[f695])).

fof(f5734,plain,
    ( spl7_108
    | ~ spl7_3
    | ~ spl7_24
    | ~ spl7_45 ),
    inference(avatar_split_clause,[],[f1651,f732,f332,f98,f5731])).

fof(f5731,plain,
    ( spl7_108
  <=> r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,sK4)))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_108])])).

fof(f1651,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,sK4)))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_24
    | ~ spl7_45 ),
    inference(unit_resulting_resolution,[],[f100,f334,f121,f734,f55])).

fof(f5729,plain,
    ( spl7_107
    | ~ spl7_3
    | ~ spl7_25
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f1548,f727,f337,f98,f5726])).

fof(f5726,plain,
    ( spl7_107
  <=> r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_107])])).

fof(f727,plain,
    ( spl7_44
  <=> r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK4,sK4)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f1548,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_25
    | ~ spl7_44 ),
    inference(unit_resulting_resolution,[],[f100,f339,f121,f729,f55])).

fof(f729,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK4,sK4)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f727])).

fof(f5724,plain,
    ( spl7_106
    | ~ spl7_3
    | ~ spl7_24
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f1547,f727,f332,f98,f5721])).

fof(f5721,plain,
    ( spl7_106
  <=> r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_106])])).

fof(f1547,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_24
    | ~ spl7_44 ),
    inference(unit_resulting_resolution,[],[f100,f334,f121,f729,f55])).

fof(f5719,plain,
    ( spl7_105
    | ~ spl7_3
    | ~ spl7_25
    | ~ spl7_43 ),
    inference(avatar_split_clause,[],[f1450,f722,f337,f98,f5716])).

fof(f5716,plain,
    ( spl7_105
  <=> r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_105])])).

fof(f722,plain,
    ( spl7_43
  <=> r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK4,sK4)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f1450,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_25
    | ~ spl7_43 ),
    inference(unit_resulting_resolution,[],[f100,f339,f121,f724,f55])).

fof(f724,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK4,sK4)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_43 ),
    inference(avatar_component_clause,[],[f722])).

fof(f5714,plain,
    ( spl7_104
    | ~ spl7_3
    | ~ spl7_24
    | ~ spl7_43 ),
    inference(avatar_split_clause,[],[f1449,f722,f332,f98,f5711])).

fof(f5711,plain,
    ( spl7_104
  <=> r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_104])])).

fof(f1449,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_24
    | ~ spl7_43 ),
    inference(unit_resulting_resolution,[],[f100,f334,f121,f724,f55])).

fof(f5709,plain,
    ( spl7_103
    | ~ spl7_39 ),
    inference(avatar_split_clause,[],[f700,f695,f5706])).

fof(f700,plain,
    ( r1_orders_2(sK2,sK6(k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3)),k2_yellow_0(sK2,sK4))
    | ~ spl7_39 ),
    inference(unit_resulting_resolution,[],[f697,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X1,sK6(X0,X1,X2,X3),X2)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f5704,plain,
    ( spl7_102
    | ~ spl7_3
    | ~ spl7_25
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f1358,f715,f337,f98,f5701])).

fof(f5701,plain,
    ( spl7_102
  <=> r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_102])])).

fof(f715,plain,
    ( spl7_42
  <=> r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK4)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f1358,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_25
    | ~ spl7_42 ),
    inference(unit_resulting_resolution,[],[f100,f339,f121,f717,f55])).

fof(f717,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK4)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f715])).

fof(f5699,plain,
    ( spl7_101
    | ~ spl7_3
    | ~ spl7_24
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f1357,f715,f332,f98,f5696])).

fof(f5696,plain,
    ( spl7_101
  <=> r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_101])])).

fof(f1357,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_24
    | ~ spl7_42 ),
    inference(unit_resulting_resolution,[],[f100,f334,f121,f717,f55])).

fof(f5694,plain,
    ( spl7_100
    | ~ spl7_3
    | ~ spl7_24
    | ~ spl7_41 ),
    inference(avatar_split_clause,[],[f855,f710,f332,f98,f5691])).

fof(f5691,plain,
    ( spl7_100
  <=> r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_100])])).

fof(f710,plain,
    ( spl7_41
  <=> r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,sK4)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f855,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_24
    | ~ spl7_41 ),
    inference(unit_resulting_resolution,[],[f100,f334,f121,f712,f55])).

fof(f712,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,sK4)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f710])).

fof(f5689,plain,
    ( spl7_99
    | ~ spl7_3
    | ~ spl7_25
    | ~ spl7_40 ),
    inference(avatar_split_clause,[],[f816,f705,f337,f98,f5686])).

fof(f5686,plain,
    ( spl7_99
  <=> r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_99])])).

fof(f705,plain,
    ( spl7_40
  <=> r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK3)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f816,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_25
    | ~ spl7_40 ),
    inference(unit_resulting_resolution,[],[f100,f339,f121,f707,f55])).

fof(f707,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK3)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_40 ),
    inference(avatar_component_clause,[],[f705])).

fof(f5684,plain,
    ( spl7_98
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_13
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f794,f649,f194,f98,f88,f5681])).

fof(f5681,plain,
    ( spl7_98
  <=> r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_98])])).

fof(f649,plain,
    ( spl7_38
  <=> r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f794,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_13
    | ~ spl7_38 ),
    inference(unit_resulting_resolution,[],[f90,f100,f121,f196,f121,f651,f57])).

fof(f651,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,sK4))
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f649])).

fof(f5679,plain,
    ( spl7_97
    | ~ spl7_3
    | ~ spl7_14
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f308,f302,f199,f98,f5676])).

fof(f5676,plain,
    ( spl7_97
  <=> r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_97])])).

fof(f199,plain,
    ( spl7_14
  <=> r1_lattice3(sK2,k2_xboole_0(sK3,sK4),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f302,plain,
    ( spl7_21
  <=> r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK4)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f308,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_14
    | ~ spl7_21 ),
    inference(unit_resulting_resolution,[],[f100,f201,f121,f304,f55])).

fof(f304,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK4)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f302])).

fof(f201,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,sK4),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f199])).

fof(f5674,plain,
    ( spl7_96
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f787,f649,f161,f98,f5671])).

fof(f5671,plain,
    ( spl7_96
  <=> r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,sK4)))),k2_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_96])])).

fof(f787,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,sK4)))),k2_yellow_0(sK2,sK4))
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_38 ),
    inference(unit_resulting_resolution,[],[f100,f163,f121,f651,f55])).

fof(f5669,plain,
    ( spl7_95
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f772,f644,f166,f98,f88,f5666])).

fof(f5666,plain,
    ( spl7_95
  <=> r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_95])])).

fof(f644,plain,
    ( spl7_37
  <=> r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f772,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_37 ),
    inference(unit_resulting_resolution,[],[f90,f100,f121,f168,f121,f646,f57])).

fof(f646,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,sK3))
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f644])).

fof(f5664,plain,
    ( spl7_94
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f765,f644,f156,f98,f5661])).

fof(f5661,plain,
    ( spl7_94
  <=> r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK3)))),k2_yellow_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_94])])).

fof(f765,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK3)))),k2_yellow_0(sK2,sK3))
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_37 ),
    inference(unit_resulting_resolution,[],[f100,f158,f121,f646,f55])).

fof(f5659,plain,
    ( spl7_93
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f678,f317,f161,f98,f5656])).

fof(f5656,plain,
    ( spl7_93
  <=> r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,k2_xboole_0(sK4,sK4)))),k2_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_93])])).

fof(f317,plain,
    ( spl7_23
  <=> r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f678,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,k2_xboole_0(sK4,sK4)))),k2_yellow_0(sK2,sK4))
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_23 ),
    inference(unit_resulting_resolution,[],[f100,f163,f121,f319,f55])).

fof(f319,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,sK4))
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f317])).

fof(f5654,plain,
    ( spl7_92
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f659,f312,f156,f98,f5651])).

fof(f5651,plain,
    ( spl7_92
  <=> r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,k2_xboole_0(sK3,sK3)))),k2_yellow_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_92])])).

fof(f312,plain,
    ( spl7_22
  <=> r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f659,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,k2_xboole_0(sK3,sK3)))),k2_yellow_0(sK2,sK3))
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_22 ),
    inference(unit_resulting_resolution,[],[f100,f158,f121,f314,f55])).

fof(f314,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,sK3))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f312])).

fof(f5641,plain,
    ( spl7_91
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f627,f511,f366,f98,f5638])).

fof(f5638,plain,
    ( spl7_91
  <=> r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK3,k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_91])])).

fof(f366,plain,
    ( spl7_27
  <=> r1_lattice3(sK2,k2_xboole_0(sK4,sK4),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f511,plain,
    ( spl7_36
  <=> r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK4,sK4)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f627,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK3,k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_36 ),
    inference(unit_resulting_resolution,[],[f100,f368,f121,f513,f55])).

fof(f513,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK4,sK4)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f511])).

fof(f368,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,sK4),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f366])).

fof(f5636,plain,
    ( spl7_90
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f622,f511,f361,f98,f5633])).

fof(f5633,plain,
    ( spl7_90
  <=> r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_90])])).

fof(f361,plain,
    ( spl7_26
  <=> r1_lattice3(sK2,k2_xboole_0(sK3,sK3),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f622,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_36 ),
    inference(unit_resulting_resolution,[],[f100,f363,f121,f513,f55])).

fof(f363,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,sK3),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f361])).

fof(f5631,plain,
    ( spl7_89
    | ~ spl7_3
    | ~ spl7_14
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f621,f511,f199,f98,f5628])).

fof(f5628,plain,
    ( spl7_89
  <=> r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_89])])).

fof(f621,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_14
    | ~ spl7_36 ),
    inference(unit_resulting_resolution,[],[f100,f201,f121,f513,f55])).

fof(f5626,plain,
    ( spl7_88
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f590,f506,f366,f98,f5623])).

fof(f5623,plain,
    ( spl7_88
  <=> r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_88])])).

fof(f506,plain,
    ( spl7_35
  <=> r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK3,sK3)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f590,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_35 ),
    inference(unit_resulting_resolution,[],[f100,f368,f121,f508,f55])).

fof(f508,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK3,sK3)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f506])).

fof(f5621,plain,
    ( spl7_87
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f586,f506,f361,f98,f5618])).

fof(f5618,plain,
    ( spl7_87
  <=> r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK4,k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_87])])).

fof(f586,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK4,k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_35 ),
    inference(unit_resulting_resolution,[],[f100,f363,f121,f508,f55])).

fof(f5608,plain,
    ( spl7_86
    | ~ spl7_3
    | ~ spl7_14
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f585,f506,f199,f98,f5605])).

fof(f5605,plain,
    ( spl7_86
  <=> r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK4,k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_86])])).

fof(f585,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK4,k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_14
    | ~ spl7_35 ),
    inference(unit_resulting_resolution,[],[f100,f201,f121,f508,f55])).

fof(f5603,plain,
    ( spl7_85
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f559,f501,f366,f98,f5600])).

fof(f5600,plain,
    ( spl7_85
  <=> r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_85])])).

fof(f501,plain,
    ( spl7_34
  <=> r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,sK4)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f559,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_34 ),
    inference(unit_resulting_resolution,[],[f100,f368,f121,f503,f55])).

fof(f503,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,sK4)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f501])).

fof(f5598,plain,
    ( spl7_84
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f555,f501,f361,f98,f5595])).

fof(f5595,plain,
    ( spl7_84
  <=> r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK4,k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_84])])).

fof(f555,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK4,k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_34 ),
    inference(unit_resulting_resolution,[],[f100,f363,f121,f503,f55])).

fof(f5593,plain,
    ( spl7_83
    | ~ spl7_3
    | ~ spl7_14
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f554,f501,f199,f98,f5590])).

fof(f5590,plain,
    ( spl7_83
  <=> r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK4,k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_83])])).

fof(f554,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK4,k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_14
    | ~ spl7_34 ),
    inference(unit_resulting_resolution,[],[f100,f201,f121,f503,f55])).

fof(f5588,plain,
    ( spl7_82
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f531,f496,f366,f98,f5585])).

fof(f5585,plain,
    ( spl7_82
  <=> r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK3,k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_82])])).

fof(f496,plain,
    ( spl7_33
  <=> r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,sK3)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f531,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK3,k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_33 ),
    inference(unit_resulting_resolution,[],[f100,f368,f121,f498,f55])).

fof(f498,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,sK3)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f496])).

fof(f5573,plain,
    ( spl7_81
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f527,f496,f361,f98,f5570])).

fof(f5570,plain,
    ( spl7_81
  <=> r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_81])])).

fof(f527,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_33 ),
    inference(unit_resulting_resolution,[],[f100,f363,f121,f498,f55])).

fof(f5568,plain,
    ( spl7_80
    | ~ spl7_3
    | ~ spl7_14
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f526,f496,f199,f98,f5565])).

fof(f5565,plain,
    ( spl7_80
  <=> r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_80])])).

fof(f526,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_14
    | ~ spl7_33 ),
    inference(unit_resulting_resolution,[],[f100,f201,f121,f498,f55])).

fof(f5563,plain,
    ( spl7_79
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f293,f269,f179,f98,f5560])).

fof(f5560,plain,
    ( spl7_79
  <=> r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK4,sK4)))),k2_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_79])])).

fof(f179,plain,
    ( spl7_12
  <=> r1_lattice3(sK2,k2_xboole_0(sK4,sK4),k2_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f269,plain,
    ( spl7_20
  <=> r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f293,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK4,sK4)))),k2_yellow_0(sK2,sK4))
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_20 ),
    inference(unit_resulting_resolution,[],[f100,f181,f121,f271,f55])).

fof(f271,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,sK4))
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f269])).

fof(f181,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,sK4),k2_yellow_0(sK2,sK4))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f179])).

fof(f5558,plain,
    ( spl7_78
    | ~ spl7_3
    | ~ spl7_11
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f279,f264,f174,f98,f5555])).

fof(f5555,plain,
    ( spl7_78
  <=> r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,sK3)))),k2_yellow_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).

fof(f174,plain,
    ( spl7_11
  <=> r1_lattice3(sK2,k2_xboole_0(sK3,sK3),k2_yellow_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f264,plain,
    ( spl7_19
  <=> r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f279,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,sK3)))),k2_yellow_0(sK2,sK3))
    | ~ spl7_3
    | ~ spl7_11
    | ~ spl7_19 ),
    inference(unit_resulting_resolution,[],[f100,f176,f121,f266,f55])).

fof(f266,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,sK3))
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f264])).

fof(f176,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,sK3),k2_yellow_0(sK2,sK3))
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f174])).

fof(f4081,plain,
    ( spl7_77
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_13
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f4031,f440,f194,f98,f93,f4078])).

fof(f4078,plain,
    ( spl7_77
  <=> k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)) = k11_lattice3(sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_77])])).

fof(f4031,plain,
    ( k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)) = k11_lattice3(sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_13
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f121,f196,f442,f121,f3460])).

fof(f3460,plain,
    ( ! [X10,X9] :
        ( ~ r1_orders_2(sK2,X9,X9)
        | ~ m1_subset_1(X9,u1_struct_0(sK2))
        | ~ m1_subset_1(X10,u1_struct_0(sK2))
        | k11_lattice3(sK2,X10,X9) = X9
        | ~ r1_orders_2(sK2,X9,X10) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f3455,f693])).

fof(f3455,plain,
    ( ! [X10,X9] :
        ( ~ r1_orders_2(sK2,X9,X10)
        | ~ m1_subset_1(X9,u1_struct_0(sK2))
        | ~ m1_subset_1(X10,u1_struct_0(sK2))
        | k11_lattice3(sK2,X10,X9) = X9
        | ~ r1_orders_2(sK2,X9,X9)
        | ~ sP1(X9,sK2,X9,X10) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(duplicate_literal_removal,[],[f3454])).

fof(f3454,plain,
    ( ! [X10,X9] :
        ( ~ r1_orders_2(sK2,X9,X10)
        | ~ m1_subset_1(X9,u1_struct_0(sK2))
        | ~ m1_subset_1(X9,u1_struct_0(sK2))
        | ~ m1_subset_1(X10,u1_struct_0(sK2))
        | k11_lattice3(sK2,X10,X9) = X9
        | ~ r1_orders_2(sK2,X9,X9)
        | ~ sP1(X9,sK2,X9,X10) )
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(resolution,[],[f2078,f70])).

fof(f4076,plain,
    ( spl7_76
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f4030,f440,f166,f98,f93,f4073])).

fof(f4073,plain,
    ( spl7_76
  <=> k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)) = k11_lattice3(sK2,k2_yellow_0(sK2,sK3),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_76])])).

fof(f4030,plain,
    ( k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)) = k11_lattice3(sK2,k2_yellow_0(sK2,sK3),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f121,f168,f442,f121,f3460])).

fof(f4054,plain,
    ( spl7_75
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_13
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f3960,f440,f194,f98,f93,f4051])).

fof(f4051,plain,
    ( spl7_75
  <=> k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)) = k11_lattice3(sK2,k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),k2_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_75])])).

fof(f3960,plain,
    ( k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)) = k11_lattice3(sK2,k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),k2_yellow_0(sK2,sK4))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_13
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f121,f196,f442,f121,f3459])).

fof(f4029,plain,
    ( spl7_74
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f3959,f440,f166,f98,f93,f4026])).

fof(f4026,plain,
    ( spl7_74
  <=> k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)) = k11_lattice3(sK2,k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),k2_yellow_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_74])])).

fof(f3959,plain,
    ( k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)) = k11_lattice3(sK2,k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),k2_yellow_0(sK2,sK3))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_32 ),
    inference(unit_resulting_resolution,[],[f121,f168,f442,f121,f3459])).

fof(f3988,plain,
    ( spl7_73
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_31 ),
    inference(avatar_split_clause,[],[f3963,f425,f98,f93,f3985])).

fof(f3985,plain,
    ( spl7_73
  <=> k2_yellow_0(sK2,sK4) = k11_lattice3(sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_73])])).

fof(f425,plain,
    ( spl7_31
  <=> r1_orders_2(sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f3963,plain,
    ( k2_yellow_0(sK2,sK4) = k11_lattice3(sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK4))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_31 ),
    inference(unit_resulting_resolution,[],[f121,f427,f427,f121,f3459])).

fof(f427,plain,
    ( r1_orders_2(sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK4))
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f425])).

fof(f3983,plain,
    ( spl7_72
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f3962,f420,f98,f93,f3980])).

fof(f3980,plain,
    ( spl7_72
  <=> k2_yellow_0(sK2,sK3) = k11_lattice3(sK2,k2_yellow_0(sK2,sK3),k2_yellow_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).

fof(f420,plain,
    ( spl7_30
  <=> r1_orders_2(sK2,k2_yellow_0(sK2,sK3),k2_yellow_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f3962,plain,
    ( k2_yellow_0(sK2,sK3) = k11_lattice3(sK2,k2_yellow_0(sK2,sK3),k2_yellow_0(sK2,sK3))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_30 ),
    inference(unit_resulting_resolution,[],[f121,f422,f422,f121,f3459])).

fof(f422,plain,
    ( r1_orders_2(sK2,k2_yellow_0(sK2,sK3),k2_yellow_0(sK2,sK3))
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f420])).

fof(f3904,plain,
    ( spl7_71
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_29 ),
    inference(avatar_split_clause,[],[f485,f407,f366,f98,f3901])).

fof(f3901,plain,
    ( spl7_71
  <=> r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,k2_xboole_0(sK3,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_71])])).

fof(f407,plain,
    ( spl7_29
  <=> r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK3,sK4)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f485,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,k2_xboole_0(sK3,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_29 ),
    inference(unit_resulting_resolution,[],[f100,f368,f121,f409,f55])).

fof(f409,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK3,sK4)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f407])).

fof(f3899,plain,
    ( spl7_70
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_29 ),
    inference(avatar_split_clause,[],[f482,f407,f361,f98,f3896])).

fof(f3896,plain,
    ( spl7_70
  <=> r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK4,k2_xboole_0(sK3,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_70])])).

fof(f482,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK4,k2_xboole_0(sK3,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_29 ),
    inference(unit_resulting_resolution,[],[f100,f363,f121,f409,f55])).

fof(f3894,plain,
    ( spl7_69
    | ~ spl7_3
    | ~ spl7_14
    | ~ spl7_29 ),
    inference(avatar_split_clause,[],[f481,f407,f199,f98,f3891])).

fof(f3891,plain,
    ( spl7_69
  <=> r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK4,k2_xboole_0(sK3,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_69])])).

fof(f481,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK4,k2_xboole_0(sK3,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_14
    | ~ spl7_29 ),
    inference(unit_resulting_resolution,[],[f100,f201,f121,f409,f55])).

fof(f3876,plain,
    ( spl7_68
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f463,f402,f366,f98,f3873])).

fof(f3873,plain,
    ( spl7_68
  <=> r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK3,k2_xboole_0(sK3,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).

fof(f402,plain,
    ( spl7_28
  <=> r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,sK4)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f463,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK3,k2_xboole_0(sK3,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_27
    | ~ spl7_28 ),
    inference(unit_resulting_resolution,[],[f100,f368,f121,f404,f55])).

fof(f404,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,sK4)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f402])).

fof(f3871,plain,
    ( spl7_67
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f460,f402,f361,f98,f3868])).

fof(f3868,plain,
    ( spl7_67
  <=> r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,k2_xboole_0(sK3,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_67])])).

fof(f460,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,k2_xboole_0(sK3,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_28 ),
    inference(unit_resulting_resolution,[],[f100,f363,f121,f404,f55])).

fof(f3866,plain,
    ( spl7_66
    | ~ spl7_3
    | ~ spl7_14
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f459,f402,f199,f98,f3863])).

fof(f3863,plain,
    ( spl7_66
  <=> r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,k2_xboole_0(sK3,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).

fof(f459,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,k2_xboole_0(sK3,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_14
    | ~ spl7_28 ),
    inference(unit_resulting_resolution,[],[f100,f201,f121,f404,f55])).

fof(f3861,plain,
    ( spl7_65
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f257,f237,f179,f98,f3858])).

fof(f3858,plain,
    ( spl7_65
  <=> r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).

fof(f237,plain,
    ( spl7_18
  <=> r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,sK4)),k2_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f257,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,sK4))
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_18 ),
    inference(unit_resulting_resolution,[],[f100,f181,f121,f239,f55])).

fof(f239,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,sK4)),k2_yellow_0(sK2,sK4))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f237])).

fof(f3856,plain,
    ( spl7_64
    | ~ spl7_3
    | ~ spl7_11
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f246,f232,f174,f98,f3853])).

fof(f3853,plain,
    ( spl7_64
  <=> r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f232,plain,
    ( spl7_17
  <=> r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK3)),k2_yellow_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f246,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,sK3))
    | ~ spl7_3
    | ~ spl7_11
    | ~ spl7_17 ),
    inference(unit_resulting_resolution,[],[f100,f176,f121,f234,f55])).

fof(f234,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK3)),k2_yellow_0(sK2,sK3))
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f232])).

fof(f3845,plain,
    ( spl7_63
    | ~ spl7_3
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f228,f211,f98,f3842])).

fof(f3842,plain,
    ( spl7_63
  <=> r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,k2_xboole_0(sK4,sK4)),k2_xboole_0(sK4,k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).

fof(f211,plain,
    ( spl7_16
  <=> r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,sK4)),k2_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f228,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,k2_xboole_0(sK4,sK4)),k2_xboole_0(sK4,k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,sK4))
    | ~ spl7_3
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f100,f213,f121,f213,f55])).

fof(f213,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,sK4)),k2_yellow_0(sK2,sK4))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f211])).

fof(f3840,plain,
    ( spl7_62
    | ~ spl7_3
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f220,f206,f98,f3837])).

fof(f3837,plain,
    ( spl7_62
  <=> r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK3,sK3)),k2_xboole_0(sK3,k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f206,plain,
    ( spl7_15
  <=> r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,sK3)),k2_yellow_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f220,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,k2_xboole_0(sK3,sK3)),k2_xboole_0(sK3,k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,sK3))
    | ~ spl7_3
    | ~ spl7_15 ),
    inference(unit_resulting_resolution,[],[f100,f208,f121,f208,f55])).

fof(f208,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,sK3)),k2_yellow_0(sK2,sK3))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f206])).

fof(f3449,plain,
    ( spl7_61
    | ~ spl7_39 ),
    inference(avatar_split_clause,[],[f702,f695,f3446])).

fof(f702,plain,
    ( m1_subset_1(sK6(k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3)),u1_struct_0(sK2))
    | ~ spl7_39 ),
    inference(unit_resulting_resolution,[],[f697,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f3444,plain,
    ( spl7_60
    | ~ spl7_3
    | ~ spl7_21
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f357,f337,f302,f98,f3441])).

fof(f3441,plain,
    ( spl7_60
  <=> r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f357,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_21
    | ~ spl7_25 ),
    inference(forward_demodulation,[],[f356,f79])).

fof(f356,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK4)),sK4),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_21
    | ~ spl7_25 ),
    inference(unit_resulting_resolution,[],[f100,f304,f121,f339,f55])).

fof(f3439,plain,
    ( spl7_59
    | ~ spl7_3
    | ~ spl7_21
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f347,f332,f302,f98,f3436])).

fof(f3436,plain,
    ( spl7_59
  <=> r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).

fof(f347,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_21
    | ~ spl7_24 ),
    inference(forward_demodulation,[],[f346,f79])).

fof(f346,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK4)),sK3),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_21
    | ~ spl7_24 ),
    inference(unit_resulting_resolution,[],[f100,f304,f121,f334,f55])).

fof(f2115,plain,
    ( spl7_58
    | ~ spl7_3
    | ~ spl7_25
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f620,f511,f337,f98,f2112])).

fof(f2112,plain,
    ( spl7_58
  <=> r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_58])])).

fof(f620,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_25
    | ~ spl7_36 ),
    inference(unit_resulting_resolution,[],[f100,f339,f121,f513,f55])).

fof(f2110,plain,
    ( spl7_57
    | ~ spl7_3
    | ~ spl7_24
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f619,f511,f332,f98,f2107])).

fof(f2107,plain,
    ( spl7_57
  <=> r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).

fof(f619,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_24
    | ~ spl7_36 ),
    inference(unit_resulting_resolution,[],[f100,f334,f121,f513,f55])).

fof(f2103,plain,
    ( spl7_56
    | ~ spl7_3
    | ~ spl7_25
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f584,f506,f337,f98,f2100])).

fof(f2100,plain,
    ( spl7_56
  <=> r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_56])])).

fof(f584,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_25
    | ~ spl7_35 ),
    inference(unit_resulting_resolution,[],[f100,f339,f121,f508,f55])).

fof(f2098,plain,
    ( spl7_55
    | ~ spl7_3
    | ~ spl7_24
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f583,f506,f332,f98,f2095])).

fof(f2095,plain,
    ( spl7_55
  <=> r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK4,k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_55])])).

fof(f583,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK4,k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_24
    | ~ spl7_35 ),
    inference(unit_resulting_resolution,[],[f100,f334,f121,f508,f55])).

fof(f2093,plain,
    ( spl7_54
    | ~ spl7_3
    | ~ spl7_24
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f552,f501,f332,f98,f2090])).

fof(f2090,plain,
    ( spl7_54
  <=> r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK4,k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).

fof(f552,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK4,k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_24
    | ~ spl7_34 ),
    inference(unit_resulting_resolution,[],[f100,f334,f121,f503,f55])).

fof(f2088,plain,
    ( spl7_53
    | ~ spl7_3
    | ~ spl7_25
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f525,f496,f337,f98,f2085])).

fof(f2085,plain,
    ( spl7_53
  <=> r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f525,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_25
    | ~ spl7_33 ),
    inference(unit_resulting_resolution,[],[f100,f339,f121,f498,f55])).

fof(f2083,plain,
    ( spl7_52
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_13
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f329,f269,f194,f98,f88,f2080])).

fof(f2080,plain,
    ( spl7_52
  <=> r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f329,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_13
    | ~ spl7_20 ),
    inference(unit_resulting_resolution,[],[f90,f100,f121,f196,f271,f121,f57])).

fof(f2076,plain,
    ( spl7_51
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f325,f264,f166,f98,f88,f2073])).

fof(f2073,plain,
    ( spl7_51
  <=> r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).

fof(f325,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_19 ),
    inference(unit_resulting_resolution,[],[f90,f100,f121,f168,f266,f121,f57])).

fof(f2071,plain,
    ( spl7_50
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f292,f269,f161,f98,f2068])).

fof(f2068,plain,
    ( spl7_50
  <=> r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK4,sK4)))),k2_yellow_0(sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f292,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK4,sK4)))),k2_yellow_0(sK2,sK4))
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_20 ),
    inference(unit_resulting_resolution,[],[f100,f163,f121,f271,f55])).

fof(f2066,plain,
    ( spl7_49
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f278,f264,f156,f98,f2063])).

fof(f2063,plain,
    ( spl7_49
  <=> r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,sK3)))),k2_yellow_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).

fof(f278,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,sK3)))),k2_yellow_0(sK2,sK3))
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_19 ),
    inference(unit_resulting_resolution,[],[f100,f158,f121,f266,f55])).

fof(f757,plain,
    ( spl7_48
    | ~ spl7_3
    | ~ spl7_25
    | ~ spl7_29 ),
    inference(avatar_split_clause,[],[f480,f407,f337,f98,f754])).

fof(f480,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK3,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_25
    | ~ spl7_29 ),
    inference(unit_resulting_resolution,[],[f100,f339,f121,f409,f55])).

fof(f745,plain,
    ( spl7_47
    | ~ spl7_3
    | ~ spl7_24
    | ~ spl7_29 ),
    inference(avatar_split_clause,[],[f479,f407,f332,f98,f742])).

fof(f479,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK4,k2_xboole_0(sK3,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_24
    | ~ spl7_29 ),
    inference(unit_resulting_resolution,[],[f100,f334,f121,f409,f55])).

fof(f740,plain,
    ( spl7_46
    | ~ spl7_3
    | ~ spl7_25
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f458,f402,f337,f98,f737])).

fof(f458,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK3,k2_xboole_0(sK3,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_25
    | ~ spl7_28 ),
    inference(unit_resulting_resolution,[],[f100,f339,f121,f404,f55])).

fof(f735,plain,
    ( spl7_45
    | ~ spl7_3
    | ~ spl7_24
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f457,f402,f332,f98,f732])).

fof(f457,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,sK4))),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_24
    | ~ spl7_28 ),
    inference(unit_resulting_resolution,[],[f100,f334,f121,f404,f55])).

fof(f730,plain,
    ( spl7_44
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f393,f366,f361,f98,f727])).

fof(f393,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK4,sK4)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_26
    | ~ spl7_27 ),
    inference(unit_resulting_resolution,[],[f100,f363,f121,f368,f55])).

fof(f725,plain,
    ( spl7_43
    | ~ spl7_3
    | ~ spl7_14
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f392,f366,f199,f98,f722])).

fof(f392,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK4,sK4)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_14
    | ~ spl7_27 ),
    inference(unit_resulting_resolution,[],[f100,f201,f121,f368,f55])).

fof(f718,plain,
    ( spl7_42
    | ~ spl7_3
    | ~ spl7_14
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f381,f361,f199,f98,f715])).

fof(f381,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK4)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_14
    | ~ spl7_26 ),
    inference(forward_demodulation,[],[f377,f79])).

fof(f377,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK3)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_14
    | ~ spl7_26 ),
    inference(unit_resulting_resolution,[],[f100,f201,f121,f363,f55])).

fof(f713,plain,
    ( spl7_41
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_13
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f330,f237,f194,f98,f88,f710])).

fof(f330,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,sK4)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_13
    | ~ spl7_18 ),
    inference(unit_resulting_resolution,[],[f90,f100,f121,f196,f239,f121,f57])).

fof(f708,plain,
    ( spl7_40
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f326,f232,f166,f98,f88,f705])).

fof(f326,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK3)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_17 ),
    inference(unit_resulting_resolution,[],[f90,f100,f121,f168,f234,f121,f57])).

fof(f698,plain,
    ( spl7_39
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7
    | ~ spl7_10
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f691,f194,f166,f124,f98,f93,f695])).

fof(f691,plain,
    ( sP1(k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK3))
    | ~ spl7_2
    | ~ spl7_3
    | spl7_7
    | ~ spl7_10
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f95,f100,f121,f121,f196,f168,f126,f121,f75])).

fof(f652,plain,
    ( spl7_38
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f256,f237,f161,f98,f649])).

fof(f256,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,sK4))
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_18 ),
    inference(unit_resulting_resolution,[],[f100,f163,f121,f239,f55])).

fof(f647,plain,
    ( spl7_37
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f245,f232,f156,f98,f644])).

fof(f245,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,sK3))
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_17 ),
    inference(unit_resulting_resolution,[],[f100,f158,f121,f234,f55])).

fof(f514,plain,
    ( spl7_36
    | ~ spl7_3
    | ~ spl7_24
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f390,f366,f332,f98,f511])).

fof(f390,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK4,sK4)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_24
    | ~ spl7_27 ),
    inference(unit_resulting_resolution,[],[f100,f334,f121,f368,f55])).

fof(f509,plain,
    ( spl7_35
    | ~ spl7_3
    | ~ spl7_25
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f376,f361,f337,f98,f506])).

fof(f376,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK3,sK3)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_25
    | ~ spl7_26 ),
    inference(unit_resulting_resolution,[],[f100,f339,f121,f363,f55])).

fof(f504,plain,
    ( spl7_34
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_13
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f328,f211,f194,f98,f88,f501])).

fof(f328,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,sK4)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_13
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f90,f100,f121,f196,f213,f121,f57])).

fof(f499,plain,
    ( spl7_33
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f324,f206,f166,f98,f88,f496])).

fof(f324,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,sK3)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_15 ),
    inference(unit_resulting_resolution,[],[f90,f100,f121,f168,f208,f121,f57])).

fof(f443,plain,
    ( spl7_32
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f415,f199,f113,f98,f93,f440])).

fof(f415,plain,
    ( r1_orders_2(sK2,k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f95,f100,f115,f201,f121,f121,f82])).

fof(f428,plain,
    ( spl7_31
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f413,f161,f108,f98,f93,f425])).

fof(f108,plain,
    ( spl7_5
  <=> r2_yellow_0(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f413,plain,
    ( r1_orders_2(sK2,k2_yellow_0(sK2,sK4),k2_yellow_0(sK2,sK4))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_9 ),
    inference(unit_resulting_resolution,[],[f95,f100,f110,f163,f121,f121,f82])).

fof(f110,plain,
    ( r2_yellow_0(sK2,sK4)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f108])).

fof(f423,plain,
    ( spl7_30
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f411,f156,f103,f98,f93,f420])).

fof(f103,plain,
    ( spl7_4
  <=> r2_yellow_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f411,plain,
    ( r1_orders_2(sK2,k2_yellow_0(sK2,sK3),k2_yellow_0(sK2,sK3))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f95,f100,f105,f158,f121,f121,f82])).

fof(f105,plain,
    ( r2_yellow_0(sK2,sK3)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f410,plain,
    ( spl7_29
    | ~ spl7_3
    | ~ spl7_14
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f358,f337,f199,f98,f407])).

fof(f358,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK3,sK4)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_14
    | ~ spl7_25 ),
    inference(forward_demodulation,[],[f355,f79])).

fof(f355,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),sK4),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_14
    | ~ spl7_25 ),
    inference(unit_resulting_resolution,[],[f100,f201,f121,f339,f55])).

fof(f405,plain,
    ( spl7_28
    | ~ spl7_3
    | ~ spl7_14
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f348,f332,f199,f98,f402])).

fof(f348,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,sK4)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_14
    | ~ spl7_24 ),
    inference(forward_demodulation,[],[f345,f79])).

fof(f345,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),sK3),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_14
    | ~ spl7_24 ),
    inference(unit_resulting_resolution,[],[f100,f201,f121,f334,f55])).

fof(f369,plain,
    ( spl7_27
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f327,f194,f179,f98,f88,f366])).

fof(f327,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,sK4),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f90,f100,f121,f196,f181,f121,f57])).

fof(f364,plain,
    ( spl7_26
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f323,f174,f166,f98,f88,f361])).

fof(f323,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,sK3),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(unit_resulting_resolution,[],[f90,f100,f121,f168,f176,f121,f57])).

fof(f340,plain,
    ( spl7_25
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f322,f194,f161,f98,f88,f337])).

fof(f322,plain,
    ( r1_lattice3(sK2,sK4,k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f90,f100,f121,f196,f163,f121,f57])).

fof(f335,plain,
    ( spl7_24
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f321,f166,f156,f98,f88,f332])).

fof(f321,plain,
    ( r1_lattice3(sK2,sK3,k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f90,f100,f121,f168,f158,f121,f57])).

fof(f320,plain,
    ( spl7_23
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f227,f211,f179,f98,f317])).

fof(f227,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,sK4))
    | ~ spl7_3
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f100,f181,f121,f213,f55])).

fof(f315,plain,
    ( spl7_22
    | ~ spl7_3
    | ~ spl7_11
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f219,f206,f174,f98,f312])).

fof(f219,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,sK3))
    | ~ spl7_3
    | ~ spl7_11
    | ~ spl7_15 ),
    inference(unit_resulting_resolution,[],[f100,f176,f121,f208,f55])).

fof(f305,plain,
    ( spl7_21
    | ~ spl7_3
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f204,f199,f98,f302])).

fof(f204,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK4),k2_xboole_0(sK3,sK4)),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_3
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f100,f201,f121,f201,f55])).

fof(f272,plain,
    ( spl7_20
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f226,f211,f161,f98,f269])).

fof(f226,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,k2_xboole_0(sK4,sK4))),k2_yellow_0(sK2,sK4))
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f100,f163,f121,f213,f55])).

fof(f267,plain,
    ( spl7_19
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f218,f206,f156,f98,f264])).

fof(f218,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,k2_xboole_0(sK3,sK3))),k2_yellow_0(sK2,sK3))
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_15 ),
    inference(unit_resulting_resolution,[],[f100,f158,f121,f208,f55])).

fof(f240,plain,
    ( spl7_18
    | ~ spl7_3
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f191,f179,f98,f237])).

fof(f191,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK4,sK4),k2_xboole_0(sK4,sK4)),k2_yellow_0(sK2,sK4))
    | ~ spl7_3
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f100,f181,f121,f181,f55])).

fof(f235,plain,
    ( spl7_17
    | ~ spl7_3
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f186,f174,f98,f232])).

fof(f186,plain,
    ( r1_lattice3(sK2,k2_xboole_0(k2_xboole_0(sK3,sK3),k2_xboole_0(sK3,sK3)),k2_yellow_0(sK2,sK3))
    | ~ spl7_3
    | ~ spl7_11 ),
    inference(unit_resulting_resolution,[],[f100,f176,f121,f176,f55])).

fof(f214,plain,
    ( spl7_16
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f190,f179,f161,f98,f211])).

fof(f190,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,k2_xboole_0(sK4,sK4)),k2_yellow_0(sK2,sK4))
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f100,f163,f121,f181,f55])).

fof(f209,plain,
    ( spl7_15
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f185,f174,f156,f98,f206])).

fof(f185,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,sK3)),k2_yellow_0(sK2,sK3))
    | ~ spl7_3
    | ~ spl7_8
    | ~ spl7_11 ),
    inference(unit_resulting_resolution,[],[f100,f158,f121,f176,f55])).

fof(f202,plain,
    ( spl7_14
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f154,f113,f98,f93,f199])).

fof(f154,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,sK4),k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f95,f100,f115,f121,f83])).

fof(f83,plain,(
    ! [X2,X0] :
      ( r1_lattice3(X0,X2,k2_yellow_0(X0,X2))
      | ~ r2_yellow_0(X0,X2)
      | ~ m1_subset_1(k2_yellow_0(X0,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X2,X1)
      | ~ r2_yellow_0(X0,X2)
      | k2_yellow_0(X0,X2) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f197,plain,
    ( spl7_13
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f151,f113,f108,f98,f194])).

fof(f151,plain,
    ( r1_orders_2(sK2,k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),k2_yellow_0(sK2,sK4))
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f100,f110,f117,f115,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
      | ~ r2_yellow_0(X0,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
          | ~ r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1))
          | ~ r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( ( r2_yellow_0(X0,X2)
            & r2_yellow_0(X0,X1)
            & r1_tarski(X1,X2) )
         => r1_orders_2(X0,k2_yellow_0(X0,X2),k2_yellow_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_yellow_0)).

fof(f117,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f77,f79])).

fof(f77,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f182,plain,
    ( spl7_12
    | ~ spl7_3
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f171,f161,f98,f179])).

fof(f171,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK4,sK4),k2_yellow_0(sK2,sK4))
    | ~ spl7_3
    | ~ spl7_9 ),
    inference(unit_resulting_resolution,[],[f100,f163,f163,f121,f55])).

fof(f177,plain,
    ( spl7_11
    | ~ spl7_3
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f170,f156,f98,f174])).

fof(f170,plain,
    ( r1_lattice3(sK2,k2_xboole_0(sK3,sK3),k2_yellow_0(sK2,sK3))
    | ~ spl7_3
    | ~ spl7_8 ),
    inference(unit_resulting_resolution,[],[f100,f158,f158,f121,f55])).

fof(f169,plain,
    ( spl7_10
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f150,f113,f103,f98,f166])).

fof(f150,plain,
    ( r1_orders_2(sK2,k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)),k2_yellow_0(sK2,sK3))
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
    ( r1_lattice3(sK2,sK4,k2_yellow_0(sK2,sK4))
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
    ( r1_lattice3(sK2,sK3,k2_yellow_0(sK2,sK3))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f95,f100,f105,f121,f83])).

fof(f127,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f53,f124])).

fof(f53,plain,(
    k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)) != k11_lattice3(sK2,k2_yellow_0(sK2,sK3),k2_yellow_0(sK2,sK4)) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)) != k11_lattice3(sK2,k2_yellow_0(sK2,sK3),k2_yellow_0(sK2,sK4))
    & r2_yellow_0(sK2,k2_xboole_0(sK3,sK4))
    & r2_yellow_0(sK2,sK4)
    & r2_yellow_0(sK2,sK3)
    & l1_orders_2(sK2)
    & v5_orders_2(sK2)
    & v4_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f16,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k2_yellow_0(X0,k2_xboole_0(X1,X2)) != k11_lattice3(X0,k2_yellow_0(X0,X1),k2_yellow_0(X0,X2))
            & r2_yellow_0(X0,k2_xboole_0(X1,X2))
            & r2_yellow_0(X0,X2)
            & r2_yellow_0(X0,X1) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
   => ( ? [X2,X1] :
          ( k2_yellow_0(sK2,k2_xboole_0(X1,X2)) != k11_lattice3(sK2,k2_yellow_0(sK2,X1),k2_yellow_0(sK2,X2))
          & r2_yellow_0(sK2,k2_xboole_0(X1,X2))
          & r2_yellow_0(sK2,X2)
          & r2_yellow_0(sK2,X1) )
      & l1_orders_2(sK2)
      & v5_orders_2(sK2)
      & v4_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2,X1] :
        ( k2_yellow_0(sK2,k2_xboole_0(X1,X2)) != k11_lattice3(sK2,k2_yellow_0(sK2,X1),k2_yellow_0(sK2,X2))
        & r2_yellow_0(sK2,k2_xboole_0(X1,X2))
        & r2_yellow_0(sK2,X2)
        & r2_yellow_0(sK2,X1) )
   => ( k2_yellow_0(sK2,k2_xboole_0(sK3,sK4)) != k11_lattice3(sK2,k2_yellow_0(sK2,sK3),k2_yellow_0(sK2,sK4))
      & r2_yellow_0(sK2,k2_xboole_0(sK3,sK4))
      & r2_yellow_0(sK2,sK4)
      & r2_yellow_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k2_yellow_0(X0,k2_xboole_0(X1,X2)) != k11_lattice3(X0,k2_yellow_0(X0,X1),k2_yellow_0(X0,X2))
          & r2_yellow_0(X0,k2_xboole_0(X1,X2))
          & r2_yellow_0(X0,X2)
          & r2_yellow_0(X0,X1) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k2_yellow_0(X0,k2_xboole_0(X1,X2)) != k11_lattice3(X0,k2_yellow_0(X0,X1),k2_yellow_0(X0,X2))
          & r2_yellow_0(X0,k2_xboole_0(X1,X2))
          & r2_yellow_0(X0,X2)
          & r2_yellow_0(X0,X1) )
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
            ( ( r2_yellow_0(X0,k2_xboole_0(X1,X2))
              & r2_yellow_0(X0,X2)
              & r2_yellow_0(X0,X1) )
           => k2_yellow_0(X0,k2_xboole_0(X1,X2)) = k11_lattice3(X0,k2_yellow_0(X0,X1),k2_yellow_0(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1,X2] :
          ( ( r2_yellow_0(X0,k2_xboole_0(X1,X2))
            & r2_yellow_0(X0,X2)
            & r2_yellow_0(X0,X1) )
         => k2_yellow_0(X0,k2_xboole_0(X1,X2)) = k11_lattice3(X0,k2_yellow_0(X0,X1),k2_yellow_0(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_yellow_0)).

fof(f116,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f52,f113])).

fof(f52,plain,(
    r2_yellow_0(sK2,k2_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f36])).

fof(f111,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f51,f108])).

fof(f51,plain,(
    r2_yellow_0(sK2,sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f106,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f50,f103])).

fof(f50,plain,(
    r2_yellow_0(sK2,sK3) ),
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
