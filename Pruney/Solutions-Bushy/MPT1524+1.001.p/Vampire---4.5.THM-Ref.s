%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1524+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 728 expanded)
%              Number of leaves         :   18 ( 295 expanded)
%              Depth                    :   22
%              Number of atoms          :  629 (6743 expanded)
%              Number of equality atoms :   58 (1173 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f461,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f76,f77,f118,f125,f401,f460])).

fof(f460,plain,
    ( spl7_2
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f459])).

fof(f459,plain,
    ( $false
    | spl7_2
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f458,f34])).

fof(f34,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ( ~ r1_lattice3(sK1,sK2,sK4)
        & r1_lattice3(sK0,sK2,sK3) )
      | ( ~ r2_lattice3(sK1,sK2,sK4)
        & r2_lattice3(sK0,sK2,sK3) ) )
    & sK3 = sK4
    & m1_subset_1(sK4,u1_struct_0(sK1))
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    & l1_orders_2(sK1)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f9,f21,f20,f19,f18])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2,X3] :
                ( ? [X4] :
                    ( ( ( ~ r1_lattice3(X1,X2,X4)
                        & r1_lattice3(X0,X2,X3) )
                      | ( ~ r2_lattice3(X1,X2,X4)
                        & r2_lattice3(X0,X2,X3) ) )
                    & X3 = X4
                    & m1_subset_1(X4,u1_struct_0(X1)) )
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
            & l1_orders_2(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X3,X2] :
              ( ? [X4] :
                  ( ( ( ~ r1_lattice3(X1,X2,X4)
                      & r1_lattice3(sK0,X2,X3) )
                    | ( ~ r2_lattice3(X1,X2,X4)
                      & r2_lattice3(sK0,X2,X3) ) )
                  & X3 = X4
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
          & l1_orders_2(X1) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X1] :
        ( ? [X3,X2] :
            ( ? [X4] :
                ( ( ( ~ r1_lattice3(X1,X2,X4)
                    & r1_lattice3(sK0,X2,X3) )
                  | ( ~ r2_lattice3(X1,X2,X4)
                    & r2_lattice3(sK0,X2,X3) ) )
                & X3 = X4
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) = g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        & l1_orders_2(X1) )
   => ( ? [X3,X2] :
          ( ? [X4] :
              ( ( ( ~ r1_lattice3(sK1,X2,X4)
                  & r1_lattice3(sK0,X2,X3) )
                | ( ~ r2_lattice3(sK1,X2,X4)
                  & r2_lattice3(sK0,X2,X3) ) )
              & X3 = X4
              & m1_subset_1(X4,u1_struct_0(sK1)) )
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
      & l1_orders_2(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X3,X2] :
        ( ? [X4] :
            ( ( ( ~ r1_lattice3(sK1,X2,X4)
                & r1_lattice3(sK0,X2,X3) )
              | ( ~ r2_lattice3(sK1,X2,X4)
                & r2_lattice3(sK0,X2,X3) ) )
            & X3 = X4
            & m1_subset_1(X4,u1_struct_0(sK1)) )
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ? [X4] :
          ( ( ( ~ r1_lattice3(sK1,sK2,X4)
              & r1_lattice3(sK0,sK2,sK3) )
            | ( ~ r2_lattice3(sK1,sK2,X4)
              & r2_lattice3(sK0,sK2,sK3) ) )
          & sK3 = X4
          & m1_subset_1(X4,u1_struct_0(sK1)) )
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X4] :
        ( ( ( ~ r1_lattice3(sK1,sK2,X4)
            & r1_lattice3(sK0,sK2,sK3) )
          | ( ~ r2_lattice3(sK1,sK2,X4)
            & r2_lattice3(sK0,sK2,sK3) ) )
        & sK3 = X4
        & m1_subset_1(X4,u1_struct_0(sK1)) )
   => ( ( ( ~ r1_lattice3(sK1,sK2,sK4)
          & r1_lattice3(sK0,sK2,sK3) )
        | ( ~ r2_lattice3(sK1,sK2,sK4)
          & r2_lattice3(sK0,sK2,sK3) ) )
      & sK3 = sK4
      & m1_subset_1(sK4,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ( ( ~ r1_lattice3(X1,X2,X4)
                      & r1_lattice3(X0,X2,X3) )
                    | ( ~ r2_lattice3(X1,X2,X4)
                      & r2_lattice3(X0,X2,X3) ) )
                  & X3 = X4
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ( ( ~ r1_lattice3(X1,X2,X4)
                      & r1_lattice3(X0,X2,X3) )
                    | ( ~ r2_lattice3(X1,X2,X4)
                      & r2_lattice3(X0,X2,X3) ) )
                  & X3 = X4
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
             => ! [X2,X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( X3 = X4
                       => ( ( r1_lattice3(X0,X2,X3)
                           => r1_lattice3(X1,X2,X4) )
                          & ( r2_lattice3(X0,X2,X3)
                           => r2_lattice3(X1,X2,X4) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2,X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( X3 = X4
                     => ( ( r1_lattice3(X0,X2,X3)
                         => r1_lattice3(X1,X2,X4) )
                        & ( r2_lattice3(X0,X2,X3)
                         => r2_lattice3(X1,X2,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_yellow_0)).

fof(f458,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | spl7_2
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f457,f171])).

fof(f171,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl7_6 ),
    inference(equality_resolution,[],[f117])).

fof(f117,plain,
    ( ! [X14,X15] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X14,X15)
        | u1_struct_0(sK1) = X14 )
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl7_6
  <=> ! [X15,X14] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X14,X15)
        | u1_struct_0(sK1) = X14 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f457,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | spl7_2
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f456,f32])).

fof(f32,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f456,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | spl7_2
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f455,f290])).

fof(f290,plain,
    ( ~ r1_lattice3(sK1,sK2,sK3)
    | spl7_2 ),
    inference(forward_demodulation,[],[f65,f36])).

fof(f36,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f22])).

fof(f65,plain,
    ( ~ r1_lattice3(sK1,sK2,sK4)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl7_2
  <=> r1_lattice3(sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f455,plain,
    ( r1_lattice3(sK1,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | spl7_2
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(resolution,[],[f448,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
                & r2_hidden(sK6(X0,X1,X2),X1)
                & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
        & r2_hidden(sK6(X0,X1,X2),X1)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

fof(f448,plain,
    ( r1_orders_2(sK1,sK3,sK6(sK1,sK2,sK3))
    | spl7_2
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f447,f295])).

fof(f295,plain,
    ( m1_subset_1(sK6(sK1,sK2,sK3),u1_struct_0(sK0))
    | spl7_2
    | ~ spl7_6 ),
    inference(resolution,[],[f290,f176])).

fof(f176,plain,
    ( ! [X0] :
        ( r1_lattice3(sK1,X0,sK3)
        | m1_subset_1(sK6(sK1,X0,sK3),u1_struct_0(sK0)) )
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f95,f171])).

fof(f95,plain,(
    ! [X0] :
      ( r1_lattice3(sK1,X0,sK3)
      | m1_subset_1(sK6(sK1,X0,sK3),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f91,f32])).

fof(f91,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK1,X0,sK3),u1_struct_0(sK1))
      | r1_lattice3(sK1,X0,sK3)
      | ~ l1_orders_2(sK1) ) ),
    inference(resolution,[],[f86,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f86,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f35,f36])).

fof(f35,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f447,plain,
    ( ~ m1_subset_1(sK6(sK1,sK2,sK3),u1_struct_0(sK0))
    | r1_orders_2(sK1,sK3,sK6(sK1,sK2,sK3))
    | spl7_2
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f446,f34])).

fof(f446,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(sK1,sK2,sK3),u1_struct_0(sK0))
    | r1_orders_2(sK1,sK3,sK6(sK1,sK2,sK3))
    | spl7_2
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(resolution,[],[f323,f388])).

fof(f388,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK1,X1,X0) )
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f386,f31])).

fof(f31,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f386,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | r1_orders_2(sK1,X1,X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl7_6 ),
    inference(duplicate_literal_removal,[],[f385])).

fof(f385,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK1,X1,X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl7_6 ),
    inference(equality_resolution,[],[f275])).

fof(f275,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | r1_orders_2(sK1,X1,X2)
        | ~ l1_orders_2(X0) )
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f274,f171])).

fof(f274,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | ~ r1_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | r1_orders_2(sK1,X1,X2)
        | ~ l1_orders_2(X0) )
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f107,f171])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(sK1,X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f99,f32])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(sK1,X1,X2)
      | ~ l1_orders_2(sK1)
      | ~ l1_orders_2(X0) ) ),
    inference(superposition,[],[f57,f33])).

fof(f33,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f57,plain,(
    ! [X4,X0,X5,X1] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ r1_orders_2(X0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X1,X4,X5)
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r1_orders_2(X0,X2,X3)
      | X3 != X5
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_orders_2(X1,X4,X5)
                              | ~ r2_orders_2(X0,X2,X3) )
                            & ( r1_orders_2(X1,X4,X5)
                              | ~ r1_orders_2(X0,X2,X3) ) )
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_orders_2(X1,X4,X5)
                              | ~ r2_orders_2(X0,X2,X3) )
                            & ( r1_orders_2(X1,X4,X5)
                              | ~ r1_orders_2(X0,X2,X3) ) )
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( ( X3 = X5
                                & X2 = X4 )
                             => ( ( r2_orders_2(X0,X2,X3)
                                 => r2_orders_2(X1,X4,X5) )
                                & ( r1_orders_2(X0,X2,X3)
                                 => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_0)).

fof(f323,plain,
    ( r1_orders_2(sK0,sK3,sK6(sK1,sK2,sK3))
    | spl7_2
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f309,f296])).

fof(f296,plain,
    ( r2_hidden(sK6(sK1,sK2,sK3),sK2)
    | spl7_2 ),
    inference(resolution,[],[f290,f96])).

fof(f96,plain,(
    ! [X1] :
      ( r1_lattice3(sK1,X1,sK3)
      | r2_hidden(sK6(sK1,X1,sK3),X1) ) ),
    inference(subsumption_resolution,[],[f92,f32])).

fof(f92,plain,(
    ! [X1] :
      ( r2_hidden(sK6(sK1,X1,sK3),X1)
      | r1_lattice3(sK1,X1,sK3)
      | ~ l1_orders_2(sK1) ) ),
    inference(resolution,[],[f86,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(sK6(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f309,plain,
    ( ~ r2_hidden(sK6(sK1,sK2,sK3),sK2)
    | r1_orders_2(sK0,sK3,sK6(sK1,sK2,sK3))
    | spl7_2
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(resolution,[],[f295,f294])).

fof(f294,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK2)
        | r1_orders_2(sK0,sK3,X0) )
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f293,f31])).

fof(f293,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK3,X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f292,f34])).

fof(f292,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK3,X0)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl7_4 ),
    inference(resolution,[],[f75,f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X4)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f75,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl7_4
  <=> r1_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f401,plain,
    ( spl7_1
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f400])).

fof(f400,plain,
    ( $false
    | spl7_1
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f399,f34])).

fof(f399,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | spl7_1
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f398,f171])).

fof(f398,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | spl7_1
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f397,f32])).

fof(f397,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | spl7_1
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f396,f87])).

fof(f87,plain,
    ( ~ r2_lattice3(sK1,sK2,sK3)
    | spl7_1 ),
    inference(forward_demodulation,[],[f61,f36])).

fof(f61,plain,
    ( ~ r2_lattice3(sK1,sK2,sK4)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl7_1
  <=> r2_lattice3(sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f396,plain,
    ( r2_lattice3(sK1,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | spl7_1
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(resolution,[],[f395,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
                & r2_hidden(sK5(X0,X1,X2),X1)
                & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
        & r2_hidden(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

fof(f395,plain,
    ( r1_orders_2(sK1,sK5(sK1,sK2,sK3),sK3)
    | spl7_1
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f394,f34])).

fof(f394,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_orders_2(sK1,sK5(sK1,sK2,sK3),sK3)
    | spl7_1
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f390,f180])).

fof(f180,plain,
    ( m1_subset_1(sK5(sK1,sK2,sK3),u1_struct_0(sK0))
    | spl7_1
    | ~ spl7_6 ),
    inference(backward_demodulation,[],[f158,f171])).

fof(f158,plain,
    ( m1_subset_1(sK5(sK1,sK2,sK3),u1_struct_0(sK1))
    | spl7_1 ),
    inference(resolution,[],[f97,f87])).

fof(f97,plain,(
    ! [X2] :
      ( r2_lattice3(sK1,X2,sK3)
      | m1_subset_1(sK5(sK1,X2,sK3),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f93,f32])).

fof(f93,plain,(
    ! [X2] :
      ( m1_subset_1(sK5(sK1,X2,sK3),u1_struct_0(sK1))
      | r2_lattice3(sK1,X2,sK3)
      | ~ l1_orders_2(sK1) ) ),
    inference(resolution,[],[f86,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f390,plain,
    ( ~ m1_subset_1(sK5(sK1,sK2,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_orders_2(sK1,sK5(sK1,sK2,sK3),sK3)
    | spl7_1
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(resolution,[],[f388,f228])).

fof(f228,plain,
    ( r1_orders_2(sK0,sK5(sK1,sK2,sK3),sK3)
    | spl7_1
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f223,f135])).

fof(f135,plain,
    ( r2_hidden(sK5(sK1,sK2,sK3),sK2)
    | spl7_1 ),
    inference(resolution,[],[f98,f87])).

fof(f98,plain,(
    ! [X3] :
      ( r2_lattice3(sK1,X3,sK3)
      | r2_hidden(sK5(sK1,X3,sK3),X3) ) ),
    inference(subsumption_resolution,[],[f94,f32])).

fof(f94,plain,(
    ! [X3] :
      ( r2_hidden(sK5(sK1,X3,sK3),X3)
      | r2_lattice3(sK1,X3,sK3)
      | ~ l1_orders_2(sK1) ) ),
    inference(resolution,[],[f86,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f223,plain,
    ( ~ r2_hidden(sK5(sK1,sK2,sK3),sK2)
    | r1_orders_2(sK0,sK5(sK1,sK2,sK3),sK3)
    | spl7_1
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(resolution,[],[f180,f90])).

fof(f90,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK2)
        | r1_orders_2(sK0,X0,sK3) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f89,f31])).

fof(f89,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK3)
        | ~ l1_orders_2(sK0) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f88,f34])).

% (19855)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f88,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl7_3 ),
    inference(resolution,[],[f70,f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f70,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl7_3
  <=> r2_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f125,plain,(
    spl7_5 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | spl7_5 ),
    inference(subsumption_resolution,[],[f123,f32])).

fof(f123,plain,
    ( ~ l1_orders_2(sK1)
    | spl7_5 ),
    inference(resolution,[],[f114,f41])).

fof(f41,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f114,plain,
    ( ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | spl7_5 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl7_5
  <=> m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f118,plain,
    ( ~ spl7_5
    | spl7_6 ),
    inference(avatar_split_clause,[],[f104,f116,f112])).

fof(f104,plain,(
    ! [X14,X15] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(X14,X15)
      | u1_struct_0(sK1) = X14
      | ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ) ),
    inference(superposition,[],[f52,f33])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f77,plain,
    ( spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f37,f73,f68])).

fof(f37,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | r2_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f76,plain,
    ( ~ spl7_1
    | spl7_4 ),
    inference(avatar_split_clause,[],[f38,f73,f59])).

fof(f38,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ r2_lattice3(sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,
    ( spl7_3
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f39,f63,f68])).

fof(f39,plain,
    ( ~ r1_lattice3(sK1,sK2,sK4)
    | r2_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f66,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f40,f63,f59])).

fof(f40,plain,
    ( ~ r1_lattice3(sK1,sK2,sK4)
    | ~ r2_lattice3(sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f22])).

%------------------------------------------------------------------------------
