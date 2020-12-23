%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 587 expanded)
%              Number of leaves         :   14 ( 225 expanded)
%              Depth                    :   26
%              Number of atoms          :  567 (4931 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f140,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f94,f106,f110,f132,f139])).

fof(f139,plain,
    ( spl6_2
    | ~ spl6_3 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f137,f100])).

fof(f100,plain,
    ( r1_lattice3(sK0,sK3,sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl6_3
  <=> r1_lattice3(sK0,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f137,plain,
    ( ~ r1_lattice3(sK0,sK3,sK1)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f33,f51])).

fof(f51,plain,
    ( ~ r2_lattice3(sK0,sK3,sK1)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl6_2
  <=> r2_lattice3(sK0,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f33,plain,
    ( r2_lattice3(sK0,sK3,sK1)
    | ~ r1_lattice3(sK0,sK3,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( ( ~ r2_lattice3(sK0,sK3,sK2)
        & r2_lattice3(sK0,sK3,sK1) )
      | ( ~ r1_lattice3(sK0,sK3,sK1)
        & r1_lattice3(sK0,sK3,sK2) ) )
    & r1_orders_2(sK0,sK1,sK2)
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v4_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f17,f16,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ r2_lattice3(X0,X3,X2)
                      & r2_lattice3(X0,X3,X1) )
                    | ( ~ r1_lattice3(X0,X3,X1)
                      & r1_lattice3(X0,X3,X2) ) )
                & r1_orders_2(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v4_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r2_lattice3(sK0,X3,X2)
                    & r2_lattice3(sK0,X3,X1) )
                  | ( ~ r1_lattice3(sK0,X3,X1)
                    & r1_lattice3(sK0,X3,X2) ) )
              & r1_orders_2(sK0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v4_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ r2_lattice3(sK0,X3,X2)
                  & r2_lattice3(sK0,X3,X1) )
                | ( ~ r1_lattice3(sK0,X3,X1)
                  & r1_lattice3(sK0,X3,X2) ) )
            & r1_orders_2(sK0,X1,X2)
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ r2_lattice3(sK0,X3,X2)
                & r2_lattice3(sK0,X3,sK1) )
              | ( ~ r1_lattice3(sK0,X3,sK1)
                & r1_lattice3(sK0,X3,X2) ) )
          & r1_orders_2(sK0,sK1,X2)
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ r2_lattice3(sK0,X3,X2)
              & r2_lattice3(sK0,X3,sK1) )
            | ( ~ r1_lattice3(sK0,X3,sK1)
              & r1_lattice3(sK0,X3,X2) ) )
        & r1_orders_2(sK0,sK1,X2)
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ? [X3] :
          ( ( ~ r2_lattice3(sK0,X3,sK2)
            & r2_lattice3(sK0,X3,sK1) )
          | ( ~ r1_lattice3(sK0,X3,sK1)
            & r1_lattice3(sK0,X3,sK2) ) )
      & r1_orders_2(sK0,sK1,sK2)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X3] :
        ( ( ~ r2_lattice3(sK0,X3,sK2)
          & r2_lattice3(sK0,X3,sK1) )
        | ( ~ r1_lattice3(sK0,X3,sK1)
          & r1_lattice3(sK0,X3,sK2) ) )
   => ( ( ~ r2_lattice3(sK0,sK3,sK2)
        & r2_lattice3(sK0,sK3,sK1) )
      | ( ~ r1_lattice3(sK0,sK3,sK1)
        & r1_lattice3(sK0,sK3,sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r2_lattice3(X0,X3,X2)
                    & r2_lattice3(X0,X3,X1) )
                  | ( ~ r1_lattice3(X0,X3,X1)
                    & r1_lattice3(X0,X3,X2) ) )
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r2_lattice3(X0,X3,X2)
                    & r2_lattice3(X0,X3,X1) )
                  | ( ~ r1_lattice3(X0,X3,X1)
                    & r1_lattice3(X0,X3,X2) ) )
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
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

fof(f132,plain,
    ( ~ spl6_1
    | spl6_3 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | ~ spl6_1
    | spl6_3 ),
    inference(subsumption_resolution,[],[f130,f31])).

fof(f31,plain,(
    r1_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f130,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | ~ spl6_1
    | spl6_3 ),
    inference(subsumption_resolution,[],[f127,f29])).

fof(f29,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f127,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ spl6_1
    | spl6_3 ),
    inference(resolution,[],[f126,f101])).

fof(f101,plain,
    ( ~ r1_lattice3(sK0,sK3,sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f99])).

fof(f126,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,sK3,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK2) )
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f125,f30])).

fof(f30,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f125,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,sK3,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK2) )
    | ~ spl6_1 ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,sK3,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK2)
        | r1_lattice3(sK0,sK3,X0) )
    | ~ spl6_1 ),
    inference(resolution,[],[f121,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK0,X1,sK4(sK0,X2,X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X0,X1)
      | r1_lattice3(sK0,X2,X0) ) ),
    inference(subsumption_resolution,[],[f72,f28])).

fof(f28,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X1,sK4(sK0,X2,X0))
      | r1_lattice3(sK0,X2,X0)
      | ~ l1_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X1,sK4(sK0,X2,X0))
      | r1_lattice3(sK0,X2,X0)
      | r1_lattice3(sK0,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f69,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
                & r2_hidden(sK4(X0,X1,X2),X1)
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
        & r2_hidden(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    inference(rectify,[],[f19])).

fof(f19,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
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
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK4(sK0,X2,X0),u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X1,sK4(sK0,X2,X0))
      | r1_lattice3(sK0,X2,X0) ) ),
    inference(subsumption_resolution,[],[f68,f28])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK0,X0,X1)
      | ~ m1_subset_1(sK4(sK0,X2,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X1,sK4(sK0,X2,X0))
      | r1_lattice3(sK0,X2,X0)
      | ~ l1_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK0,X0,X1)
      | ~ m1_subset_1(sK4(sK0,X2,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X1,sK4(sK0,X2,X0))
      | r1_lattice3(sK0,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f64,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(sK0,X2,X1)
      | ~ r1_orders_2(sK0,X2,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f63,f27])).

fof(f27,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK0,X0,X1)
      | ~ r1_orders_2(sK0,X2,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_orders_2(sK0,X2,X1)
      | ~ v4_orders_2(sK0) ) ),
    inference(resolution,[],[f44,f28])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X3)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                   => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_orders_2)).

fof(f121,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK2,sK4(sK0,sK3,X0))
        | r1_lattice3(sK0,sK3,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f120,f28])).

fof(f120,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK2,sK4(sK0,sK3,X0))
        | r1_lattice3(sK0,sK3,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl6_1 ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK2,sK4(sK0,sK3,X0))
        | r1_lattice3(sK0,sK3,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r1_lattice3(sK0,sK3,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl6_1 ),
    inference(resolution,[],[f113,f37])).

fof(f113,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4(X0,sK3,X1),u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2,sK4(X0,sK3,X1))
        | r1_lattice3(X0,sK3,X1)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_orders_2(X0) )
    | ~ spl6_1 ),
    inference(resolution,[],[f97,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f97,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2,X0) )
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f96,f28])).

fof(f96,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2,X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f95,f30])).

fof(f95,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK2,X0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl6_1 ),
    inference(resolution,[],[f48,f36])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X4)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f48,plain,
    ( r1_lattice3(sK0,sK3,sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl6_1
  <=> r1_lattice3(sK0,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f110,plain,
    ( ~ spl6_2
    | spl6_4 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | ~ spl6_2
    | spl6_4 ),
    inference(subsumption_resolution,[],[f108,f31])).

fof(f108,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | ~ spl6_2
    | spl6_4 ),
    inference(subsumption_resolution,[],[f107,f30])).

fof(f107,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ spl6_2
    | spl6_4 ),
    inference(resolution,[],[f105,f88])).

fof(f88,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,sK3,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0) )
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f87,f28])).

fof(f87,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,sK3,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl6_2 ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,sK3,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | r2_lattice3(sK0,sK3,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl6_2 ),
    inference(resolution,[],[f85,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
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
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f85,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK0,sK3,X0),u1_struct_0(sK0))
        | r2_lattice3(sK0,sK3,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0) )
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f84,f28])).

fof(f84,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK1,X0)
        | r2_lattice3(sK0,sK3,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,sK3,X0),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl6_2 ),
    inference(duplicate_literal_removal,[],[f83])).

fof(f83,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK1,X0)
        | r2_lattice3(sK0,sK3,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,sK3,X0),u1_struct_0(sK0))
        | r2_lattice3(sK0,sK3,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl6_2 ),
    inference(resolution,[],[f82,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK5(sK0,X1,X0),sK3)
        | ~ r1_orders_2(sK0,sK1,X0)
        | r2_lattice3(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,X1,X0),u1_struct_0(sK0)) )
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f79,f29])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | r2_lattice3(sK0,X1,X0)
        | ~ r2_hidden(sK5(sK0,X1,X0),sK3)
        | ~ m1_subset_1(sK5(sK0,X1,X0),u1_struct_0(sK0)) )
    | ~ spl6_2 ),
    inference(resolution,[],[f78,f57])).

fof(f57,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK1)
        | ~ r2_hidden(X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f56,f29])).

fof(f56,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK3)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK1) )
    | ~ spl6_2 ),
    inference(resolution,[],[f55,f52])).

fof(f52,plain,
    ( r2_lattice3(sK0,sK3,sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(sK0,X1,X2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r1_orders_2(sK0,X0,X2) ) ),
    inference(resolution,[],[f40,f28])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X4,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(sK0,sK5(sK0,X2,X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X1,X0)
      | r2_lattice3(sK0,X2,X0) ) ),
    inference(subsumption_resolution,[],[f77,f28])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,sK5(sK0,X2,X0),X1)
      | ~ r1_orders_2(sK0,X1,X0)
      | r2_lattice3(sK0,X2,X0)
      | ~ l1_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,sK5(sK0,X2,X0),X1)
      | ~ r1_orders_2(sK0,X1,X0)
      | r2_lattice3(sK0,X2,X0)
      | r2_lattice3(sK0,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f70,f41])).

fof(f70,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(sK5(sK0,X3,X4),u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,sK5(sK0,X3,X4),X5)
      | ~ r1_orders_2(sK0,X5,X4)
      | r2_lattice3(sK0,X3,X4) ) ),
    inference(subsumption_resolution,[],[f67,f28])).

fof(f67,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_orders_2(sK0,sK5(sK0,X3,X4),X5)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(sK5(sK0,X3,X4),u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X5,X4)
      | r2_lattice3(sK0,X3,X4)
      | ~ l1_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f66])).

fof(f66,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_orders_2(sK0,sK5(sK0,X3,X4),X5)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(sK5(sK0,X3,X4),u1_struct_0(sK0))
      | ~ r1_orders_2(sK0,X5,X4)
      | r2_lattice3(sK0,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f64,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f105,plain,
    ( ~ r2_lattice3(sK0,sK3,sK2)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl6_4
  <=> r2_lattice3(sK0,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f106,plain,
    ( ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f35,f103,f99])).

fof(f35,plain,
    ( ~ r2_lattice3(sK0,sK3,sK2)
    | ~ r1_lattice3(sK0,sK3,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f94,plain,
    ( spl6_1
    | ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f92,f31])).

fof(f92,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | spl6_1
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f89,f30])).

fof(f89,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK2)
    | spl6_1
    | ~ spl6_2 ),
    inference(resolution,[],[f88,f54])).

fof(f54,plain,
    ( ~ r2_lattice3(sK0,sK3,sK2)
    | spl6_1 ),
    inference(subsumption_resolution,[],[f34,f47])).

fof(f47,plain,
    ( ~ r1_lattice3(sK0,sK3,sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f46])).

fof(f34,plain,
    ( ~ r2_lattice3(sK0,sK3,sK2)
    | r1_lattice3(sK0,sK3,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f53,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f32,f50,f46])).

fof(f32,plain,
    ( r2_lattice3(sK0,sK3,sK1)
    | r1_lattice3(sK0,sK3,sK2) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:06:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (31381)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.22/0.48  % (31375)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.22/0.48  % (31382)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.22/0.48  % (31369)dis+1011_10_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=64:nwc=4:sac=on:sp=occurrence_2 on theBenchmark
% 0.22/0.48  % (31369)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f140,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f53,f94,f106,f110,f132,f139])).
% 0.22/0.48  fof(f139,plain,(
% 0.22/0.48    spl6_2 | ~spl6_3),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f138])).
% 0.22/0.48  fof(f138,plain,(
% 0.22/0.48    $false | (spl6_2 | ~spl6_3)),
% 0.22/0.48    inference(subsumption_resolution,[],[f137,f100])).
% 0.22/0.48  fof(f100,plain,(
% 0.22/0.48    r1_lattice3(sK0,sK3,sK1) | ~spl6_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f99])).
% 0.22/0.48  fof(f99,plain,(
% 0.22/0.48    spl6_3 <=> r1_lattice3(sK0,sK3,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.48  fof(f137,plain,(
% 0.22/0.48    ~r1_lattice3(sK0,sK3,sK1) | spl6_2),
% 0.22/0.48    inference(subsumption_resolution,[],[f33,f51])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    ~r2_lattice3(sK0,sK3,sK1) | spl6_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f50])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    spl6_2 <=> r2_lattice3(sK0,sK3,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    r2_lattice3(sK0,sK3,sK1) | ~r1_lattice3(sK0,sK3,sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ((((~r2_lattice3(sK0,sK3,sK2) & r2_lattice3(sK0,sK3,sK1)) | (~r1_lattice3(sK0,sK3,sK1) & r1_lattice3(sK0,sK3,sK2))) & r1_orders_2(sK0,sK1,sK2) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v4_orders_2(sK0)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f17,f16,f15,f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(X0,X3,X2) & r2_lattice3(X0,X3,X1)) | (~r1_lattice3(X0,X3,X1) & r1_lattice3(X0,X3,X2))) & r1_orders_2(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v4_orders_2(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(sK0,X3,X2) & r2_lattice3(sK0,X3,X1)) | (~r1_lattice3(sK0,X3,X1) & r1_lattice3(sK0,X3,X2))) & r1_orders_2(sK0,X1,X2) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v4_orders_2(sK0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(sK0,X3,X2) & r2_lattice3(sK0,X3,X1)) | (~r1_lattice3(sK0,X3,X1) & r1_lattice3(sK0,X3,X2))) & r1_orders_2(sK0,X1,X2) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : ((~r2_lattice3(sK0,X3,X2) & r2_lattice3(sK0,X3,sK1)) | (~r1_lattice3(sK0,X3,sK1) & r1_lattice3(sK0,X3,X2))) & r1_orders_2(sK0,sK1,X2) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ? [X2] : (? [X3] : ((~r2_lattice3(sK0,X3,X2) & r2_lattice3(sK0,X3,sK1)) | (~r1_lattice3(sK0,X3,sK1) & r1_lattice3(sK0,X3,X2))) & r1_orders_2(sK0,sK1,X2) & m1_subset_1(X2,u1_struct_0(sK0))) => (? [X3] : ((~r2_lattice3(sK0,X3,sK2) & r2_lattice3(sK0,X3,sK1)) | (~r1_lattice3(sK0,X3,sK1) & r1_lattice3(sK0,X3,sK2))) & r1_orders_2(sK0,sK1,sK2) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ? [X3] : ((~r2_lattice3(sK0,X3,sK2) & r2_lattice3(sK0,X3,sK1)) | (~r1_lattice3(sK0,X3,sK1) & r1_lattice3(sK0,X3,sK2))) => ((~r2_lattice3(sK0,sK3,sK2) & r2_lattice3(sK0,sK3,sK1)) | (~r1_lattice3(sK0,sK3,sK1) & r1_lattice3(sK0,sK3,sK2)))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f7,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r2_lattice3(X0,X3,X2) & r2_lattice3(X0,X3,X1)) | (~r1_lattice3(X0,X3,X1) & r1_lattice3(X0,X3,X2))) & r1_orders_2(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 0.22/0.48    inference(flattening,[],[f6])).
% 0.22/0.48  fof(f6,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~r2_lattice3(X0,X3,X2) & r2_lattice3(X0,X3,X1)) | (~r1_lattice3(X0,X3,X1) & r1_lattice3(X0,X3,X2))) & r1_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v4_orders_2(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,negated_conjecture,(
% 0.22/0.48    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) => ! [X3] : ((r2_lattice3(X0,X3,X1) => r2_lattice3(X0,X3,X2)) & (r1_lattice3(X0,X3,X2) => r1_lattice3(X0,X3,X1)))))))),
% 0.22/0.48    inference(negated_conjecture,[],[f4])).
% 0.22/0.48  fof(f4,conjecture,(
% 0.22/0.48    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) => ! [X3] : ((r2_lattice3(X0,X3,X1) => r2_lattice3(X0,X3,X2)) & (r1_lattice3(X0,X3,X2) => r1_lattice3(X0,X3,X1)))))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_0)).
% 0.22/0.48  fof(f132,plain,(
% 0.22/0.48    ~spl6_1 | spl6_3),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f131])).
% 0.22/0.48  fof(f131,plain,(
% 0.22/0.48    $false | (~spl6_1 | spl6_3)),
% 0.22/0.48    inference(subsumption_resolution,[],[f130,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    r1_orders_2(sK0,sK1,sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f130,plain,(
% 0.22/0.48    ~r1_orders_2(sK0,sK1,sK2) | (~spl6_1 | spl6_3)),
% 0.22/0.48    inference(subsumption_resolution,[],[f127,f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f127,plain,(
% 0.22/0.48    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK2) | (~spl6_1 | spl6_3)),
% 0.22/0.48    inference(resolution,[],[f126,f101])).
% 0.22/0.48  fof(f101,plain,(
% 0.22/0.48    ~r1_lattice3(sK0,sK3,sK1) | spl6_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f99])).
% 0.22/0.48  fof(f126,plain,(
% 0.22/0.48    ( ! [X0] : (r1_lattice3(sK0,sK3,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,sK2)) ) | ~spl6_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f125,f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f125,plain,(
% 0.22/0.48    ( ! [X0] : (r1_lattice3(sK0,sK3,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,sK2)) ) | ~spl6_1),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f122])).
% 0.22/0.48  fof(f122,plain,(
% 0.22/0.48    ( ! [X0] : (r1_lattice3(sK0,sK3,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,sK2) | r1_lattice3(sK0,sK3,X0)) ) | ~spl6_1),
% 0.22/0.48    inference(resolution,[],[f121,f73])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r1_orders_2(sK0,X1,sK4(sK0,X2,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | r1_lattice3(sK0,X2,X0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f72,f28])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    l1_orders_2(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK4(sK0,X2,X0)) | r1_lattice3(sK0,X2,X0) | ~l1_orders_2(sK0)) )),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f71])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK4(sK0,X2,X0)) | r1_lattice3(sK0,X2,X0) | r1_lattice3(sK0,X2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) )),
% 0.22/0.48    inference(resolution,[],[f69,f37])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK4(X0,X1,X2)) & r2_hidden(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK4(X0,X1,X2)) & r2_hidden(sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.48    inference(rectify,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.48    inference(nnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.48    inference(flattening,[],[f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(sK4(sK0,X2,X0),u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK4(sK0,X2,X0)) | r1_lattice3(sK0,X2,X0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f68,f28])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(sK4(sK0,X2,X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK4(sK0,X2,X0)) | r1_lattice3(sK0,X2,X0) | ~l1_orders_2(sK0)) )),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f65])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(sK4(sK0,X2,X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,sK4(sK0,X2,X0)) | r1_lattice3(sK0,X2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) )),
% 0.22/0.48    inference(resolution,[],[f64,f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X2,sK4(X0,X1,X2)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_orders_2(sK0,X2,X1) | ~r1_orders_2(sK0,X2,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f63,f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    v4_orders_2(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~r1_orders_2(sK0,X2,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r1_orders_2(sK0,X2,X1) | ~v4_orders_2(sK0)) )),
% 0.22/0.48    inference(resolution,[],[f44,f28])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X3) | ~v4_orders_2(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v4_orders_2(X0))),
% 0.22/0.48    inference(flattening,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_orders_2(X0,X1,X3) | (~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v4_orders_2(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) => r1_orders_2(X0,X1,X3))))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_orders_2)).
% 0.22/0.48  fof(f121,plain,(
% 0.22/0.48    ( ! [X0] : (r1_orders_2(sK0,sK2,sK4(sK0,sK3,X0)) | r1_lattice3(sK0,sK3,X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl6_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f120,f28])).
% 0.22/0.48  fof(f120,plain,(
% 0.22/0.48    ( ! [X0] : (r1_orders_2(sK0,sK2,sK4(sK0,sK3,X0)) | r1_lattice3(sK0,sK3,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) ) | ~spl6_1),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f119])).
% 0.22/0.48  fof(f119,plain,(
% 0.22/0.48    ( ! [X0] : (r1_orders_2(sK0,sK2,sK4(sK0,sK3,X0)) | r1_lattice3(sK0,sK3,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r1_lattice3(sK0,sK3,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) ) | ~spl6_1),
% 0.22/0.48    inference(resolution,[],[f113,f37])).
% 0.22/0.48  fof(f113,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(sK4(X0,sK3,X1),u1_struct_0(sK0)) | r1_orders_2(sK0,sK2,sK4(X0,sK3,X1)) | r1_lattice3(X0,sK3,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) ) | ~spl6_1),
% 0.22/0.48    inference(resolution,[],[f97,f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f97,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(X0,sK3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,sK2,X0)) ) | ~spl6_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f96,f28])).
% 0.22/0.48  fof(f96,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(X0,sK3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,sK2,X0) | ~l1_orders_2(sK0)) ) | ~spl6_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f95,f30])).
% 0.22/0.48  fof(f95,plain,(
% 0.22/0.48    ( ! [X0] : (~r2_hidden(X0,sK3) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,sK2,X0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) ) | ~spl6_1),
% 0.22/0.48    inference(resolution,[],[f48,f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X1] : (~r1_lattice3(X0,X1,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_orders_2(X0,X2,X4) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f22])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    r1_lattice3(sK0,sK3,sK2) | ~spl6_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f46])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    spl6_1 <=> r1_lattice3(sK0,sK3,sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.48  fof(f110,plain,(
% 0.22/0.48    ~spl6_2 | spl6_4),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f109])).
% 0.22/0.48  fof(f109,plain,(
% 0.22/0.48    $false | (~spl6_2 | spl6_4)),
% 0.22/0.48    inference(subsumption_resolution,[],[f108,f31])).
% 0.22/0.48  fof(f108,plain,(
% 0.22/0.48    ~r1_orders_2(sK0,sK1,sK2) | (~spl6_2 | spl6_4)),
% 0.22/0.48    inference(subsumption_resolution,[],[f107,f30])).
% 0.22/0.48  fof(f107,plain,(
% 0.22/0.48    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK2) | (~spl6_2 | spl6_4)),
% 0.22/0.48    inference(resolution,[],[f105,f88])).
% 0.22/0.48  fof(f88,plain,(
% 0.22/0.48    ( ! [X0] : (r2_lattice3(sK0,sK3,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,X0)) ) | ~spl6_2),
% 0.22/0.48    inference(subsumption_resolution,[],[f87,f28])).
% 0.22/0.48  fof(f87,plain,(
% 0.22/0.48    ( ! [X0] : (r2_lattice3(sK0,sK3,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,X0) | ~l1_orders_2(sK0)) ) | ~spl6_2),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f86])).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    ( ! [X0] : (r2_lattice3(sK0,sK3,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,X0) | r2_lattice3(sK0,sK3,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) ) | ~spl6_2),
% 0.22/0.48    inference(resolution,[],[f85,f41])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK5(X0,X1,X2),X2) & r2_hidden(sK5(X0,X1,X2),X1) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK5(X0,X1,X2),X2) & r2_hidden(sK5(X0,X1,X2),X1) & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.48    inference(rectify,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.48    inference(nnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.48    inference(flattening,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    ( ! [X0] : (~m1_subset_1(sK5(sK0,sK3,X0),u1_struct_0(sK0)) | r2_lattice3(sK0,sK3,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,X0)) ) | ~spl6_2),
% 0.22/0.48    inference(subsumption_resolution,[],[f84,f28])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    ( ! [X0] : (~r1_orders_2(sK0,sK1,X0) | r2_lattice3(sK0,sK3,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,sK3,X0),u1_struct_0(sK0)) | ~l1_orders_2(sK0)) ) | ~spl6_2),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f83])).
% 0.22/0.48  fof(f83,plain,(
% 0.22/0.48    ( ! [X0] : (~r1_orders_2(sK0,sK1,X0) | r2_lattice3(sK0,sK3,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,sK3,X0),u1_struct_0(sK0)) | r2_lattice3(sK0,sK3,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) ) | ~spl6_2),
% 0.22/0.48    inference(resolution,[],[f82,f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f82,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_hidden(sK5(sK0,X1,X0),sK3) | ~r1_orders_2(sK0,sK1,X0) | r2_lattice3(sK0,X1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,X1,X0),u1_struct_0(sK0))) ) | ~spl6_2),
% 0.22/0.48    inference(subsumption_resolution,[],[f79,f29])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,X0) | r2_lattice3(sK0,X1,X0) | ~r2_hidden(sK5(sK0,X1,X0),sK3) | ~m1_subset_1(sK5(sK0,X1,X0),u1_struct_0(sK0))) ) | ~spl6_2),
% 0.22/0.48    inference(resolution,[],[f78,f57])).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    ( ! [X0] : (r1_orders_2(sK0,X0,sK1) | ~r2_hidden(X0,sK3) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl6_2),
% 0.22/0.48    inference(subsumption_resolution,[],[f56,f29])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK3) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,sK1)) ) | ~spl6_2),
% 0.22/0.48    inference(resolution,[],[f55,f52])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    r2_lattice3(sK0,sK3,sK1) | ~spl6_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f50])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r2_lattice3(sK0,X1,X2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,X1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,X2)) )),
% 0.22/0.48    inference(resolution,[],[f40,f28])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X4,X2,X0,X1] : (~l1_orders_2(X0) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X4,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r1_orders_2(sK0,sK5(sK0,X2,X0),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X1,X0) | r2_lattice3(sK0,X2,X0)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f77,f28])).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X2,X0),X1) | ~r1_orders_2(sK0,X1,X0) | r2_lattice3(sK0,X2,X0) | ~l1_orders_2(sK0)) )),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f76])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X2,X0),X1) | ~r1_orders_2(sK0,X1,X0) | r2_lattice3(sK0,X2,X0) | r2_lattice3(sK0,X2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) )),
% 0.22/0.48    inference(resolution,[],[f70,f41])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    ( ! [X4,X5,X3] : (~m1_subset_1(sK5(sK0,X3,X4),u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK5(sK0,X3,X4),X5) | ~r1_orders_2(sK0,X5,X4) | r2_lattice3(sK0,X3,X4)) )),
% 0.22/0.48    inference(subsumption_resolution,[],[f67,f28])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    ( ! [X4,X5,X3] : (~r1_orders_2(sK0,sK5(sK0,X3,X4),X5) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,X3,X4),u1_struct_0(sK0)) | ~r1_orders_2(sK0,X5,X4) | r2_lattice3(sK0,X3,X4) | ~l1_orders_2(sK0)) )),
% 0.22/0.48    inference(duplicate_literal_removal,[],[f66])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    ( ! [X4,X5,X3] : (~r1_orders_2(sK0,sK5(sK0,X3,X4),X5) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,X3,X4),u1_struct_0(sK0)) | ~r1_orders_2(sK0,X5,X4) | r2_lattice3(sK0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) )),
% 0.22/0.48    inference(resolution,[],[f64,f43])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r1_orders_2(X0,sK5(X0,X1,X2),X2) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f26])).
% 0.22/0.48  fof(f105,plain,(
% 0.22/0.48    ~r2_lattice3(sK0,sK3,sK2) | spl6_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f103])).
% 0.22/0.48  fof(f103,plain,(
% 0.22/0.48    spl6_4 <=> r2_lattice3(sK0,sK3,sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.48  fof(f106,plain,(
% 0.22/0.48    ~spl6_3 | ~spl6_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f35,f103,f99])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ~r2_lattice3(sK0,sK3,sK2) | ~r1_lattice3(sK0,sK3,sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f94,plain,(
% 0.22/0.48    spl6_1 | ~spl6_2),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f93])).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    $false | (spl6_1 | ~spl6_2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f92,f31])).
% 0.22/0.48  fof(f92,plain,(
% 0.22/0.48    ~r1_orders_2(sK0,sK1,sK2) | (spl6_1 | ~spl6_2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f89,f30])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK1,sK2) | (spl6_1 | ~spl6_2)),
% 0.22/0.48    inference(resolution,[],[f88,f54])).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    ~r2_lattice3(sK0,sK3,sK2) | spl6_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f34,f47])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ~r1_lattice3(sK0,sK3,sK2) | spl6_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f46])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ~r2_lattice3(sK0,sK3,sK2) | r1_lattice3(sK0,sK3,sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    spl6_1 | spl6_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f32,f50,f46])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    r2_lattice3(sK0,sK3,sK1) | r1_lattice3(sK0,sK3,sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (31369)------------------------------
% 0.22/0.48  % (31369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (31369)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (31369)Memory used [KB]: 5373
% 0.22/0.48  % (31369)Time elapsed: 0.065 s
% 0.22/0.48  % (31369)------------------------------
% 0.22/0.48  % (31369)------------------------------
% 0.22/0.49  % (31374)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.49  % (31368)Success in time 0.123 s
%------------------------------------------------------------------------------
