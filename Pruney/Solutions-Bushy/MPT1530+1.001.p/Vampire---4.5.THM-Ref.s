%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1530+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:01 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 560 expanded)
%              Number of leaves         :   31 ( 246 expanded)
%              Depth                    :   13
%              Number of atoms          :  977 (4490 expanded)
%              Number of equality atoms :   90 ( 370 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f409,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f98,f103,f108,f115,f121,f139,f144,f154,f160,f168,f171,f175,f179,f249,f252,f258,f282,f283,f285,f299,f307,f315,f350,f362,f374,f383,f392,f408])).

fof(f408,plain,
    ( spl7_14
    | spl7_7
    | spl7_8
    | spl7_9 ),
    inference(avatar_split_clause,[],[f407,f132,f128,f124,f165])).

fof(f165,plain,
    ( spl7_14
  <=> r1_orders_2(sK0,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f124,plain,
    ( spl7_7
  <=> r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f128,plain,
    ( spl7_8
  <=> r1_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f132,plain,
    ( spl7_9
  <=> r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f407,plain,
    ( r1_orders_2(sK0,sK3,sK1)
    | spl7_7
    | spl7_8
    | spl7_9 ),
    inference(subsumption_resolution,[],[f406,f125])).

fof(f125,plain,
    ( ~ r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f124])).

fof(f406,plain,
    ( r1_orders_2(sK0,sK3,sK1)
    | r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | spl7_8
    | spl7_9 ),
    inference(subsumption_resolution,[],[f405,f129])).

fof(f129,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f128])).

fof(f405,plain,
    ( r1_orders_2(sK0,sK3,sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | spl7_9 ),
    inference(subsumption_resolution,[],[f46,f133])).

fof(f133,plain,
    ( ~ r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | spl7_9 ),
    inference(avatar_component_clause,[],[f132])).

fof(f46,plain,
    ( r1_orders_2(sK0,sK3,sK1)
    | r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( ( ~ r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
        & r1_orders_2(sK0,sK3,sK1)
        & r1_orders_2(sK0,sK2,sK1) )
      | ( ( ~ r1_orders_2(sK0,sK3,sK1)
          | ~ r1_orders_2(sK0,sK2,sK1) )
        & r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1) )
      | ( ~ r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
        & r1_orders_2(sK0,sK1,sK3)
        & r1_orders_2(sK0,sK1,sK2) )
      | ( ( ~ r1_orders_2(sK0,sK1,sK3)
          | ~ r1_orders_2(sK0,sK1,sK2) )
        & r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1) ) )
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f7,f15,f14,f13,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ~ r2_lattice3(X0,k2_tarski(X2,X3),X1)
                        & r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) )
                      | ( ( ~ r1_orders_2(X0,X3,X1)
                          | ~ r1_orders_2(X0,X2,X1) )
                        & r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                      | ( ~ r1_lattice3(X0,k2_tarski(X2,X3),X1)
                        & r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ( ( ~ r1_orders_2(X0,X1,X3)
                          | ~ r1_orders_2(X0,X1,X2) )
                        & r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ r2_lattice3(sK0,k2_tarski(X2,X3),X1)
                      & r1_orders_2(sK0,X3,X1)
                      & r1_orders_2(sK0,X2,X1) )
                    | ( ( ~ r1_orders_2(sK0,X3,X1)
                        | ~ r1_orders_2(sK0,X2,X1) )
                      & r2_lattice3(sK0,k2_tarski(X2,X3),X1) )
                    | ( ~ r1_lattice3(sK0,k2_tarski(X2,X3),X1)
                      & r1_orders_2(sK0,X1,X3)
                      & r1_orders_2(sK0,X1,X2) )
                    | ( ( ~ r1_orders_2(sK0,X1,X3)
                        | ~ r1_orders_2(sK0,X1,X2) )
                      & r1_lattice3(sK0,k2_tarski(X2,X3),X1) ) )
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ~ r2_lattice3(sK0,k2_tarski(X2,X3),X1)
                    & r1_orders_2(sK0,X3,X1)
                    & r1_orders_2(sK0,X2,X1) )
                  | ( ( ~ r1_orders_2(sK0,X3,X1)
                      | ~ r1_orders_2(sK0,X2,X1) )
                    & r2_lattice3(sK0,k2_tarski(X2,X3),X1) )
                  | ( ~ r1_lattice3(sK0,k2_tarski(X2,X3),X1)
                    & r1_orders_2(sK0,X1,X3)
                    & r1_orders_2(sK0,X1,X2) )
                  | ( ( ~ r1_orders_2(sK0,X1,X3)
                      | ~ r1_orders_2(sK0,X1,X2) )
                    & r1_lattice3(sK0,k2_tarski(X2,X3),X1) ) )
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ~ r2_lattice3(sK0,k2_tarski(X2,X3),sK1)
                  & r1_orders_2(sK0,X3,sK1)
                  & r1_orders_2(sK0,X2,sK1) )
                | ( ( ~ r1_orders_2(sK0,X3,sK1)
                    | ~ r1_orders_2(sK0,X2,sK1) )
                  & r2_lattice3(sK0,k2_tarski(X2,X3),sK1) )
                | ( ~ r1_lattice3(sK0,k2_tarski(X2,X3),sK1)
                  & r1_orders_2(sK0,sK1,X3)
                  & r1_orders_2(sK0,sK1,X2) )
                | ( ( ~ r1_orders_2(sK0,sK1,X3)
                    | ~ r1_orders_2(sK0,sK1,X2) )
                  & r1_lattice3(sK0,k2_tarski(X2,X3),sK1) ) )
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ~ r2_lattice3(sK0,k2_tarski(X2,X3),sK1)
                & r1_orders_2(sK0,X3,sK1)
                & r1_orders_2(sK0,X2,sK1) )
              | ( ( ~ r1_orders_2(sK0,X3,sK1)
                  | ~ r1_orders_2(sK0,X2,sK1) )
                & r2_lattice3(sK0,k2_tarski(X2,X3),sK1) )
              | ( ~ r1_lattice3(sK0,k2_tarski(X2,X3),sK1)
                & r1_orders_2(sK0,sK1,X3)
                & r1_orders_2(sK0,sK1,X2) )
              | ( ( ~ r1_orders_2(sK0,sK1,X3)
                  | ~ r1_orders_2(sK0,sK1,X2) )
                & r1_lattice3(sK0,k2_tarski(X2,X3),sK1) ) )
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ? [X3] :
          ( ( ( ~ r2_lattice3(sK0,k2_tarski(sK2,X3),sK1)
              & r1_orders_2(sK0,X3,sK1)
              & r1_orders_2(sK0,sK2,sK1) )
            | ( ( ~ r1_orders_2(sK0,X3,sK1)
                | ~ r1_orders_2(sK0,sK2,sK1) )
              & r2_lattice3(sK0,k2_tarski(sK2,X3),sK1) )
            | ( ~ r1_lattice3(sK0,k2_tarski(sK2,X3),sK1)
              & r1_orders_2(sK0,sK1,X3)
              & r1_orders_2(sK0,sK1,sK2) )
            | ( ( ~ r1_orders_2(sK0,sK1,X3)
                | ~ r1_orders_2(sK0,sK1,sK2) )
              & r1_lattice3(sK0,k2_tarski(sK2,X3),sK1) ) )
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X3] :
        ( ( ( ~ r2_lattice3(sK0,k2_tarski(sK2,X3),sK1)
            & r1_orders_2(sK0,X3,sK1)
            & r1_orders_2(sK0,sK2,sK1) )
          | ( ( ~ r1_orders_2(sK0,X3,sK1)
              | ~ r1_orders_2(sK0,sK2,sK1) )
            & r2_lattice3(sK0,k2_tarski(sK2,X3),sK1) )
          | ( ~ r1_lattice3(sK0,k2_tarski(sK2,X3),sK1)
            & r1_orders_2(sK0,sK1,X3)
            & r1_orders_2(sK0,sK1,sK2) )
          | ( ( ~ r1_orders_2(sK0,sK1,X3)
              | ~ r1_orders_2(sK0,sK1,sK2) )
            & r1_lattice3(sK0,k2_tarski(sK2,X3),sK1) ) )
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ( ( ~ r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
          & r1_orders_2(sK0,sK3,sK1)
          & r1_orders_2(sK0,sK2,sK1) )
        | ( ( ~ r1_orders_2(sK0,sK3,sK1)
            | ~ r1_orders_2(sK0,sK2,sK1) )
          & r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1) )
        | ( ~ r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
          & r1_orders_2(sK0,sK1,sK3)
          & r1_orders_2(sK0,sK1,sK2) )
        | ( ( ~ r1_orders_2(sK0,sK1,sK3)
            | ~ r1_orders_2(sK0,sK1,sK2) )
          & r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1) ) )
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ r2_lattice3(X0,k2_tarski(X2,X3),X1)
                      & r1_orders_2(X0,X3,X1)
                      & r1_orders_2(X0,X2,X1) )
                    | ( ( ~ r1_orders_2(X0,X3,X1)
                        | ~ r1_orders_2(X0,X2,X1) )
                      & r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    | ( ~ r1_lattice3(X0,k2_tarski(X2,X3),X1)
                      & r1_orders_2(X0,X1,X3)
                      & r1_orders_2(X0,X1,X2) )
                    | ( ( ~ r1_orders_2(X0,X1,X3)
                        | ~ r1_orders_2(X0,X1,X2) )
                      & r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ r2_lattice3(X0,k2_tarski(X2,X3),X1)
                      & r1_orders_2(X0,X3,X1)
                      & r1_orders_2(X0,X2,X1) )
                    | ( ( ~ r1_orders_2(X0,X3,X1)
                        | ~ r1_orders_2(X0,X2,X1) )
                      & r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    | ( ~ r1_lattice3(X0,k2_tarski(X2,X3),X1)
                      & r1_orders_2(X0,X1,X3)
                      & r1_orders_2(X0,X1,X2) )
                    | ( ( ~ r1_orders_2(X0,X1,X3)
                        | ~ r1_orders_2(X0,X1,X2) )
                      & r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( ( r1_orders_2(X0,X3,X1)
                          & r1_orders_2(X0,X2,X1) )
                       => r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                      & ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
                       => ( r1_orders_2(X0,X3,X1)
                          & r1_orders_2(X0,X2,X1) ) )
                      & ( ( r1_orders_2(X0,X1,X3)
                          & r1_orders_2(X0,X1,X2) )
                       => r1_lattice3(X0,k2_tarski(X2,X3),X1) )
                      & ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
                       => ( r1_orders_2(X0,X1,X3)
                          & r1_orders_2(X0,X1,X2) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) )
                     => r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
                     => ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) ) )
                    & ( ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) )
                     => r1_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
                     => ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_yellow_0)).

fof(f392,plain,
    ( ~ spl7_3
    | spl7_10
    | ~ spl7_13 ),
    inference(avatar_contradiction_clause,[],[f391])).

fof(f391,plain,
    ( $false
    | ~ spl7_3
    | spl7_10
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f102,f87,f137,f159])).

fof(f159,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k2_tarski(sK2,sK3))
        | r1_orders_2(sK0,X0,sK1) )
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl7_13
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k2_tarski(sK2,sK3))
        | r1_orders_2(sK0,X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f137,plain,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl7_10
  <=> r1_orders_2(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f87,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK6(X0,X1,X2) != X1
              & sK6(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( sK6(X0,X1,X2) = X1
            | sK6(X0,X1,X2) = X0
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f27,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK6(X0,X1,X2) != X1
            & sK6(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( sK6(X0,X1,X2) = X1
          | sK6(X0,X1,X2) = X0
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f102,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl7_3
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f383,plain,
    ( spl7_10
    | ~ spl7_7
    | ~ spl7_8
    | spl7_9
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f382,f141,f132,f128,f124,f136])).

fof(f141,plain,
    ( spl7_11
  <=> r1_orders_2(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f382,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ spl7_7
    | ~ spl7_8
    | spl7_9
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f381,f130])).

fof(f130,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f128])).

fof(f381,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ spl7_7
    | spl7_9
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f380,f143])).

fof(f143,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f141])).

fof(f380,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ spl7_7
    | spl7_9 ),
    inference(subsumption_resolution,[],[f379,f126])).

fof(f126,plain,
    ( r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f124])).

fof(f379,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | spl7_9 ),
    inference(subsumption_resolution,[],[f39,f133])).

fof(f39,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f374,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | spl7_9
    | ~ spl7_10
    | ~ spl7_24 ),
    inference(avatar_contradiction_clause,[],[f373])).

fof(f373,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | spl7_9
    | ~ spl7_10
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f372,f92])).

fof(f92,plain,
    ( l1_orders_2(sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl7_1
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f372,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl7_2
    | spl7_9
    | ~ spl7_10
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f371,f97])).

fof(f97,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl7_2
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f371,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl7_9
    | ~ spl7_10
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f370,f133])).

fof(f370,plain,
    ( r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl7_10
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f368,f138])).

fof(f138,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f136])).

fof(f368,plain,
    ( ~ r1_orders_2(sK0,sK2,sK1)
    | r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl7_24 ),
    inference(superposition,[],[f77,f349])).

fof(f349,plain,
    ( sK2 = sK5(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f347])).

fof(f347,plain,
    ( spl7_24
  <=> sK2 = sK5(sK0,k2_tarski(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f22,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
        & r2_hidden(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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

fof(f362,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | spl7_9
    | ~ spl7_14
    | ~ spl7_23 ),
    inference(avatar_contradiction_clause,[],[f361])).

fof(f361,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | spl7_9
    | ~ spl7_14
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f360,f92])).

fof(f360,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl7_2
    | spl7_9
    | ~ spl7_14
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f359,f97])).

fof(f359,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl7_9
    | ~ spl7_14
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f358,f133])).

fof(f358,plain,
    ( r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl7_14
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f356,f167])).

fof(f167,plain,
    ( r1_orders_2(sK0,sK3,sK1)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f165])).

fof(f356,plain,
    ( ~ r1_orders_2(sK0,sK3,sK1)
    | r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl7_23 ),
    inference(superposition,[],[f77,f345])).

fof(f345,plain,
    ( sK3 = sK5(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f343])).

fof(f343,plain,
    ( spl7_23
  <=> sK3 = sK5(sK0,k2_tarski(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f350,plain,
    ( spl7_23
    | spl7_24
    | ~ spl7_2
    | spl7_9
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f314,f177,f132,f95,f347,f343])).

fof(f177,plain,
    ( spl7_16
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK0,k2_tarski(X1,X2),X0)
        | sK5(sK0,k2_tarski(X1,X2),X0) = X1
        | sK5(sK0,k2_tarski(X1,X2),X0) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f314,plain,
    ( sK2 = sK5(sK0,k2_tarski(sK2,sK3),sK1)
    | sK3 = sK5(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ spl7_2
    | spl7_9
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f313,f97])).

fof(f313,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK2 = sK5(sK0,k2_tarski(sK2,sK3),sK1)
    | sK3 = sK5(sK0,k2_tarski(sK2,sK3),sK1)
    | spl7_9
    | ~ spl7_16 ),
    inference(resolution,[],[f133,f178])).

fof(f178,plain,
    ( ! [X2,X0,X1] :
        ( r2_lattice3(sK0,k2_tarski(X1,X2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK5(sK0,k2_tarski(X1,X2),X0) = X1
        | sK5(sK0,k2_tarski(X1,X2),X0) = X2 )
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f177])).

fof(f315,plain,
    ( spl7_7
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_8
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f296,f246,f128,f95,f90,f124])).

fof(f246,plain,
    ( spl7_18
  <=> sK2 = sK4(sK0,k2_tarski(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f296,plain,
    ( r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_8
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f295,f92])).

fof(f295,plain,
    ( r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl7_2
    | ~ spl7_8
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f290,f97])).

fof(f290,plain,
    ( r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl7_8
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f288,f130])).

fof(f288,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl7_18 ),
    inference(superposition,[],[f73,f248])).

fof(f248,plain,
    ( sK2 = sK4(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f246])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f19])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
        & r2_hidden(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
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
    inference(rectify,[],[f17])).

fof(f17,plain,(
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

fof(f307,plain,
    ( ~ spl7_2
    | ~ spl7_4
    | ~ spl7_9
    | ~ spl7_12
    | spl7_14 ),
    inference(avatar_contradiction_clause,[],[f305])).

fof(f305,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_9
    | ~ spl7_12
    | spl7_14 ),
    inference(unit_resulting_resolution,[],[f85,f134,f97,f107,f166,f153])).

fof(f153,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_lattice3(sK0,X1,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X2) )
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl7_12
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f166,plain,
    ( ~ r1_orders_2(sK0,sK3,sK1)
    | spl7_14 ),
    inference(avatar_component_clause,[],[f165])).

fof(f107,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f105])).

% (4663)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
fof(f105,plain,
    ( spl7_4
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f134,plain,
    ( r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f132])).

fof(f85,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f299,plain,
    ( ~ spl7_7
    | ~ spl7_14
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f298,f141,f136,f132,f128,f165,f124])).

fof(f298,plain,
    ( ~ r1_orders_2(sK0,sK3,sK1)
    | ~ r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f297,f130])).

fof(f297,plain,
    ( ~ r1_orders_2(sK0,sK3,sK1)
    | ~ r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ spl7_9
    | ~ spl7_10
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f272,f143])).

fof(f272,plain,
    ( ~ r1_orders_2(sK0,sK3,sK1)
    | ~ r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f260,f134])).

fof(f260,plain,
    ( ~ r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ r1_orders_2(sK0,sK3,sK1)
    | ~ r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f69,f138])).

fof(f69,plain,
    ( ~ r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ r1_orders_2(sK0,sK3,sK1)
    | ~ r1_orders_2(sK0,sK2,sK1)
    | ~ r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f285,plain,
    ( spl7_11
    | ~ spl7_14
    | spl7_7
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f284,f136,f132,f124,f165,f141])).

fof(f284,plain,
    ( ~ r1_orders_2(sK0,sK3,sK1)
    | r1_orders_2(sK0,sK1,sK3)
    | spl7_7
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f271,f125])).

fof(f271,plain,
    ( ~ r1_orders_2(sK0,sK3,sK1)
    | r1_orders_2(sK0,sK1,sK3)
    | r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f270,f138])).

fof(f270,plain,
    ( ~ r1_orders_2(sK0,sK3,sK1)
    | ~ r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK1,sK3)
    | r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f66,f134])).

fof(f66,plain,
    ( ~ r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ r1_orders_2(sK0,sK3,sK1)
    | ~ r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK1,sK3)
    | r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f283,plain,
    ( spl7_8
    | ~ spl7_14
    | spl7_7
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f281,f136,f132,f124,f165,f128])).

fof(f281,plain,
    ( ~ r1_orders_2(sK0,sK3,sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | spl7_7
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f269,f125])).

fof(f269,plain,
    ( ~ r1_orders_2(sK0,sK3,sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f268,f138])).

fof(f268,plain,
    ( ~ r1_orders_2(sK0,sK3,sK1)
    | ~ r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f64,f134])).

fof(f64,plain,
    ( ~ r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ r1_orders_2(sK0,sK3,sK1)
    | ~ r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f282,plain,
    ( ~ spl7_11
    | ~ spl7_1
    | ~ spl7_2
    | spl7_7
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f280,f242,f124,f95,f90,f141])).

fof(f242,plain,
    ( spl7_17
  <=> sK3 = sK4(sK0,k2_tarski(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f280,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | ~ spl7_1
    | ~ spl7_2
    | spl7_7
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f279,f92])).

fof(f279,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | ~ l1_orders_2(sK0)
    | ~ spl7_2
    | spl7_7
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f278,f97])).

fof(f278,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl7_7
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f276,f125])).

fof(f276,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl7_17 ),
    inference(superposition,[],[f73,f244])).

fof(f244,plain,
    ( sK3 = sK4(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f242])).

fof(f258,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_7
    | spl7_8 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_7
    | spl7_8 ),
    inference(unit_resulting_resolution,[],[f92,f87,f126,f97,f102,f129,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X4)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f252,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_7
    | spl7_11 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_7
    | spl7_11 ),
    inference(unit_resulting_resolution,[],[f92,f97,f142,f107,f85,f126,f70])).

fof(f142,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | spl7_11 ),
    inference(avatar_component_clause,[],[f141])).

fof(f249,plain,
    ( spl7_17
    | spl7_18
    | ~ spl7_2
    | spl7_7
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f235,f173,f124,f95,f246,f242])).

fof(f173,plain,
    ( spl7_15
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattice3(sK0,k2_tarski(X1,X2),X0)
        | sK4(sK0,k2_tarski(X1,X2),X0) = X1
        | sK4(sK0,k2_tarski(X1,X2),X0) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f235,plain,
    ( sK2 = sK4(sK0,k2_tarski(sK2,sK3),sK1)
    | sK3 = sK4(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ spl7_2
    | spl7_7
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f232,f97])).

fof(f232,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK2 = sK4(sK0,k2_tarski(sK2,sK3),sK1)
    | sK3 = sK4(sK0,k2_tarski(sK2,sK3),sK1)
    | spl7_7
    | ~ spl7_15 ),
    inference(resolution,[],[f174,f125])).

fof(f174,plain,
    ( ! [X2,X0,X1] :
        ( r1_lattice3(sK0,k2_tarski(X1,X2),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK4(sK0,k2_tarski(X1,X2),X0) = X1
        | sK4(sK0,k2_tarski(X1,X2),X0) = X2 )
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f173])).

fof(f179,plain,
    ( spl7_16
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f122,f119,f177])).

fof(f119,plain,
    ( spl7_6
  <=> ! [X1,X0] :
        ( r2_hidden(sK5(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f122,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK0,k2_tarski(X1,X2),X0)
        | sK5(sK0,k2_tarski(X1,X2),X0) = X1
        | sK5(sK0,k2_tarski(X1,X2),X0) = X2 )
    | ~ spl7_6 ),
    inference(resolution,[],[f120,f88])).

fof(f88,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f120,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,X1) )
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f119])).

fof(f175,plain,
    ( spl7_15
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f117,f113,f173])).

fof(f113,plain,
    ( spl7_5
  <=> ! [X1,X0] :
        ( r2_hidden(sK4(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f117,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattice3(sK0,k2_tarski(X1,X2),X0)
        | sK4(sK0,k2_tarski(X1,X2),X0) = X1
        | sK4(sK0,k2_tarski(X1,X2),X0) = X2 )
    | ~ spl7_5 ),
    inference(resolution,[],[f114,f88])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,X1) )
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f113])).

fof(f171,plain,
    ( ~ spl7_7
    | spl7_14
    | ~ spl7_8
    | spl7_9
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f170,f141,f132,f128,f165,f124])).

fof(f170,plain,
    ( r1_orders_2(sK0,sK3,sK1)
    | ~ r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ spl7_8
    | spl7_9
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f169,f143])).

fof(f169,plain,
    ( r1_orders_2(sK0,sK3,sK1)
    | ~ r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ spl7_8
    | spl7_9 ),
    inference(subsumption_resolution,[],[f161,f133])).

fof(f161,plain,
    ( r1_orders_2(sK0,sK3,sK1)
    | r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f51,f130])).

fof(f51,plain,
    ( r1_orders_2(sK0,sK3,sK1)
    | r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f168,plain,
    ( spl7_7
    | spl7_11
    | spl7_14
    | spl7_9 ),
    inference(avatar_split_clause,[],[f163,f132,f165,f141,f124])).

fof(f163,plain,
    ( r1_orders_2(sK0,sK3,sK1)
    | r1_orders_2(sK0,sK1,sK3)
    | r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | spl7_9 ),
    inference(subsumption_resolution,[],[f48,f133])).

fof(f48,plain,
    ( r1_orders_2(sK0,sK3,sK1)
    | r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | r1_orders_2(sK0,sK1,sK3)
    | r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f160,plain,
    ( spl7_13
    | ~ spl7_2
    | ~ spl7_9
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f156,f152,f132,f95,f158])).

fof(f156,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k2_tarski(sK2,sK3))
        | r1_orders_2(sK0,X0,sK1) )
    | ~ spl7_2
    | ~ spl7_9
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f155,f97])).

fof(f155,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k2_tarski(sK2,sK3))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK1) )
    | ~ spl7_9
    | ~ spl7_12 ),
    inference(resolution,[],[f153,f134])).

fof(f154,plain,
    ( spl7_12
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f145,f90,f152])).

fof(f145,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,X2) )
    | ~ spl7_1 ),
    inference(resolution,[],[f74,f92])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X4,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f144,plain,
    ( spl7_7
    | spl7_11
    | spl7_9
    | spl7_10 ),
    inference(avatar_split_clause,[],[f36,f136,f132,f141,f124])).

fof(f36,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | r1_orders_2(sK0,sK1,sK3)
    | r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f139,plain,
    ( spl7_7
    | spl7_8
    | spl7_9
    | spl7_10 ),
    inference(avatar_split_clause,[],[f34,f136,f132,f128,f124])).

fof(f34,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r2_lattice3(sK0,k2_tarski(sK2,sK3),sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | r1_lattice3(sK0,k2_tarski(sK2,sK3),sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f121,plain,
    ( spl7_6
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f116,f90,f119])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,X1) )
    | ~ spl7_1 ),
    inference(resolution,[],[f76,f92])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f115,plain,
    ( spl7_5
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f111,f90,f113])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(sK0,X0,X1),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,X1) )
    | ~ spl7_1 ),
    inference(resolution,[],[f72,f92])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f108,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f33,f105])).

fof(f33,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f103,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f32,f100])).

fof(f32,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f98,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f31,f95])).

fof(f31,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f93,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f30,f90])).

fof(f30,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

%------------------------------------------------------------------------------
