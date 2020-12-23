%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : orders_2__t32_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:19 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 539 expanded)
%              Number of leaves         :   14 ( 244 expanded)
%              Depth                    :   14
%              Number of atoms          :  322 (5668 expanded)
%              Number of equality atoms :   15 (  60 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f139,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f75,f82,f110,f123,f138])).

fof(f138,plain,
    ( ~ spl6_0
    | spl6_3 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f125,f61])).

fof(f61,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl6_0
  <=> r2_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f125,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | ~ spl6_3 ),
    inference(unit_resulting_resolution,[],[f36,f37,f38,f64,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X0,X1,X2)
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t32_orders_2.p',d10_orders_2)).

fof(f64,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl6_3
  <=> ~ r1_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f38,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r2_orders_2(sK0,sK1,sK3)
    & ( ( r2_orders_2(sK0,sK2,sK3)
        & r1_orders_2(sK0,sK1,sK2) )
      | ( r1_orders_2(sK0,sK2,sK3)
        & r2_orders_2(sK0,sK1,sK2) ) )
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f26,f25,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_orders_2(X0,X1,X3)
                    & ( ( r2_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ( r1_orders_2(X0,X2,X3)
                        & r2_orders_2(X0,X1,X2) ) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_orders_2(sK0,X1,X3)
                  & ( ( r2_orders_2(sK0,X2,X3)
                      & r1_orders_2(sK0,X1,X2) )
                    | ( r1_orders_2(sK0,X2,X3)
                      & r2_orders_2(sK0,X1,X2) ) )
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_orders_2(X0,X1,X3)
                  & ( ( r2_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                    | ( r1_orders_2(X0,X2,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r2_orders_2(X0,sK1,X3)
                & ( ( r2_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,sK1,X2) )
                  | ( r1_orders_2(X0,X2,X3)
                    & r2_orders_2(X0,sK1,X2) ) )
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_orders_2(X0,X1,X3)
              & ( ( r2_orders_2(X0,X2,X3)
                  & r1_orders_2(X0,X1,X2) )
                | ( r1_orders_2(X0,X2,X3)
                  & r2_orders_2(X0,X1,X2) ) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_orders_2(X0,X1,X3)
            & ( ( r2_orders_2(X0,sK2,X3)
                & r1_orders_2(X0,X1,sK2) )
              | ( r1_orders_2(X0,sK2,X3)
                & r2_orders_2(X0,X1,sK2) ) )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_orders_2(X0,X1,X3)
          & ( ( r2_orders_2(X0,X2,X3)
              & r1_orders_2(X0,X1,X2) )
            | ( r1_orders_2(X0,X2,X3)
              & r2_orders_2(X0,X1,X2) ) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_orders_2(X0,X1,sK3)
        & ( ( r2_orders_2(X0,X2,sK3)
            & r1_orders_2(X0,X1,X2) )
          | ( r1_orders_2(X0,X2,sK3)
            & r2_orders_2(X0,X1,X2) ) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_orders_2(X0,X1,X3)
                  & ( ( r2_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                    | ( r1_orders_2(X0,X2,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_orders_2(X0,X1,X3)
                  & ( ( r2_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                    | ( r1_orders_2(X0,X2,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( ( r2_orders_2(X0,X2,X3)
                          & r1_orders_2(X0,X1,X2) )
                        | ( r1_orders_2(X0,X2,X3)
                          & r2_orders_2(X0,X1,X2) ) )
                     => r2_orders_2(X0,X1,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( r2_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ( r1_orders_2(X0,X2,X3)
                        & r2_orders_2(X0,X1,X2) ) )
                   => r2_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t32_orders_2.p',t32_orders_2)).

fof(f37,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f36,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f123,plain,
    ( ~ spl6_0
    | spl6_5
    | ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | ~ spl6_0
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f120,f61])).

fof(f120,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(backward_demodulation,[],[f117,f44])).

fof(f44,plain,(
    ~ r2_orders_2(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f117,plain,
    ( sK2 = sK3
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(unit_resulting_resolution,[],[f36,f38,f39,f71,f81,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | X1 = X2
      | r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f81,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl6_6
  <=> r1_orders_2(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f71,plain,
    ( ~ r2_orders_2(sK0,sK2,sK3)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl6_5
  <=> ~ r2_orders_2(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f39,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f110,plain,
    ( ~ spl6_2
    | ~ spl6_4 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f104,f83])).

fof(f83,plain,(
    ~ r2_orders_2(sK0,sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f36,f37,f54])).

fof(f54,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f53])).

fof(f53,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f104,plain,
    ( r2_orders_2(sK0,sK1,sK1)
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f101,f95])).

fof(f95,plain,
    ( r2_orders_2(sK0,sK2,sK1)
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f91,f74])).

fof(f74,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl6_4
  <=> r2_orders_2(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f91,plain,
    ( sK1 = sK3
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f36,f37,f39,f44,f90,f52])).

fof(f90,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f34,f36,f37,f67,f38,f89,f39,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox/benchmark/orders_2__t32_orders_2.p',t26_orders_2)).

fof(f89,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f36,f38,f74,f39,f50])).

fof(f67,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl6_2
  <=> r1_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f34,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f101,plain,
    ( sK1 = sK2
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(unit_resulting_resolution,[],[f35,f36,f38,f37,f67,f93,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,X1)
      | X1 = X2
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t32_orders_2.p',t25_orders_2)).

fof(f93,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(backward_demodulation,[],[f91,f89])).

fof(f35,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f82,plain,
    ( spl6_6
    | spl6_4 ),
    inference(avatar_split_clause,[],[f43,f73,f80])).

fof(f43,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | r1_orders_2(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,
    ( spl6_0
    | spl6_4 ),
    inference(avatar_split_clause,[],[f42,f73,f60])).

fof(f42,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f68,plain,
    ( spl6_0
    | spl6_2 ),
    inference(avatar_split_clause,[],[f40,f66,f60])).

fof(f40,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
