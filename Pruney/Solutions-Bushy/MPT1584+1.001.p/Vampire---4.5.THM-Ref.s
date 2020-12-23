%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1584+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:09 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 771 expanded)
%              Number of leaves         :   17 ( 340 expanded)
%              Depth                    :   12
%              Number of atoms          :  443 (7971 expanded)
%              Number of equality atoms :   26 ( 792 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f120,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f70,f75,f76,f95,f119])).

fof(f119,plain,
    ( spl7_2
    | ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | spl7_2
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f34,f35,f77,f37,f97,f99,f101,f103,f56])).

fof(f56,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_orders_2(X0,X4,X5)
      | ~ r1_orders_2(X1,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X1,X4,X5)
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X1,X4,X5)
      | X3 != X5
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X0,X2,X3)
                          | ~ r1_orders_2(X1,X4,X5)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X0,X2,X3)
                          | ~ r1_orders_2(X1,X4,X5)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X4,X5)
                              & X3 = X5
                              & X2 = X4 )
                           => r1_orders_2(X0,X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_yellow_0)).

fof(f103,plain,
    ( r1_orders_2(sK1,sK5(sK0,sK2,sK3),sK3)
    | spl7_2
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f79,f77,f96,f98,f101,f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f27,f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
        & r2_hidden(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

fof(f98,plain,
    ( r2_hidden(sK5(sK0,sK2,sK3),sK2)
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f34,f37,f64,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f64,plain,
    ( ~ r2_lattice3(sK0,sK2,sK3)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl7_2
  <=> r2_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f96,plain,
    ( r2_lattice3(sK1,sK2,sK3)
    | ~ spl7_4 ),
    inference(forward_demodulation,[],[f74,f39])).

fof(f39,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ( ~ r2_lattice3(sK0,sK2,sK3)
        & r2_lattice3(sK1,sK2,sK4) )
      | ( ~ r1_lattice3(sK0,sK2,sK3)
        & r1_lattice3(sK1,sK2,sK4) ) )
    & sK3 = sK4
    & m1_subset_1(sK4,u1_struct_0(sK1))
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_yellow_0(sK1,sK0)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f10,f24,f23,f22,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ( ( ~ r2_lattice3(X0,X2,X3)
                            & r2_lattice3(X1,X2,X4) )
                          | ( ~ r1_lattice3(X0,X2,X3)
                            & r1_lattice3(X1,X2,X4) ) )
                        & X3 = X4
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_yellow_0(X1,X0) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( ~ r2_lattice3(sK0,X2,X3)
                          & r2_lattice3(X1,X2,X4) )
                        | ( ~ r1_lattice3(sK0,X2,X3)
                          & r1_lattice3(X1,X2,X4) ) )
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,sK0) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ( ~ r2_lattice3(sK0,X2,X3)
                        & r2_lattice3(X1,X2,X4) )
                      | ( ~ r1_lattice3(sK0,X2,X3)
                        & r1_lattice3(X1,X2,X4) ) )
                    & X3 = X4
                    & m1_subset_1(X4,u1_struct_0(X1)) )
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_yellow_0(X1,sK0) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ( ~ r2_lattice3(sK0,X2,X3)
                      & r2_lattice3(sK1,X2,X4) )
                    | ( ~ r1_lattice3(sK0,X2,X3)
                      & r1_lattice3(sK1,X2,X4) ) )
                  & X3 = X4
                  & m1_subset_1(X4,u1_struct_0(sK1)) )
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_yellow_0(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ( ( ~ r2_lattice3(sK0,X2,X3)
                    & r2_lattice3(sK1,X2,X4) )
                  | ( ~ r1_lattice3(sK0,X2,X3)
                    & r1_lattice3(sK1,X2,X4) ) )
                & X3 = X4
                & m1_subset_1(X4,u1_struct_0(sK1)) )
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ( ( ~ r2_lattice3(sK0,sK2,X3)
                  & r2_lattice3(sK1,sK2,X4) )
                | ( ~ r1_lattice3(sK0,sK2,X3)
                  & r1_lattice3(sK1,sK2,X4) ) )
              & X3 = X4
              & m1_subset_1(X4,u1_struct_0(sK1)) )
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ( ( ~ r2_lattice3(sK0,sK2,X3)
                & r2_lattice3(sK1,sK2,X4) )
              | ( ~ r1_lattice3(sK0,sK2,X3)
                & r1_lattice3(sK1,sK2,X4) ) )
            & X3 = X4
            & m1_subset_1(X4,u1_struct_0(sK1)) )
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ? [X4] :
          ( ( ( ~ r2_lattice3(sK0,sK2,sK3)
              & r2_lattice3(sK1,sK2,X4) )
            | ( ~ r1_lattice3(sK0,sK2,sK3)
              & r1_lattice3(sK1,sK2,X4) ) )
          & sK3 = X4
          & m1_subset_1(X4,u1_struct_0(sK1)) )
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X4] :
        ( ( ( ~ r2_lattice3(sK0,sK2,sK3)
            & r2_lattice3(sK1,sK2,X4) )
          | ( ~ r1_lattice3(sK0,sK2,sK3)
            & r1_lattice3(sK1,sK2,X4) ) )
        & sK3 = X4
        & m1_subset_1(X4,u1_struct_0(sK1)) )
   => ( ( ( ~ r2_lattice3(sK0,sK2,sK3)
          & r2_lattice3(sK1,sK2,sK4) )
        | ( ~ r1_lattice3(sK0,sK2,sK3)
          & r1_lattice3(sK1,sK2,sK4) ) )
      & sK3 = sK4
      & m1_subset_1(sK4,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( ~ r2_lattice3(X0,X2,X3)
                          & r2_lattice3(X1,X2,X4) )
                        | ( ~ r1_lattice3(X0,X2,X3)
                          & r1_lattice3(X1,X2,X4) ) )
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,X0) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( ~ r2_lattice3(X0,X2,X3)
                          & r2_lattice3(X1,X2,X4) )
                        | ( ~ r1_lattice3(X0,X2,X3)
                          & r1_lattice3(X1,X2,X4) ) )
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,X0) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_yellow_0(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ( X3 = X4
                         => ( ( r2_lattice3(X1,X2,X4)
                             => r2_lattice3(X0,X2,X3) )
                            & ( r1_lattice3(X1,X2,X4)
                             => r1_lattice3(X0,X2,X3) ) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_yellow_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ( X3 = X4
                         => ( ( r2_lattice3(X1,X2,X4)
                             => r2_lattice3(X0,X2,X3) )
                            & ( r1_lattice3(X1,X2,X4)
                             => r1_lattice3(X0,X2,X3) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( X3 = X4
                       => ( ( r2_lattice3(X1,X2,X4)
                           => r2_lattice3(X0,X2,X3) )
                          & ( r1_lattice3(X1,X2,X4)
                           => r1_lattice3(X0,X2,X3) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_yellow_0)).

fof(f74,plain,
    ( r2_lattice3(sK1,sK2,sK4)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl7_4
  <=> r2_lattice3(sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f79,plain,(
    l1_orders_2(sK1) ),
    inference(unit_resulting_resolution,[],[f34,f35,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_yellow_0)).

fof(f101,plain,
    ( m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK1))
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f36,f98,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f99,plain,
    ( ~ r1_orders_2(sK0,sK5(sK0,sK2,sK3),sK3)
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f34,f37,f64,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f97,plain,
    ( m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0))
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f34,f37,f64,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f37,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f77,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f38,f39])).

fof(f38,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f35,plain,(
    m1_yellow_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f34,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f95,plain,
    ( spl7_1
    | ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | spl7_1
    | ~ spl7_3 ),
    inference(unit_resulting_resolution,[],[f34,f35,f37,f77,f80,f82,f83,f85,f56])).

fof(f85,plain,
    ( r1_orders_2(sK1,sK3,sK6(sK0,sK2,sK3))
    | spl7_1
    | ~ spl7_3 ),
    inference(unit_resulting_resolution,[],[f79,f77,f78,f81,f83,f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
        & r2_hidden(sK6(X0,X1,X2),X1)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).

fof(f81,plain,
    ( r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f34,f37,f60,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f60,plain,
    ( ~ r1_lattice3(sK0,sK2,sK3)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl7_1
  <=> r1_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f78,plain,
    ( r1_lattice3(sK1,sK2,sK3)
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f69,f39])).

fof(f69,plain,
    ( r1_lattice3(sK1,sK2,sK4)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl7_3
  <=> r1_lattice3(sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f83,plain,
    ( m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK1))
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f36,f81,f54])).

fof(f82,plain,
    ( ~ r1_orders_2(sK0,sK3,sK6(sK0,sK2,sK3))
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f34,f37,f60,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f80,plain,
    ( m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f34,f37,f60,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f76,plain,
    ( spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f40,f72,f67])).

fof(f40,plain,
    ( r2_lattice3(sK1,sK2,sK4)
    | r1_lattice3(sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f75,plain,
    ( ~ spl7_1
    | spl7_4 ),
    inference(avatar_split_clause,[],[f41,f72,f58])).

fof(f41,plain,
    ( r2_lattice3(sK1,sK2,sK4)
    | ~ r1_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f70,plain,
    ( spl7_3
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f42,f62,f67])).

fof(f42,plain,
    ( ~ r2_lattice3(sK0,sK2,sK3)
    | r1_lattice3(sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f65,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f43,f62,f58])).

fof(f43,plain,
    ( ~ r2_lattice3(sK0,sK2,sK3)
    | ~ r1_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

%------------------------------------------------------------------------------
