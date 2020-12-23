%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t2_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:40 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
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
fof(f943,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f131,f138,f145,f146,f223,f234,f833,f942])).

fof(f942,plain,
    ( spl11_1
    | ~ spl11_4
    | ~ spl11_18 ),
    inference(avatar_contradiction_clause,[],[f941])).

fof(f941,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f940,f77])).

fof(f77,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f33,f60,f59,f58,f57])).

fof(f57,plain,
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
          & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0] :
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
     => ( ? [X3,X2] :
            ( ? [X4] :
                ( ( ( ~ r1_lattice3(sK1,X2,X4)
                    & r1_lattice3(X0,X2,X3) )
                  | ( ~ r2_lattice3(sK1,X2,X4)
                    & r2_lattice3(X0,X2,X3) ) )
                & X3 = X4
                & m1_subset_1(X4,u1_struct_0(sK1)) )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        & l1_orders_2(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ? [X2,X3] :
          ( ? [X4] :
              ( ( ( ~ r1_lattice3(X1,X2,X4)
                  & r1_lattice3(X0,X2,X3) )
                | ( ~ r2_lattice3(X1,X2,X4)
                  & r2_lattice3(X0,X2,X3) ) )
              & X3 = X4
              & m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ? [X4] :
            ( ( ( ~ r1_lattice3(X1,sK2,X4)
                & r1_lattice3(X0,sK2,sK3) )
              | ( ~ r2_lattice3(X1,sK2,X4)
                & r2_lattice3(X0,sK2,sK3) ) )
            & sK3 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ( ( ~ r1_lattice3(X1,X2,X4)
              & r1_lattice3(X0,X2,X3) )
            | ( ~ r2_lattice3(X1,X2,X4)
              & r2_lattice3(X0,X2,X3) ) )
          & X3 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ( ( ~ r1_lattice3(X1,X2,sK4)
            & r1_lattice3(X0,X2,X3) )
          | ( ~ r2_lattice3(X1,X2,sK4)
            & r2_lattice3(X0,X2,X3) ) )
        & sK4 = X3
        & m1_subset_1(sK4,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
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
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/yellow_0__t2_yellow_0.p',t2_yellow_0)).

fof(f940,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_18 ),
    inference(forward_demodulation,[],[f939,f363])).

fof(f363,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1)
    | ~ spl11_18 ),
    inference(equality_resolution,[],[f222])).

fof(f222,plain,
    ( ! [X14,X15] :
        ( g1_orders_2(X14,X15) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_struct_0(sK1) = X14 )
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl11_18
  <=> ! [X15,X14] :
        ( g1_orders_2(X14,X15) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
        | u1_struct_0(sK1) = X14 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f939,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f938,f75])).

fof(f75,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f938,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f937,f171])).

fof(f171,plain,
    ( ~ r2_lattice3(sK1,sK2,sK3)
    | ~ spl11_1 ),
    inference(forward_demodulation,[],[f124,f79])).

fof(f79,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f61])).

fof(f124,plain,
    ( ~ r2_lattice3(sK1,sK2,sK4)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl11_1
  <=> ~ r2_lattice3(sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f937,plain,
    ( r2_lattice3(sK1,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_18 ),
    inference(resolution,[],[f877,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
                & r2_hidden(sK6(X0,X1,X2),X1)
                & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f67,f68])).

fof(f68,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
        & r2_hidden(sK6(X0,X1,X2),X1)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
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
    inference(rectify,[],[f66])).

fof(f66,plain,(
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
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t2_yellow_0.p',d9_lattice3)).

fof(f877,plain,
    ( r1_orders_2(sK1,sK6(sK1,sK2,sK3),sK3)
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f876,f77])).

fof(f876,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_orders_2(sK1,sK6(sK1,sK2,sK3),sK3)
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f875,f379])).

fof(f379,plain,
    ( m1_subset_1(sK6(sK1,sK2,sK3),u1_struct_0(sK0))
    | ~ spl11_1
    | ~ spl11_18 ),
    inference(backward_demodulation,[],[f363,f340])).

fof(f340,plain,
    ( m1_subset_1(sK6(sK1,sK2,sK3),u1_struct_0(sK1))
    | ~ spl11_1 ),
    inference(resolution,[],[f181,f171])).

fof(f181,plain,(
    ! [X0] :
      ( r2_lattice3(sK1,X0,sK3)
      | m1_subset_1(sK6(sK1,X0,sK3),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f175,f75])).

fof(f175,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(sK1,X0,sK3),u1_struct_0(sK1))
      | r2_lattice3(sK1,X0,sK3)
      | ~ l1_orders_2(sK1) ) ),
    inference(resolution,[],[f170,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f170,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f78,f79])).

fof(f78,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f61])).

fof(f875,plain,
    ( ~ m1_subset_1(sK6(sK1,sK2,sK3),u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_orders_2(sK1,sK6(sK1,sK2,sK3),sK3)
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_18 ),
    inference(resolution,[],[f418,f769])).

fof(f769,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK1,X1,X0) )
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f768,f74])).

fof(f74,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f768,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | r1_orders_2(sK1,X1,X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl11_18 ),
    inference(duplicate_literal_removal,[],[f767])).

fof(f767,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK1,X1,X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl11_18 ),
    inference(equality_resolution,[],[f563])).

fof(f563,plain,
    ( ! [X2,X0,X1] :
        ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | r1_orders_2(sK1,X1,X2)
        | ~ l1_orders_2(X0) )
    | ~ spl11_18 ),
    inference(forward_demodulation,[],[f562,f363])).

fof(f562,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        | ~ r1_orders_2(X0,X1,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(X0))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | r1_orders_2(sK1,X1,X2)
        | ~ l1_orders_2(X0) )
    | ~ spl11_18 ),
    inference(forward_demodulation,[],[f210,f363])).

fof(f210,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(sK1,X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f202,f75])).

fof(f202,plain,(
    ! [X2,X0,X1] :
      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(sK1,X1,X2)
      | ~ l1_orders_2(sK1)
      | ~ l1_orders_2(X0) ) ),
    inference(superposition,[],[f114,f76])).

fof(f76,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(cnf_transformation,[],[f61])).

fof(f114,plain,(
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
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
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
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/yellow_0__t2_yellow_0.p',t1_yellow_0)).

fof(f418,plain,
    ( r1_orders_2(sK0,sK6(sK1,sK2,sK3),sK3)
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f411,f294])).

fof(f294,plain,
    ( r2_hidden(sK6(sK1,sK2,sK3),sK2)
    | ~ spl11_1 ),
    inference(resolution,[],[f182,f171])).

fof(f182,plain,(
    ! [X1] :
      ( r2_lattice3(sK1,X1,sK3)
      | r2_hidden(sK6(sK1,X1,sK3),X1) ) ),
    inference(subsumption_resolution,[],[f176,f75])).

fof(f176,plain,(
    ! [X1] :
      ( r2_hidden(sK6(sK1,X1,sK3),X1)
      | r2_lattice3(sK1,X1,sK3)
      | ~ l1_orders_2(sK1) ) ),
    inference(resolution,[],[f170,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(sK6(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f411,plain,
    ( ~ r2_hidden(sK6(sK1,sK2,sK3),sK2)
    | r1_orders_2(sK0,sK6(sK1,sK2,sK3),sK3)
    | ~ spl11_1
    | ~ spl11_4
    | ~ spl11_18 ),
    inference(resolution,[],[f379,f174])).

fof(f174,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK2)
        | r1_orders_2(sK0,X0,sK3) )
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f173,f74])).

fof(f173,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK3)
        | ~ l1_orders_2(sK0) )
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f172,f77])).

fof(f172,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl11_4 ),
    inference(resolution,[],[f137,f93])).

fof(f93,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f137,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl11_4
  <=> r2_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f833,plain,
    ( spl11_3
    | ~ spl11_6
    | ~ spl11_18 ),
    inference(avatar_contradiction_clause,[],[f832])).

fof(f832,plain,
    ( $false
    | ~ spl11_3
    | ~ spl11_6
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f831,f77])).

fof(f831,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl11_3
    | ~ spl11_6
    | ~ spl11_18 ),
    inference(forward_demodulation,[],[f830,f363])).

fof(f830,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl11_3
    | ~ spl11_6
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f829,f75])).

fof(f829,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl11_3
    | ~ spl11_6
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f828,f600])).

fof(f600,plain,
    ( ~ r1_lattice3(sK1,sK2,sK3)
    | ~ spl11_3 ),
    inference(forward_demodulation,[],[f130,f79])).

fof(f130,plain,
    ( ~ r1_lattice3(sK1,sK2,sK4)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl11_3
  <=> ~ r1_lattice3(sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f828,plain,
    ( r1_lattice3(sK1,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ spl11_3
    | ~ spl11_6
    | ~ spl11_18 ),
    inference(resolution,[],[f821,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
                & r2_hidden(sK5(X0,X1,X2),X1)
                & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f63,f64])).

fof(f64,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
        & r2_hidden(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
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
    inference(rectify,[],[f62])).

fof(f62,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t2_yellow_0.p',d8_lattice3)).

fof(f821,plain,
    ( r1_orders_2(sK1,sK3,sK5(sK1,sK2,sK3))
    | ~ spl11_3
    | ~ spl11_6
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f820,f605])).

fof(f605,plain,
    ( m1_subset_1(sK5(sK1,sK2,sK3),u1_struct_0(sK0))
    | ~ spl11_3
    | ~ spl11_18 ),
    inference(resolution,[],[f600,f367])).

fof(f367,plain,
    ( ! [X2] :
        ( r1_lattice3(sK1,X2,sK3)
        | m1_subset_1(sK5(sK1,X2,sK3),u1_struct_0(sK0)) )
    | ~ spl11_18 ),
    inference(backward_demodulation,[],[f363,f183])).

fof(f183,plain,(
    ! [X2] :
      ( r1_lattice3(sK1,X2,sK3)
      | m1_subset_1(sK5(sK1,X2,sK3),u1_struct_0(sK1)) ) ),
    inference(subsumption_resolution,[],[f177,f75])).

fof(f177,plain,(
    ! [X2] :
      ( m1_subset_1(sK5(sK1,X2,sK3),u1_struct_0(sK1))
      | r1_lattice3(sK1,X2,sK3)
      | ~ l1_orders_2(sK1) ) ),
    inference(resolution,[],[f170,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f820,plain,
    ( ~ m1_subset_1(sK5(sK1,sK2,sK3),u1_struct_0(sK0))
    | r1_orders_2(sK1,sK3,sK5(sK1,sK2,sK3))
    | ~ spl11_3
    | ~ spl11_6
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f819,f77])).

fof(f819,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK1,sK2,sK3),u1_struct_0(sK0))
    | r1_orders_2(sK1,sK3,sK5(sK1,sK2,sK3))
    | ~ spl11_3
    | ~ spl11_6
    | ~ spl11_18 ),
    inference(resolution,[],[f657,f769])).

fof(f657,plain,
    ( r1_orders_2(sK0,sK3,sK5(sK1,sK2,sK3))
    | ~ spl11_3
    | ~ spl11_6
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f628,f606])).

fof(f606,plain,
    ( r2_hidden(sK5(sK1,sK2,sK3),sK2)
    | ~ spl11_3 ),
    inference(resolution,[],[f600,f184])).

fof(f184,plain,(
    ! [X3] :
      ( r1_lattice3(sK1,X3,sK3)
      | r2_hidden(sK5(sK1,X3,sK3),X3) ) ),
    inference(subsumption_resolution,[],[f178,f75])).

fof(f178,plain,(
    ! [X3] :
      ( r2_hidden(sK5(sK1,X3,sK3),X3)
      | r1_lattice3(sK1,X3,sK3)
      | ~ l1_orders_2(sK1) ) ),
    inference(resolution,[],[f170,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f628,plain,
    ( ~ r2_hidden(sK5(sK1,sK2,sK3),sK2)
    | r1_orders_2(sK0,sK3,sK5(sK1,sK2,sK3))
    | ~ spl11_3
    | ~ spl11_6
    | ~ spl11_18 ),
    inference(resolution,[],[f605,f604])).

fof(f604,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK2)
        | r1_orders_2(sK0,sK3,X0) )
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f603,f74])).

fof(f603,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK3,X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f602,f77])).

fof(f602,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK3,X0)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl11_6 ),
    inference(resolution,[],[f144,f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X4)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f144,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl11_6
  <=> r1_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f234,plain,(
    spl11_17 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | ~ spl11_17 ),
    inference(subsumption_resolution,[],[f232,f75])).

fof(f232,plain,
    ( ~ l1_orders_2(sK1)
    | ~ spl11_17 ),
    inference(resolution,[],[f219,f85])).

fof(f85,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t2_yellow_0.p',dt_u1_orders_2)).

fof(f219,plain,
    ( ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))))
    | ~ spl11_17 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl11_17
  <=> ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f223,plain,
    ( ~ spl11_17
    | spl11_18 ),
    inference(avatar_split_clause,[],[f207,f221,f218])).

fof(f207,plain,(
    ! [X14,X15] :
      ( g1_orders_2(X14,X15) != g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0))
      | u1_struct_0(sK1) = X14
      | ~ m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ) ),
    inference(superposition,[],[f103,f76])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t2_yellow_0.p',free_g1_orders_2)).

fof(f146,plain,
    ( spl11_4
    | spl11_6 ),
    inference(avatar_split_clause,[],[f80,f143,f136])).

fof(f80,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | r2_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f145,plain,
    ( ~ spl11_1
    | spl11_6 ),
    inference(avatar_split_clause,[],[f81,f143,f123])).

fof(f81,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ r2_lattice3(sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f61])).

fof(f138,plain,
    ( spl11_4
    | ~ spl11_3 ),
    inference(avatar_split_clause,[],[f82,f129,f136])).

fof(f82,plain,
    ( ~ r1_lattice3(sK1,sK2,sK4)
    | r2_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f61])).

fof(f131,plain,
    ( ~ spl11_1
    | ~ spl11_3 ),
    inference(avatar_split_clause,[],[f83,f129,f123])).

fof(f83,plain,
    ( ~ r1_lattice3(sK1,sK2,sK4)
    | ~ r2_lattice3(sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f61])).
%------------------------------------------------------------------------------
