%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t10_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:36 EDT 2019

% Result     : Theorem 0.79s
% Output     : Refutation 0.79s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 486 expanded)
%              Number of leaves         :   15 ( 155 expanded)
%              Depth                    :   24
%              Number of atoms          :  610 (3663 expanded)
%              Number of equality atoms :   10 (  20 expanded)
%              Maximal formula depth    :   12 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f919,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f109,f113,f117,f118,f119,f123,f124,f125,f692,f909])).

fof(f909,plain,
    ( spl9_3
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(avatar_contradiction_clause,[],[f908])).

fof(f908,plain,
    ( $false
    | ~ spl9_3
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f905,f104])).

fof(f104,plain,
    ( ~ r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl9_3
  <=> ~ r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f905,plain,
    ( r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(duplicate_literal_removal,[],[f892])).

fof(f892,plain,
    ( r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
    | r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(resolution,[],[f788,f769])).

fof(f769,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK0,X0,sK3),sK1)
        | r2_lattice3(sK0,X0,sK3) )
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f768,f60])).

fof(f60,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( ( ~ r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
        & r2_lattice3(sK0,sK2,sK3)
        & r2_lattice3(sK0,sK1,sK3) )
      | ( ~ r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
        & r1_lattice3(sK0,sK2,sK3)
        & r1_lattice3(sK0,sK1,sK3) ) )
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f41,f40])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1,X2,X3] :
            ( ( ( ~ r2_lattice3(X0,k2_xboole_0(X1,X2),X3)
                & r2_lattice3(X0,X2,X3)
                & r2_lattice3(X0,X1,X3) )
              | ( ~ r1_lattice3(X0,k2_xboole_0(X1,X2),X3)
                & r1_lattice3(X0,X2,X3)
                & r1_lattice3(X0,X1,X3) ) )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & l1_orders_2(X0) )
   => ( ? [X3,X2,X1] :
          ( ( ( ~ r2_lattice3(sK0,k2_xboole_0(X1,X2),X3)
              & r2_lattice3(sK0,X2,X3)
              & r2_lattice3(sK0,X1,X3) )
            | ( ~ r1_lattice3(sK0,k2_xboole_0(X1,X2),X3)
              & r1_lattice3(sK0,X2,X3)
              & r1_lattice3(sK0,X1,X3) ) )
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1,X2,X3] :
          ( ( ( ~ r2_lattice3(X0,k2_xboole_0(X1,X2),X3)
              & r2_lattice3(X0,X2,X3)
              & r2_lattice3(X0,X1,X3) )
            | ( ~ r1_lattice3(X0,k2_xboole_0(X1,X2),X3)
              & r1_lattice3(X0,X2,X3)
              & r1_lattice3(X0,X1,X3) ) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ( ~ r2_lattice3(X0,k2_xboole_0(sK1,sK2),sK3)
            & r2_lattice3(X0,sK2,sK3)
            & r2_lattice3(X0,sK1,sK3) )
          | ( ~ r1_lattice3(X0,k2_xboole_0(sK1,sK2),sK3)
            & r1_lattice3(X0,sK2,sK3)
            & r1_lattice3(X0,sK1,sK3) ) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1,X2,X3] :
          ( ( ( ~ r2_lattice3(X0,k2_xboole_0(X1,X2),X3)
              & r2_lattice3(X0,X2,X3)
              & r2_lattice3(X0,X1,X3) )
            | ( ~ r1_lattice3(X0,k2_xboole_0(X1,X2),X3)
              & r1_lattice3(X0,X2,X3)
              & r1_lattice3(X0,X1,X3) ) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1,X2,X3] :
          ( ( ( ~ r2_lattice3(X0,k2_xboole_0(X1,X2),X3)
              & r2_lattice3(X0,X2,X3)
              & r2_lattice3(X0,X1,X3) )
            | ( ~ r1_lattice3(X0,k2_xboole_0(X1,X2),X3)
              & r1_lattice3(X0,X2,X3)
              & r1_lattice3(X0,X1,X3) ) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1,X2,X3] :
            ( m1_subset_1(X3,u1_struct_0(X0))
           => ( ( ( r2_lattice3(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3) )
               => r2_lattice3(X0,k2_xboole_0(X1,X2),X3) )
              & ( ( r1_lattice3(X0,X2,X3)
                  & r1_lattice3(X0,X1,X3) )
               => r1_lattice3(X0,k2_xboole_0(X1,X2),X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/yellow_0__t10_yellow_0.p',t10_yellow_0)).

fof(f768,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK0,X0,sK3),sK1)
        | r2_lattice3(sK0,X0,sK3)
        | ~ l1_orders_2(sK0) )
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f767,f61])).

fof(f61,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f767,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK0,X0,sK3),sK1)
        | r2_lattice3(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_10 ),
    inference(duplicate_literal_removal,[],[f766])).

fof(f766,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK0,X0,sK3),sK1)
        | r2_lattice3(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_10 ),
    inference(resolution,[],[f728,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f48,f49])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
        & r2_hidden(sK5(X0,X1,X2),X1)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t10_yellow_0.p',d9_lattice3)).

fof(f728,plain,
    ( ! [X4,X5] :
        ( r1_orders_2(sK0,sK5(sK0,X4,X5),sK3)
        | ~ r2_hidden(sK5(sK0,X4,X5),sK1)
        | r2_lattice3(sK0,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f724,f60])).

fof(f724,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(sK5(sK0,X4,X5),sK1)
        | r1_orders_2(sK0,sK5(sK0,X4,X5),sK3)
        | r2_lattice3(sK0,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_10 ),
    inference(resolution,[],[f707,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f707,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | r1_orders_2(sK0,X0,sK3) )
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f706,f60])).

fof(f706,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK3)
        | ~ l1_orders_2(sK0) )
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f705,f61])).

fof(f705,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_10 ),
    inference(resolution,[],[f122,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X4,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f122,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl9_10
  <=> r2_lattice3(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f788,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK0,k2_xboole_0(X0,sK2),sK3),X0)
        | r2_lattice3(sK0,k2_xboole_0(X0,sK2),sK3) )
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f787,f60])).

fof(f787,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,k2_xboole_0(X0,sK2),sK3)
        | ~ l1_orders_2(sK0)
        | r2_hidden(sK5(sK0,k2_xboole_0(X0,sK2),sK3),X0) )
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f785,f61])).

fof(f785,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,k2_xboole_0(X0,sK2),sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r2_hidden(sK5(sK0,k2_xboole_0(X0,sK2),sK3),X0) )
    | ~ spl9_8 ),
    inference(duplicate_literal_removal,[],[f784])).

fof(f784,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,k2_xboole_0(X0,sK2),sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r2_hidden(sK5(sK0,k2_xboole_0(X0,sK2),sK3),X0)
        | r2_lattice3(sK0,k2_xboole_0(X0,sK2),sK3) )
    | ~ spl9_8 ),
    inference(resolution,[],[f755,f172])).

fof(f172,plain,(
    ! [X12,X10,X11,X9] :
      ( r2_hidden(sK5(X9,k2_xboole_0(X10,X11),X12),X11)
      | ~ m1_subset_1(X12,u1_struct_0(X9))
      | ~ l1_orders_2(X9)
      | r2_hidden(sK5(X9,k2_xboole_0(X10,X11),X12),X10)
      | r2_lattice3(X9,k2_xboole_0(X10,X11),X12) ) ),
    inference(resolution,[],[f79,f98])).

fof(f98,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_xboole_0(X0,X1))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
              & ~ r2_hidden(sK7(X0,X1,X2),X0) )
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( r2_hidden(sK7(X0,X1,X2),X1)
            | r2_hidden(sK7(X0,X1,X2),X0)
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f55,f56])).

fof(f56,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
            & ~ r2_hidden(sK7(X0,X1,X2),X0) )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( r2_hidden(sK7(X0,X1,X2),X1)
          | r2_hidden(sK7(X0,X1,X2),X0)
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t10_yellow_0.p',d3_xboole_0)).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f755,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK0,X0,sK3),sK2)
        | r2_lattice3(sK0,X0,sK3) )
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f754,f60])).

fof(f754,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK0,X0,sK3),sK2)
        | r2_lattice3(sK0,X0,sK3)
        | ~ l1_orders_2(sK0) )
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f753,f61])).

fof(f753,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK0,X0,sK3),sK2)
        | r2_lattice3(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_8 ),
    inference(duplicate_literal_removal,[],[f752])).

fof(f752,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK0,X0,sK3),sK2)
        | r2_lattice3(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_8 ),
    inference(resolution,[],[f720,f80])).

fof(f720,plain,
    ( ! [X4,X5] :
        ( r1_orders_2(sK0,sK5(sK0,X4,X5),sK3)
        | ~ r2_hidden(sK5(sK0,X4,X5),sK2)
        | r2_lattice3(sK0,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f716,f60])).

fof(f716,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(sK5(sK0,X4,X5),sK2)
        | r1_orders_2(sK0,sK5(sK0,X4,X5),sK3)
        | r2_lattice3(sK0,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_8 ),
    inference(resolution,[],[f704,f78])).

fof(f704,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK2)
        | r1_orders_2(sK0,X0,sK3) )
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f703,f60])).

fof(f703,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK3)
        | ~ l1_orders_2(sK0) )
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f702,f61])).

fof(f702,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_8 ),
    inference(resolution,[],[f116,f77])).

fof(f116,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl9_8
  <=> r2_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f692,plain,
    ( spl9_1
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(avatar_contradiction_clause,[],[f691])).

fof(f691,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f690,f101])).

fof(f101,plain,
    ( ~ r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl9_1
  <=> ~ r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f690,plain,
    ( r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(duplicate_literal_removal,[],[f685])).

fof(f685,plain,
    ( r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
    | r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
    | ~ spl9_4
    | ~ spl9_6 ),
    inference(resolution,[],[f638,f511])).

fof(f511,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK0,k2_xboole_0(X0,sK2),sK3),X0)
        | r1_lattice3(sK0,k2_xboole_0(X0,sK2),sK3) )
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f510,f60])).

fof(f510,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK0)
        | r2_hidden(sK4(sK0,k2_xboole_0(X0,sK2),sK3),X0)
        | r1_lattice3(sK0,k2_xboole_0(X0,sK2),sK3) )
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f509,f61])).

fof(f509,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r2_hidden(sK4(sK0,k2_xboole_0(X0,sK2),sK3),X0)
        | r1_lattice3(sK0,k2_xboole_0(X0,sK2),sK3) )
    | ~ spl9_4 ),
    inference(duplicate_literal_removal,[],[f495])).

fof(f495,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r2_hidden(sK4(sK0,k2_xboole_0(X0,sK2),sK3),X0)
        | r1_lattice3(sK0,k2_xboole_0(X0,sK2),sK3)
        | r1_lattice3(sK0,k2_xboole_0(X0,sK2),sK3) )
    | ~ spl9_4 ),
    inference(resolution,[],[f168,f451])).

fof(f451,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK0,X0,sK3),sK2)
        | r1_lattice3(sK0,X0,sK3) )
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f450,f60])).

fof(f450,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK0,X0,sK3),sK2)
        | r1_lattice3(sK0,X0,sK3)
        | ~ l1_orders_2(sK0) )
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f449,f61])).

fof(f449,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK0,X0,sK3),sK2)
        | r1_lattice3(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_4 ),
    inference(duplicate_literal_removal,[],[f448])).

fof(f448,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK0,X0,sK3),sK2)
        | r1_lattice3(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_4 ),
    inference(resolution,[],[f233,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f44,f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK4(X0,X1,X2))
        & r2_hidden(sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
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
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_0__t10_yellow_0.p',d8_lattice3)).

fof(f233,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,sK3,sK4(sK0,X0,X1))
        | ~ r2_hidden(sK4(sK0,X0,X1),sK2)
        | r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f223,f60])).

fof(f223,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK4(sK0,X0,X1),sK2)
        | r1_orders_2(sK0,sK3,sK4(sK0,X0,X1))
        | r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_4 ),
    inference(resolution,[],[f205,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f205,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK2)
        | r1_orders_2(sK0,sK3,X0) )
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f204,f60])).

fof(f204,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK3,X0)
        | ~ l1_orders_2(sK0) )
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f202,f61])).

fof(f202,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK3,X0)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_4 ),
    inference(resolution,[],[f73,f108])).

fof(f108,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl9_4
  <=> r1_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_orders_2(X0,X2,X4)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f168,plain,(
    ! [X12,X10,X11,X9] :
      ( r2_hidden(sK4(X9,k2_xboole_0(X10,X11),X12),X11)
      | ~ m1_subset_1(X12,u1_struct_0(X9))
      | ~ l1_orders_2(X9)
      | r2_hidden(sK4(X9,k2_xboole_0(X10,X11),X12),X10)
      | r1_lattice3(X9,k2_xboole_0(X10,X11),X12) ) ),
    inference(resolution,[],[f75,f98])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f638,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK0,X0,sK3),sK1)
        | r1_lattice3(sK0,X0,sK3) )
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f637,f60])).

fof(f637,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK0,X0,sK3),sK1)
        | r1_lattice3(sK0,X0,sK3)
        | ~ l1_orders_2(sK0) )
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f636,f61])).

fof(f636,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK0,X0,sK3),sK1)
        | r1_lattice3(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_6 ),
    inference(duplicate_literal_removal,[],[f635])).

fof(f635,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK0,X0,sK3),sK1)
        | r1_lattice3(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,sK3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_6 ),
    inference(resolution,[],[f250,f76])).

fof(f250,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,sK3,sK4(sK0,X0,X1))
        | ~ r2_hidden(sK4(sK0,X0,X1),sK1)
        | r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f243,f60])).

fof(f243,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK4(sK0,X0,X1),sK1)
        | r1_orders_2(sK0,sK3,sK4(sK0,X0,X1))
        | r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_6 ),
    inference(resolution,[],[f207,f74])).

fof(f207,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,sK1)
        | r1_orders_2(sK0,sK3,X1) )
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f206,f60])).

fof(f206,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK3,X1)
        | ~ l1_orders_2(sK0) )
    | ~ spl9_6 ),
    inference(subsumption_resolution,[],[f203,f61])).

fof(f203,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_orders_2(sK0,sK3,X1)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl9_6 ),
    inference(resolution,[],[f73,f112])).

fof(f112,plain,
    ( r1_lattice3(sK0,sK1,sK3)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl9_6
  <=> r1_lattice3(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f125,plain,
    ( spl9_6
    | spl9_10 ),
    inference(avatar_split_clause,[],[f62,f121,f111])).

fof(f62,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f124,plain,
    ( spl9_4
    | spl9_10 ),
    inference(avatar_split_clause,[],[f63,f121,f107])).

fof(f63,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | r1_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f123,plain,
    ( ~ spl9_1
    | spl9_10 ),
    inference(avatar_split_clause,[],[f64,f121,f100])).

fof(f64,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | ~ r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f119,plain,
    ( spl9_6
    | spl9_8 ),
    inference(avatar_split_clause,[],[f65,f115,f111])).

fof(f65,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f118,plain,
    ( spl9_4
    | spl9_8 ),
    inference(avatar_split_clause,[],[f66,f115,f107])).

fof(f66,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | r1_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f117,plain,
    ( ~ spl9_1
    | spl9_8 ),
    inference(avatar_split_clause,[],[f67,f115,f100])).

fof(f67,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f113,plain,
    ( spl9_6
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f68,f103,f111])).

fof(f68,plain,
    ( ~ r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
    | r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f109,plain,
    ( spl9_4
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f69,f103,f107])).

fof(f69,plain,
    ( ~ r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
    | r1_lattice3(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f105,plain,
    ( ~ spl9_1
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f70,f103,f100])).

fof(f70,plain,
    ( ~ r2_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3)
    | ~ r1_lattice3(sK0,k2_xboole_0(sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
