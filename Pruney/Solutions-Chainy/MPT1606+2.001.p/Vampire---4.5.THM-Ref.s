%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 631 expanded)
%              Number of leaves         :   23 ( 159 expanded)
%              Depth                    :   41
%              Number of atoms          :  609 (2488 expanded)
%              Number of equality atoms :   39 ( 228 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f379,plain,(
    $false ),
    inference(subsumption_resolution,[],[f378,f79])).

fof(f79,plain,(
    r2_hidden(k3_tarski(sK3),sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,
    ( k3_tarski(sK3) != k4_yellow_0(k2_yellow_1(sK3))
    & r2_hidden(k3_tarski(sK3),sK3)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f54])).

fof(f54,plain,
    ( ? [X0] :
        ( k3_tarski(X0) != k4_yellow_0(k2_yellow_1(X0))
        & r2_hidden(k3_tarski(X0),X0)
        & ~ v1_xboole_0(X0) )
   => ( k3_tarski(sK3) != k4_yellow_0(k2_yellow_1(sK3))
      & r2_hidden(k3_tarski(sK3),sK3)
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0] :
      ( k3_tarski(X0) != k4_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k3_tarski(X0),X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( k3_tarski(X0) != k4_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k3_tarski(X0),X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( r2_hidden(k3_tarski(X0),X0)
         => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

fof(f378,plain,(
    ~ r2_hidden(k3_tarski(sK3),sK3) ),
    inference(resolution,[],[f377,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f377,plain,(
    ~ m1_subset_1(k3_tarski(sK3),sK3) ),
    inference(subsumption_resolution,[],[f374,f80])).

fof(f80,plain,(
    k3_tarski(sK3) != k4_yellow_0(k2_yellow_1(sK3)) ),
    inference(cnf_transformation,[],[f55])).

fof(f374,plain,
    ( ~ m1_subset_1(k3_tarski(sK3),sK3)
    | k3_tarski(sK3) = k4_yellow_0(k2_yellow_1(sK3)) ),
    inference(resolution,[],[f360,f321])).

fof(f321,plain,(
    sP0(k3_tarski(sK3),k2_yellow_1(sK3),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f320,f79])).

fof(f320,plain,
    ( sP0(k3_tarski(sK3),k2_yellow_1(sK3),k1_xboole_0)
    | ~ r2_hidden(k3_tarski(sK3),sK3) ),
    inference(resolution,[],[f319,f116])).

fof(f319,plain,
    ( ~ m1_subset_1(k3_tarski(sK3),sK3)
    | sP0(k3_tarski(sK3),k2_yellow_1(sK3),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f318,f152])).

fof(f152,plain,(
    ! [X0,X1] :
      ( r1_lattice3(k2_yellow_1(X0),k1_xboole_0,X1)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(resolution,[],[f151,f81])).

fof(f81,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,sK6(k2_yellow_1(X1),X2,X0))
      | r1_lattice3(k2_yellow_1(X1),X2,X0)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f150,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(k2_yellow_1(X0),X1,X2),X1)
      | ~ m1_subset_1(X2,X0)
      | r1_lattice3(k2_yellow_1(X0),X1,X2) ) ),
    inference(forward_demodulation,[],[f149,f85])).

fof(f85,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(k2_yellow_1(X0),X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | r1_lattice3(k2_yellow_1(X0),X1,X2) ) ),
    inference(resolution,[],[f106,f84])).

fof(f84,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f69,f70])).

fof(f70,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
        & r2_hidden(sK6(X0,X1,X2),X1)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f69,plain,(
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
    inference(rectify,[],[f68])).

fof(f68,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f318,plain,
    ( sP0(k3_tarski(sK3),k2_yellow_1(sK3),k1_xboole_0)
    | ~ r1_lattice3(k2_yellow_1(sK3),k1_xboole_0,k3_tarski(sK3))
    | ~ m1_subset_1(k3_tarski(sK3),sK3) ),
    inference(subsumption_resolution,[],[f317,f78])).

fof(f78,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f317,plain,
    ( sP0(k3_tarski(sK3),k2_yellow_1(sK3),k1_xboole_0)
    | ~ r1_lattice3(k2_yellow_1(sK3),k1_xboole_0,k3_tarski(sK3))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(k3_tarski(sK3),sK3) ),
    inference(duplicate_literal_removal,[],[f314])).

fof(f314,plain,
    ( sP0(k3_tarski(sK3),k2_yellow_1(sK3),k1_xboole_0)
    | ~ r1_lattice3(k2_yellow_1(sK3),k1_xboole_0,k3_tarski(sK3))
    | sP0(k3_tarski(sK3),k2_yellow_1(sK3),k1_xboole_0)
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(k3_tarski(sK3),sK3) ),
    inference(resolution,[],[f285,f155])).

fof(f155,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,k2_yellow_1(X1),k1_xboole_0),X1)
      | sP0(X0,k2_yellow_1(X1),k1_xboole_0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f154,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f154,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,k2_yellow_1(X1),k1_xboole_0),X1)
      | ~ m1_subset_1(X0,X1)
      | sP0(X0,k2_yellow_1(X1),k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f153,f85])).

fof(f153,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | m1_subset_1(sK4(X0,k2_yellow_1(X1),k1_xboole_0),u1_struct_0(k2_yellow_1(X1)))
      | sP0(X0,k2_yellow_1(X1),k1_xboole_0) ) ),
    inference(resolution,[],[f152,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X1,X2,X0)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r1_orders_2(X1,sK4(X0,X1,X2),X0)
          & r1_lattice3(X1,X2,sK4(X0,X1,X2))
          & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) )
        | ~ r1_lattice3(X1,X2,X0) )
      & ( ( ! [X4] :
              ( r1_orders_2(X1,X4,X0)
              | ~ r1_lattice3(X1,X2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r1_lattice3(X1,X2,X0) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f61,f62])).

fof(f62,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X1,X3,X0)
          & r1_lattice3(X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,sK4(X0,X1,X2),X0)
        & r1_lattice3(X1,X2,sK4(X0,X1,X2))
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_orders_2(X1,X3,X0)
            & r1_lattice3(X1,X2,X3)
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ r1_lattice3(X1,X2,X0) )
      & ( ( ! [X4] :
              ( r1_orders_2(X1,X4,X0)
              | ~ r1_lattice3(X1,X2,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r1_lattice3(X1,X2,X0) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ? [X3] :
            ( ~ r1_orders_2(X0,X3,X2)
            & r1_lattice3(X0,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ r1_lattice3(X0,X1,X2) )
      & ( ( ! [X3] :
              ( r1_orders_2(X0,X3,X2)
              | ~ r1_lattice3(X0,X1,X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,X2) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ? [X3] :
            ( ~ r1_orders_2(X0,X3,X2)
            & r1_lattice3(X0,X1,X3)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ r1_lattice3(X0,X1,X2) )
      & ( ( ! [X3] :
              ( r1_orders_2(X0,X3,X2)
              | ~ r1_lattice3(X0,X1,X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,X2) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
    <=> ( ! [X3] :
            ( r1_orders_2(X0,X3,X2)
            | ~ r1_lattice3(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & r1_lattice3(X0,X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f285,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK4(k3_tarski(sK3),k2_yellow_1(sK3),X1),sK3)
      | sP0(k3_tarski(sK3),k2_yellow_1(sK3),X1)
      | ~ r1_lattice3(k2_yellow_1(sK3),X1,k3_tarski(sK3)) ) ),
    inference(resolution,[],[f283,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X1,sK4(X0,X1,X2),X0)
      | sP0(X0,X1,X2)
      | ~ r1_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f283,plain,(
    ! [X0] :
      ( r1_orders_2(k2_yellow_1(sK3),X0,k3_tarski(sK3))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f282,f116])).

fof(f282,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK3)
      | ~ r2_hidden(X0,sK3)
      | r1_orders_2(k2_yellow_1(sK3),X0,k3_tarski(sK3)) ) ),
    inference(subsumption_resolution,[],[f281,f78])).

fof(f281,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK3)
      | v1_xboole_0(sK3)
      | ~ r2_hidden(X0,sK3)
      | r1_orders_2(k2_yellow_1(sK3),X0,k3_tarski(sK3)) ) ),
    inference(resolution,[],[f280,f79])).

fof(f280,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k3_tarski(X2),X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | ~ r2_hidden(X1,X2)
      | r1_orders_2(k2_yellow_1(X0),X1,k3_tarski(X2)) ) ),
    inference(resolution,[],[f278,f116])).

fof(f278,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(k3_tarski(X4),X3)
      | r1_orders_2(k2_yellow_1(X3),X2,k3_tarski(X4))
      | ~ m1_subset_1(X2,X3)
      | v1_xboole_0(X3)
      | ~ r2_hidden(X2,X4) ) ),
    inference(resolution,[],[f276,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f276,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | ~ m1_subset_1(X2,X1)
      | r1_orders_2(k2_yellow_1(X1),X2,X0)
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f275,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ~ v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).

fof(f275,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | ~ m1_subset_1(X2,X1)
      | r1_orders_2(k2_yellow_1(X1),X2,X0)
      | v2_struct_0(k2_yellow_1(X1))
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f274])).

fof(f274,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | ~ m1_subset_1(X2,X1)
      | r1_orders_2(k2_yellow_1(X1),X2,X0)
      | v2_struct_0(k2_yellow_1(X1))
      | ~ m1_subset_1(X0,X1)
      | ~ m1_subset_1(X2,X1)
      | ~ r1_tarski(X2,X0)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f273,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f125,f85])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f89,f85])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
                  | ~ r1_tarski(X1,X2) )
                & ( r1_tarski(X1,X2)
                  | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f273,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(forward_demodulation,[],[f272,f85])).

fof(f272,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(forward_demodulation,[],[f271,f85])).

fof(f271,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f270,f82])).

fof(f82,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f270,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(resolution,[],[f120,f84])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f360,plain,(
    ! [X0] :
      ( ~ sP0(X0,k2_yellow_1(sK3),k1_xboole_0)
      | ~ m1_subset_1(X0,sK3)
      | k4_yellow_0(k2_yellow_1(sK3)) = X0 ) ),
    inference(forward_demodulation,[],[f355,f133])).

fof(f133,plain,(
    ! [X0] : k4_yellow_0(k2_yellow_1(X0)) = k2_yellow_0(k2_yellow_1(X0),k1_xboole_0) ),
    inference(resolution,[],[f91,f84])).

fof(f91,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k4_yellow_0(X0) = k2_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k4_yellow_0(X0) = k2_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k4_yellow_0(X0) = k2_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_yellow_0)).

fof(f355,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK3)
      | ~ sP0(X0,k2_yellow_1(sK3),k1_xboole_0)
      | k2_yellow_0(k2_yellow_1(sK3),k1_xboole_0) = X0 ) ),
    inference(resolution,[],[f352,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | k2_yellow_0(X1,X0) = X2 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( ( k2_yellow_0(X1,X0) = X2
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k2_yellow_0(X1,X0) != X2 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X1,X0,X2] :
      ( ( ( k2_yellow_0(X0,X1) = X2
          | ~ sP0(X2,X0,X1) )
        & ( sP0(X2,X0,X1)
          | k2_yellow_0(X0,X1) != X2 ) )
      | ~ sP1(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X1,X0,X2] :
      ( ( k2_yellow_0(X0,X1) = X2
      <=> sP0(X2,X0,X1) )
      | ~ sP1(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f352,plain,(
    ! [X0] :
      ( sP1(k1_xboole_0,k2_yellow_1(sK3),X0)
      | ~ m1_subset_1(X0,sK3) ) ),
    inference(forward_demodulation,[],[f351,f85])).

fof(f351,plain,(
    ! [X0] :
      ( sP1(k1_xboole_0,k2_yellow_1(sK3),X0)
      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK3))) ) ),
    inference(subsumption_resolution,[],[f345,f84])).

fof(f345,plain,(
    ! [X0] :
      ( sP1(k1_xboole_0,k2_yellow_1(sK3),X0)
      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK3)))
      | ~ l1_orders_2(k2_yellow_1(sK3)) ) ),
    inference(resolution,[],[f341,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_yellow_0(X0,X1)
      | sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( sP1(X1,X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f33,f50,f49])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f32])).

% (19280)Refutation not found, incomplete strategy% (19280)------------------------------
% (19280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19280)Termination reason: Refutation not found, incomplete strategy

% (19280)Memory used [KB]: 10618
% (19280)Time elapsed: 0.126 s
% (19280)------------------------------
% (19280)------------------------------
fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_yellow_0(X0,X1)
           => ( k2_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r1_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X3,X2) ) )
                & r1_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_yellow_0)).

fof(f341,plain,(
    r2_yellow_0(k2_yellow_1(sK3),k1_xboole_0) ),
    inference(resolution,[],[f340,f323])).

fof(f323,plain,(
    r1_lattice3(k2_yellow_1(sK3),k1_xboole_0,k3_tarski(sK3)) ),
    inference(resolution,[],[f321,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r1_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f340,plain,(
    ! [X0] :
      ( ~ r1_lattice3(k2_yellow_1(sK3),X0,k3_tarski(sK3))
      | r2_yellow_0(k2_yellow_1(sK3),X0) ) ),
    inference(subsumption_resolution,[],[f339,f79])).

fof(f339,plain,(
    ! [X0] :
      ( ~ r1_lattice3(k2_yellow_1(sK3),X0,k3_tarski(sK3))
      | r2_yellow_0(k2_yellow_1(sK3),X0)
      | ~ r2_hidden(k3_tarski(sK3),sK3) ) ),
    inference(resolution,[],[f338,f116])).

fof(f338,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k3_tarski(sK3),sK3)
      | ~ r1_lattice3(k2_yellow_1(sK3),X1,k3_tarski(sK3))
      | r2_yellow_0(k2_yellow_1(sK3),X1) ) ),
    inference(subsumption_resolution,[],[f336,f176])).

fof(f176,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,k2_yellow_1(X1),X2),X1)
      | ~ m1_subset_1(X0,X1)
      | ~ r1_lattice3(k2_yellow_1(X1),X2,X0)
      | r2_yellow_0(k2_yellow_1(X1),X2) ) ),
    inference(forward_demodulation,[],[f175,f85])).

fof(f175,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | ~ r1_lattice3(k2_yellow_1(X1),X2,X0)
      | r2_yellow_0(k2_yellow_1(X1),X2)
      | m1_subset_1(sK7(X0,k2_yellow_1(X1),X2),u1_struct_0(k2_yellow_1(X1))) ) ),
    inference(resolution,[],[f174,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_orders_2(X1,sK7(X0,X1,X2),X0)
        & r1_lattice3(X1,X2,sK7(X0,X1,X2))
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f73,f74])).

fof(f74,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X1,X3,X0)
          & r1_lattice3(X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,sK7(X0,X1,X2),X0)
        & r1_lattice3(X1,X2,sK7(X0,X1,X2))
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r1_orders_2(X1,X3,X0)
          & r1_lattice3(X1,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X1)) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f72])).

fof(f72,plain,(
    ! [X1,X0,X2] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X1)
          & r1_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ sP2(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X1,X0,X2] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X1)
          & r1_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ sP2(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f174,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,k2_yellow_1(X1),X2)
      | ~ m1_subset_1(X0,X1)
      | ~ r1_lattice3(k2_yellow_1(X1),X2,X0)
      | r2_yellow_0(k2_yellow_1(X1),X2) ) ),
    inference(forward_demodulation,[],[f173,f85])).

fof(f173,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,k2_yellow_1(X1),X2)
      | ~ r1_lattice3(k2_yellow_1(X1),X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
      | r2_yellow_0(k2_yellow_1(X1),X2) ) ),
    inference(subsumption_resolution,[],[f172,f84])).

fof(f172,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,k2_yellow_1(X1),X2)
      | ~ r1_lattice3(k2_yellow_1(X1),X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
      | ~ l1_orders_2(k2_yellow_1(X1))
      | r2_yellow_0(k2_yellow_1(X1),X2) ) ),
    inference(resolution,[],[f114,f83])).

fof(f83,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | sP2(X1,X0,X2)
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_yellow_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | sP2(X1,X0,X2)
                | ~ r1_lattice3(X0,X2,X1) )
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
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | sP2(X1,X0,X2)
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
    inference(definition_folding,[],[f39,f52])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(rectify,[],[f13])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_yellow_0)).

fof(f336,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK7(k3_tarski(sK3),k2_yellow_1(sK3),X1),sK3)
      | ~ m1_subset_1(k3_tarski(sK3),sK3)
      | ~ r1_lattice3(k2_yellow_1(sK3),X1,k3_tarski(sK3))
      | r2_yellow_0(k2_yellow_1(sK3),X1) ) ),
    inference(resolution,[],[f332,f174])).

fof(f332,plain,(
    ! [X0] :
      ( ~ sP2(k3_tarski(sK3),k2_yellow_1(sK3),X0)
      | ~ m1_subset_1(sK7(k3_tarski(sK3),k2_yellow_1(sK3),X0),sK3) ) ),
    inference(resolution,[],[f325,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X1,sK7(X0,X1,X2),X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f325,plain,(
    ! [X0] :
      ( r1_orders_2(k2_yellow_1(sK3),X0,k3_tarski(sK3))
      | ~ m1_subset_1(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f324,f152])).

fof(f324,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK3)
      | ~ r1_lattice3(k2_yellow_1(sK3),k1_xboole_0,X0)
      | r1_orders_2(k2_yellow_1(sK3),X0,k3_tarski(sK3)) ) ),
    inference(forward_demodulation,[],[f322,f85])).

fof(f322,plain,(
    ! [X0] :
      ( ~ r1_lattice3(k2_yellow_1(sK3),k1_xboole_0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK3)))
      | r1_orders_2(k2_yellow_1(sK3),X0,k3_tarski(sK3)) ) ),
    inference(resolution,[],[f321,f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r1_lattice3(X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f63])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:17:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (19293)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (19282)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.50  % (19279)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (19285)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (19302)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (19298)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.51  % (19279)Refutation not found, incomplete strategy% (19279)------------------------------
% 0.22/0.51  % (19279)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (19291)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.51  % (19283)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (19287)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.51  % (19279)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (19279)Memory used [KB]: 10618
% 0.22/0.51  % (19279)Time elapsed: 0.093 s
% 0.22/0.51  % (19279)------------------------------
% 0.22/0.51  % (19279)------------------------------
% 0.22/0.51  % (19297)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.52  % (19280)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (19285)Refutation not found, incomplete strategy% (19285)------------------------------
% 0.22/0.52  % (19285)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (19285)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (19285)Memory used [KB]: 10618
% 0.22/0.52  % (19285)Time elapsed: 0.104 s
% 0.22/0.52  % (19285)------------------------------
% 0.22/0.52  % (19285)------------------------------
% 0.22/0.52  % (19301)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.52  % (19290)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (19294)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.52  % (19300)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (19290)Refutation not found, incomplete strategy% (19290)------------------------------
% 0.22/0.52  % (19290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (19290)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (19290)Memory used [KB]: 10618
% 0.22/0.52  % (19290)Time elapsed: 0.107 s
% 0.22/0.52  % (19290)------------------------------
% 0.22/0.52  % (19290)------------------------------
% 0.22/0.52  % (19286)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  % (19286)Refutation not found, incomplete strategy% (19286)------------------------------
% 0.22/0.52  % (19286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (19286)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (19286)Memory used [KB]: 1791
% 0.22/0.52  % (19286)Time elapsed: 0.085 s
% 0.22/0.52  % (19286)------------------------------
% 0.22/0.52  % (19286)------------------------------
% 0.22/0.52  % (19292)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (19295)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.53  % (19303)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.53  % (19282)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f379,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(subsumption_resolution,[],[f378,f79])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    r2_hidden(k3_tarski(sK3),sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    k3_tarski(sK3) != k4_yellow_0(k2_yellow_1(sK3)) & r2_hidden(k3_tarski(sK3),sK3) & ~v1_xboole_0(sK3)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ? [X0] : (k3_tarski(X0) != k4_yellow_0(k2_yellow_1(X0)) & r2_hidden(k3_tarski(X0),X0) & ~v1_xboole_0(X0)) => (k3_tarski(sK3) != k4_yellow_0(k2_yellow_1(sK3)) & r2_hidden(k3_tarski(sK3),sK3) & ~v1_xboole_0(sK3))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ? [X0] : (k3_tarski(X0) != k4_yellow_0(k2_yellow_1(X0)) & r2_hidden(k3_tarski(X0),X0) & ~v1_xboole_0(X0))),
% 0.22/0.53    inference(flattening,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ? [X0] : ((k3_tarski(X0) != k4_yellow_0(k2_yellow_1(X0)) & r2_hidden(k3_tarski(X0),X0)) & ~v1_xboole_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,negated_conjecture,(
% 0.22/0.53    ~! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 0.22/0.53    inference(negated_conjecture,[],[f19])).
% 0.22/0.53  fof(f19,conjecture,(
% 0.22/0.53    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).
% 0.22/0.53  fof(f378,plain,(
% 0.22/0.53    ~r2_hidden(k3_tarski(sK3),sK3)),
% 0.22/0.53    inference(resolution,[],[f377,f116])).
% 0.22/0.53  fof(f116,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.53  fof(f377,plain,(
% 0.22/0.53    ~m1_subset_1(k3_tarski(sK3),sK3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f374,f80])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    k3_tarski(sK3) != k4_yellow_0(k2_yellow_1(sK3))),
% 0.22/0.53    inference(cnf_transformation,[],[f55])).
% 0.22/0.53  fof(f374,plain,(
% 0.22/0.53    ~m1_subset_1(k3_tarski(sK3),sK3) | k3_tarski(sK3) = k4_yellow_0(k2_yellow_1(sK3))),
% 0.22/0.53    inference(resolution,[],[f360,f321])).
% 0.22/0.53  fof(f321,plain,(
% 0.22/0.53    sP0(k3_tarski(sK3),k2_yellow_1(sK3),k1_xboole_0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f320,f79])).
% 0.22/0.53  fof(f320,plain,(
% 0.22/0.53    sP0(k3_tarski(sK3),k2_yellow_1(sK3),k1_xboole_0) | ~r2_hidden(k3_tarski(sK3),sK3)),
% 0.22/0.53    inference(resolution,[],[f319,f116])).
% 0.22/0.53  fof(f319,plain,(
% 0.22/0.53    ~m1_subset_1(k3_tarski(sK3),sK3) | sP0(k3_tarski(sK3),k2_yellow_1(sK3),k1_xboole_0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f318,f152])).
% 0.22/0.53  fof(f152,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_lattice3(k2_yellow_1(X0),k1_xboole_0,X1) | ~m1_subset_1(X1,X0)) )),
% 0.22/0.53    inference(resolution,[],[f151,f81])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.53  fof(f151,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X2,sK6(k2_yellow_1(X1),X2,X0)) | r1_lattice3(k2_yellow_1(X1),X2,X0) | ~m1_subset_1(X0,X1)) )),
% 0.22/0.53    inference(resolution,[],[f150,f119])).
% 0.22/0.53  fof(f119,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.53  fof(f150,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK6(k2_yellow_1(X0),X1,X2),X1) | ~m1_subset_1(X2,X0) | r1_lattice3(k2_yellow_1(X0),X1,X2)) )),
% 0.22/0.53    inference(forward_demodulation,[],[f149,f85])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,axiom,(
% 0.22/0.53    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.22/0.53  fof(f149,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK6(k2_yellow_1(X0),X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | r1_lattice3(k2_yellow_1(X0),X1,X2)) )),
% 0.22/0.53    inference(resolution,[],[f106,f84])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 0.22/0.53    inference(pure_predicate_removal,[],[f14])).
% 0.22/0.53  fof(f14,axiom,(
% 0.22/0.53    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | r2_hidden(sK6(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattice3(X0,X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f71])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X1) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f69,f70])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X1) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(rectify,[],[f68])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(flattening,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).
% 0.22/0.53  fof(f318,plain,(
% 0.22/0.53    sP0(k3_tarski(sK3),k2_yellow_1(sK3),k1_xboole_0) | ~r1_lattice3(k2_yellow_1(sK3),k1_xboole_0,k3_tarski(sK3)) | ~m1_subset_1(k3_tarski(sK3),sK3)),
% 0.22/0.53    inference(subsumption_resolution,[],[f317,f78])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    ~v1_xboole_0(sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f55])).
% 0.22/0.53  fof(f317,plain,(
% 0.22/0.53    sP0(k3_tarski(sK3),k2_yellow_1(sK3),k1_xboole_0) | ~r1_lattice3(k2_yellow_1(sK3),k1_xboole_0,k3_tarski(sK3)) | v1_xboole_0(sK3) | ~m1_subset_1(k3_tarski(sK3),sK3)),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f314])).
% 0.22/0.53  fof(f314,plain,(
% 0.22/0.53    sP0(k3_tarski(sK3),k2_yellow_1(sK3),k1_xboole_0) | ~r1_lattice3(k2_yellow_1(sK3),k1_xboole_0,k3_tarski(sK3)) | sP0(k3_tarski(sK3),k2_yellow_1(sK3),k1_xboole_0) | v1_xboole_0(sK3) | ~m1_subset_1(k3_tarski(sK3),sK3)),
% 0.22/0.53    inference(resolution,[],[f285,f155])).
% 0.22/0.53  fof(f155,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(sK4(X0,k2_yellow_1(X1),k1_xboole_0),X1) | sP0(X0,k2_yellow_1(X1),k1_xboole_0) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.22/0.53    inference(resolution,[],[f154,f118])).
% 0.22/0.53  fof(f118,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.53    inference(flattening,[],[f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.53  fof(f154,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(sK4(X0,k2_yellow_1(X1),k1_xboole_0),X1) | ~m1_subset_1(X0,X1) | sP0(X0,k2_yellow_1(X1),k1_xboole_0)) )),
% 0.22/0.53    inference(forward_demodulation,[],[f153,f85])).
% 0.22/0.53  fof(f153,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | m1_subset_1(sK4(X0,k2_yellow_1(X1),k1_xboole_0),u1_struct_0(k2_yellow_1(X1))) | sP0(X0,k2_yellow_1(X1),k1_xboole_0)) )),
% 0.22/0.53    inference(resolution,[],[f152,f96])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_lattice3(X1,X2,X0) | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) | sP0(X0,X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f63])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (~r1_orders_2(X1,sK4(X0,X1,X2),X0) & r1_lattice3(X1,X2,sK4(X0,X1,X2)) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))) | ~r1_lattice3(X1,X2,X0)) & ((! [X4] : (r1_orders_2(X1,X4,X0) | ~r1_lattice3(X1,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & r1_lattice3(X1,X2,X0)) | ~sP0(X0,X1,X2)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f61,f62])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X1,X3,X0) & r1_lattice3(X1,X2,X3) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_orders_2(X1,sK4(X0,X1,X2),X0) & r1_lattice3(X1,X2,sK4(X0,X1,X2)) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (~r1_orders_2(X1,X3,X0) & r1_lattice3(X1,X2,X3) & m1_subset_1(X3,u1_struct_0(X1))) | ~r1_lattice3(X1,X2,X0)) & ((! [X4] : (r1_orders_2(X1,X4,X0) | ~r1_lattice3(X1,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & r1_lattice3(X1,X2,X0)) | ~sP0(X0,X1,X2)))),
% 0.22/0.53    inference(rectify,[],[f60])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    ! [X2,X0,X1] : ((sP0(X2,X0,X1) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2)) & ((! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | ~sP0(X2,X0,X1)))),
% 0.22/0.53    inference(flattening,[],[f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ! [X2,X0,X1] : ((sP0(X2,X0,X1) | (? [X3] : (~r1_orders_2(X0,X3,X2) & r1_lattice3(X0,X1,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) & ((! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)) | ~sP0(X2,X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ! [X2,X0,X1] : (sP0(X2,X0,X1) <=> (! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2)))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.53  fof(f285,plain,(
% 0.22/0.53    ( ! [X1] : (~r2_hidden(sK4(k3_tarski(sK3),k2_yellow_1(sK3),X1),sK3) | sP0(k3_tarski(sK3),k2_yellow_1(sK3),X1) | ~r1_lattice3(k2_yellow_1(sK3),X1,k3_tarski(sK3))) )),
% 0.22/0.53    inference(resolution,[],[f283,f98])).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_orders_2(X1,sK4(X0,X1,X2),X0) | sP0(X0,X1,X2) | ~r1_lattice3(X1,X2,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f63])).
% 0.22/0.53  fof(f283,plain,(
% 0.22/0.53    ( ! [X0] : (r1_orders_2(k2_yellow_1(sK3),X0,k3_tarski(sK3)) | ~r2_hidden(X0,sK3)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f282,f116])).
% 0.22/0.53  fof(f282,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,sK3) | ~r2_hidden(X0,sK3) | r1_orders_2(k2_yellow_1(sK3),X0,k3_tarski(sK3))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f281,f78])).
% 0.22/0.53  fof(f281,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,sK3) | v1_xboole_0(sK3) | ~r2_hidden(X0,sK3) | r1_orders_2(k2_yellow_1(sK3),X0,k3_tarski(sK3))) )),
% 0.22/0.53    inference(resolution,[],[f280,f79])).
% 0.22/0.53  fof(f280,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(k3_tarski(X2),X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0) | ~r2_hidden(X1,X2) | r1_orders_2(k2_yellow_1(X0),X1,k3_tarski(X2))) )),
% 0.22/0.53    inference(resolution,[],[f278,f116])).
% 0.22/0.53  fof(f278,plain,(
% 0.22/0.53    ( ! [X4,X2,X3] : (~m1_subset_1(k3_tarski(X4),X3) | r1_orders_2(k2_yellow_1(X3),X2,k3_tarski(X4)) | ~m1_subset_1(X2,X3) | v1_xboole_0(X3) | ~r2_hidden(X2,X4)) )),
% 0.22/0.53    inference(resolution,[],[f276,f117])).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.22/0.53  fof(f276,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | ~m1_subset_1(X2,X1) | r1_orders_2(k2_yellow_1(X1),X2,X0) | ~m1_subset_1(X0,X1) | v1_xboole_0(X1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f275,f87])).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0] : (~v1_xboole_0(X0) => ~v2_struct_0(k2_yellow_1(X0)))),
% 0.22/0.53    inference(pure_predicate_removal,[],[f16])).
% 0.22/0.53  fof(f16,axiom,(
% 0.22/0.53    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).
% 0.22/0.53  fof(f275,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,X1) | ~m1_subset_1(X2,X1) | r1_orders_2(k2_yellow_1(X1),X2,X0) | v2_struct_0(k2_yellow_1(X1)) | ~r1_tarski(X2,X0) | v1_xboole_0(X1)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f274])).
% 0.22/0.53  fof(f274,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,X1) | ~m1_subset_1(X2,X1) | r1_orders_2(k2_yellow_1(X1),X2,X0) | v2_struct_0(k2_yellow_1(X1)) | ~m1_subset_1(X0,X1) | ~m1_subset_1(X2,X1) | ~r1_tarski(X2,X0) | v1_xboole_0(X1)) )),
% 0.22/0.53    inference(resolution,[],[f273,f126])).
% 0.22/0.53  fof(f126,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.22/0.53    inference(forward_demodulation,[],[f125,f85])).
% 0.22/0.53  fof(f125,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.22/0.53    inference(forward_demodulation,[],[f89,f85])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f56])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,axiom,(
% 0.22/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).
% 0.22/0.53  fof(f273,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | r1_orders_2(k2_yellow_1(X0),X1,X2) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.22/0.53    inference(forward_demodulation,[],[f272,f85])).
% 0.22/0.53  fof(f272,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | r1_orders_2(k2_yellow_1(X0),X1,X2) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.22/0.53    inference(forward_demodulation,[],[f271,f85])).
% 0.22/0.53  fof(f271,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | r1_orders_2(k2_yellow_1(X0),X1,X2) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f270,f82])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 0.22/0.53    inference(pure_predicate_removal,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.22/0.53    inference(pure_predicate_removal,[],[f15])).
% 0.22/0.53  fof(f15,axiom,(
% 0.22/0.53    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.22/0.53  fof(f270,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0))) )),
% 0.22/0.53    inference(resolution,[],[f120,f84])).
% 0.22/0.53  fof(f120,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f77])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.22/0.53  fof(f360,plain,(
% 0.22/0.53    ( ! [X0] : (~sP0(X0,k2_yellow_1(sK3),k1_xboole_0) | ~m1_subset_1(X0,sK3) | k4_yellow_0(k2_yellow_1(sK3)) = X0) )),
% 0.22/0.53    inference(forward_demodulation,[],[f355,f133])).
% 0.22/0.53  fof(f133,plain,(
% 0.22/0.53    ( ! [X0] : (k4_yellow_0(k2_yellow_1(X0)) = k2_yellow_0(k2_yellow_1(X0),k1_xboole_0)) )),
% 0.22/0.53    inference(resolution,[],[f91,f84])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_orders_2(X0) | k4_yellow_0(X0) = k2_yellow_0(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0] : (k4_yellow_0(X0) = k2_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0] : (l1_orders_2(X0) => k4_yellow_0(X0) = k2_yellow_0(X0,k1_xboole_0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_yellow_0)).
% 0.22/0.53  fof(f355,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,sK3) | ~sP0(X0,k2_yellow_1(sK3),k1_xboole_0) | k2_yellow_0(k2_yellow_1(sK3),k1_xboole_0) = X0) )),
% 0.22/0.53    inference(resolution,[],[f352,f93])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | k2_yellow_0(X1,X0) = X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f58])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((k2_yellow_0(X1,X0) = X2 | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | k2_yellow_0(X1,X0) != X2)) | ~sP1(X0,X1,X2))),
% 0.22/0.53    inference(rectify,[],[f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ! [X1,X0,X2] : (((k2_yellow_0(X0,X1) = X2 | ~sP0(X2,X0,X1)) & (sP0(X2,X0,X1) | k2_yellow_0(X0,X1) != X2)) | ~sP1(X1,X0,X2))),
% 0.22/0.53    inference(nnf_transformation,[],[f50])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ! [X1,X0,X2] : ((k2_yellow_0(X0,X1) = X2 <=> sP0(X2,X0,X1)) | ~sP1(X1,X0,X2))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.53  fof(f352,plain,(
% 0.22/0.53    ( ! [X0] : (sP1(k1_xboole_0,k2_yellow_1(sK3),X0) | ~m1_subset_1(X0,sK3)) )),
% 0.22/0.53    inference(forward_demodulation,[],[f351,f85])).
% 0.22/0.53  fof(f351,plain,(
% 0.22/0.53    ( ! [X0] : (sP1(k1_xboole_0,k2_yellow_1(sK3),X0) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK3)))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f345,f84])).
% 0.22/0.53  fof(f345,plain,(
% 0.22/0.53    ( ! [X0] : (sP1(k1_xboole_0,k2_yellow_1(sK3),X0) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK3))) | ~l1_orders_2(k2_yellow_1(sK3))) )),
% 0.22/0.53    inference(resolution,[],[f341,f99])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_yellow_0(X0,X1) | sP1(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ! [X0] : (! [X1,X2] : (sP1(X1,X0,X2) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(definition_folding,[],[f33,f50,f49])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X0] : (! [X1,X2] : ((k2_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2))) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(flattening,[],[f32])).
% 0.22/0.53  % (19280)Refutation not found, incomplete strategy% (19280)------------------------------
% 0.22/0.53  % (19280)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (19280)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (19280)Memory used [KB]: 10618
% 0.22/0.53  % (19280)Time elapsed: 0.126 s
% 0.22/0.53  % (19280)------------------------------
% 0.22/0.53  % (19280)------------------------------
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2))) | ~r2_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_yellow_0(X0,X1) => (k2_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) => r1_orders_2(X0,X3,X2))) & r1_lattice3(X0,X1,X2))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_yellow_0)).
% 0.22/0.53  fof(f341,plain,(
% 0.22/0.53    r2_yellow_0(k2_yellow_1(sK3),k1_xboole_0)),
% 0.22/0.53    inference(resolution,[],[f340,f323])).
% 0.22/0.53  fof(f323,plain,(
% 0.22/0.53    r1_lattice3(k2_yellow_1(sK3),k1_xboole_0,k3_tarski(sK3))),
% 0.22/0.53    inference(resolution,[],[f321,f94])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | r1_lattice3(X1,X2,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f63])).
% 0.22/0.53  fof(f340,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_lattice3(k2_yellow_1(sK3),X0,k3_tarski(sK3)) | r2_yellow_0(k2_yellow_1(sK3),X0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f339,f79])).
% 0.22/0.53  fof(f339,plain,(
% 0.22/0.53    ( ! [X0] : (~r1_lattice3(k2_yellow_1(sK3),X0,k3_tarski(sK3)) | r2_yellow_0(k2_yellow_1(sK3),X0) | ~r2_hidden(k3_tarski(sK3),sK3)) )),
% 0.22/0.53    inference(resolution,[],[f338,f116])).
% 0.22/0.53  fof(f338,plain,(
% 0.22/0.53    ( ! [X1] : (~m1_subset_1(k3_tarski(sK3),sK3) | ~r1_lattice3(k2_yellow_1(sK3),X1,k3_tarski(sK3)) | r2_yellow_0(k2_yellow_1(sK3),X1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f336,f176])).
% 0.22/0.53  fof(f176,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (m1_subset_1(sK7(X0,k2_yellow_1(X1),X2),X1) | ~m1_subset_1(X0,X1) | ~r1_lattice3(k2_yellow_1(X1),X2,X0) | r2_yellow_0(k2_yellow_1(X1),X2)) )),
% 0.22/0.53    inference(forward_demodulation,[],[f175,f85])).
% 0.22/0.53  fof(f175,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,X1) | ~r1_lattice3(k2_yellow_1(X1),X2,X0) | r2_yellow_0(k2_yellow_1(X1),X2) | m1_subset_1(sK7(X0,k2_yellow_1(X1),X2),u1_struct_0(k2_yellow_1(X1)))) )),
% 0.22/0.53    inference(resolution,[],[f174,f108])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f75])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((~r1_orders_2(X1,sK7(X0,X1,X2),X0) & r1_lattice3(X1,X2,sK7(X0,X1,X2)) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))) | ~sP2(X0,X1,X2))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f73,f74])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X1,X3,X0) & r1_lattice3(X1,X2,X3) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_orders_2(X1,sK7(X0,X1,X2),X0) & r1_lattice3(X1,X2,sK7(X0,X1,X2)) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (? [X3] : (~r1_orders_2(X1,X3,X0) & r1_lattice3(X1,X2,X3) & m1_subset_1(X3,u1_struct_0(X1))) | ~sP2(X0,X1,X2))),
% 0.22/0.53    inference(rectify,[],[f72])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ! [X1,X0,X2] : (? [X3] : (~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~sP2(X1,X0,X2))),
% 0.22/0.53    inference(nnf_transformation,[],[f52])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ! [X1,X0,X2] : (? [X3] : (~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~sP2(X1,X0,X2))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.53  fof(f174,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (sP2(X0,k2_yellow_1(X1),X2) | ~m1_subset_1(X0,X1) | ~r1_lattice3(k2_yellow_1(X1),X2,X0) | r2_yellow_0(k2_yellow_1(X1),X2)) )),
% 0.22/0.53    inference(forward_demodulation,[],[f173,f85])).
% 0.22/0.53  fof(f173,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (sP2(X0,k2_yellow_1(X1),X2) | ~r1_lattice3(k2_yellow_1(X1),X2,X0) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) | r2_yellow_0(k2_yellow_1(X1),X2)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f172,f84])).
% 0.22/0.54  fof(f172,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (sP2(X0,k2_yellow_1(X1),X2) | ~r1_lattice3(k2_yellow_1(X1),X2,X0) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) | ~l1_orders_2(k2_yellow_1(X1)) | r2_yellow_0(k2_yellow_1(X1),X2)) )),
% 0.22/0.54    inference(resolution,[],[f114,f83])).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f114,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | sP2(X1,X0,X2) | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_yellow_0(X0,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f76])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | sP2(X1,X0,X2) | ~r1_lattice3(X0,X2,X1)) & ((! [X3] : (r1_orders_2(X0,X3,X1) | ~r1_lattice3(X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | ~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.22/0.54    inference(rectify,[],[f53])).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | sP2(X1,X0,X2) | ~r1_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | ~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.22/0.54    inference(definition_folding,[],[f39,f52])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | ~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.22/0.54    inference(flattening,[],[f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | (~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1)) => (r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1)) & ((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X4) => r1_orders_2(X0,X4,X1))) & r1_lattice3(X0,X2,X1))))))),
% 0.22/0.54    inference(rectify,[],[f13])).
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1)) => (r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1)) & ((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1))))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_yellow_0)).
% 0.22/0.54  fof(f336,plain,(
% 0.22/0.54    ( ! [X1] : (~m1_subset_1(sK7(k3_tarski(sK3),k2_yellow_1(sK3),X1),sK3) | ~m1_subset_1(k3_tarski(sK3),sK3) | ~r1_lattice3(k2_yellow_1(sK3),X1,k3_tarski(sK3)) | r2_yellow_0(k2_yellow_1(sK3),X1)) )),
% 0.22/0.54    inference(resolution,[],[f332,f174])).
% 0.22/0.54  fof(f332,plain,(
% 0.22/0.54    ( ! [X0] : (~sP2(k3_tarski(sK3),k2_yellow_1(sK3),X0) | ~m1_subset_1(sK7(k3_tarski(sK3),k2_yellow_1(sK3),X0),sK3)) )),
% 0.22/0.54    inference(resolution,[],[f325,f110])).
% 0.22/0.54  fof(f110,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_orders_2(X1,sK7(X0,X1,X2),X0) | ~sP2(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f75])).
% 0.22/0.54  fof(f325,plain,(
% 0.22/0.54    ( ! [X0] : (r1_orders_2(k2_yellow_1(sK3),X0,k3_tarski(sK3)) | ~m1_subset_1(X0,sK3)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f324,f152])).
% 0.22/0.54  fof(f324,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(X0,sK3) | ~r1_lattice3(k2_yellow_1(sK3),k1_xboole_0,X0) | r1_orders_2(k2_yellow_1(sK3),X0,k3_tarski(sK3))) )),
% 0.22/0.54    inference(forward_demodulation,[],[f322,f85])).
% 0.22/0.54  fof(f322,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_lattice3(k2_yellow_1(sK3),k1_xboole_0,X0) | ~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK3))) | r1_orders_2(k2_yellow_1(sK3),X0,k3_tarski(sK3))) )),
% 0.22/0.54    inference(resolution,[],[f321,f95])).
% 0.22/0.54  fof(f95,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r1_lattice3(X1,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_orders_2(X1,X4,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f63])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (19282)------------------------------
% 0.22/0.54  % (19282)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (19282)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (19282)Memory used [KB]: 6524
% 0.22/0.54  % (19282)Time elapsed: 0.126 s
% 0.22/0.54  % (19282)------------------------------
% 0.22/0.54  % (19282)------------------------------
% 0.22/0.54  % (19288)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.54  % (19278)Success in time 0.176 s
%------------------------------------------------------------------------------
