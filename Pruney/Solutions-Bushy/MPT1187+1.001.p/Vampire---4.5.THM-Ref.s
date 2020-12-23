%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1187+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  207 ( 526 expanded)
%              Number of leaves         :   49 ( 203 expanded)
%              Depth                    :   12
%              Number of atoms          :  758 (3367 expanded)
%              Number of equality atoms :   40 ( 101 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f944,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f104,f108,f118,f140,f146,f173,f178,f179,f260,f280,f290,f310,f328,f329,f380,f447,f448,f498,f509,f567,f636,f656,f745,f752,f895,f900,f925,f932,f943])).

fof(f943,plain,
    ( ~ spl4_26
    | ~ spl4_1
    | spl4_95
    | ~ spl4_92
    | ~ spl4_36
    | ~ spl4_80 ),
    inference(avatar_split_clause,[],[f942,f789,f318,f840,f860,f92,f236])).

fof(f236,plain,
    ( spl4_26
  <=> v1_relat_1(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f92,plain,
    ( spl4_1
  <=> r6_orders_1(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f860,plain,
    ( spl4_95
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_95])])).

fof(f840,plain,
    ( spl4_92
  <=> r2_hidden(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_92])])).

fof(f318,plain,
    ( spl4_36
  <=> u1_struct_0(sK0) = k3_relat_1(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f789,plain,
    ( spl4_80
  <=> r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).

fof(f942,plain,
    ( ~ r2_hidden(sK2,u1_struct_0(sK0))
    | sK1 = sK2
    | ~ r6_orders_1(u1_orders_2(sK0),sK1)
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl4_36
    | ~ spl4_80 ),
    inference(forward_demodulation,[],[f940,f320])).

fof(f320,plain,
    ( u1_struct_0(sK0) = k3_relat_1(u1_orders_2(sK0))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f318])).

fof(f940,plain,
    ( sK1 = sK2
    | ~ r2_hidden(sK2,k3_relat_1(u1_orders_2(sK0)))
    | ~ r6_orders_1(u1_orders_2(sK0),sK1)
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl4_80 ),
    inference(resolution,[],[f790,f71])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X3),X0)
      | X1 = X3
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ r6_orders_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r6_orders_1(X0,X1)
            | ( r2_hidden(k4_tarski(X1,sK3(X0,X1)),X0)
              & sK3(X0,X1) != X1
              & r2_hidden(sK3(X0,X1),k3_relat_1(X0)) )
            | ~ r2_hidden(X1,k3_relat_1(X0)) )
          & ( ( ! [X3] :
                  ( ~ r2_hidden(k4_tarski(X1,X3),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,k3_relat_1(X0)) )
              & r2_hidden(X1,k3_relat_1(X0)) )
            | ~ r6_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f54,f55])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r2_hidden(k4_tarski(X1,X2),X0)
          & X1 != X2
          & r2_hidden(X2,k3_relat_1(X0)) )
     => ( r2_hidden(k4_tarski(X1,sK3(X0,X1)),X0)
        & sK3(X0,X1) != X1
        & r2_hidden(sK3(X0,X1),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r6_orders_1(X0,X1)
            | ? [X2] :
                ( r2_hidden(k4_tarski(X1,X2),X0)
                & X1 != X2
                & r2_hidden(X2,k3_relat_1(X0)) )
            | ~ r2_hidden(X1,k3_relat_1(X0)) )
          & ( ( ! [X3] :
                  ( ~ r2_hidden(k4_tarski(X1,X3),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,k3_relat_1(X0)) )
              & r2_hidden(X1,k3_relat_1(X0)) )
            | ~ r6_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r6_orders_1(X0,X1)
            | ? [X2] :
                ( r2_hidden(k4_tarski(X1,X2),X0)
                & X1 != X2
                & r2_hidden(X2,k3_relat_1(X0)) )
            | ~ r2_hidden(X1,k3_relat_1(X0)) )
          & ( ( ! [X2] :
                  ( ~ r2_hidden(k4_tarski(X1,X2),X0)
                  | X1 = X2
                  | ~ r2_hidden(X2,k3_relat_1(X0)) )
              & r2_hidden(X1,k3_relat_1(X0)) )
            | ~ r6_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r6_orders_1(X0,X1)
            | ? [X2] :
                ( r2_hidden(k4_tarski(X1,X2),X0)
                & X1 != X2
                & r2_hidden(X2,k3_relat_1(X0)) )
            | ~ r2_hidden(X1,k3_relat_1(X0)) )
          & ( ( ! [X2] :
                  ( ~ r2_hidden(k4_tarski(X1,X2),X0)
                  | X1 = X2
                  | ~ r2_hidden(X2,k3_relat_1(X0)) )
              & r2_hidden(X1,k3_relat_1(X0)) )
            | ~ r6_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r6_orders_1(X0,X1)
        <=> ( ! [X2] :
                ( ~ r2_hidden(k4_tarski(X1,X2),X0)
                | X1 = X2
                | ~ r2_hidden(X2,k3_relat_1(X0)) )
            & r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r6_orders_1(X0,X1)
        <=> ( ! [X2] :
                ~ ( r2_hidden(k4_tarski(X1,X2),X0)
                  & X1 != X2
                  & r2_hidden(X2,k3_relat_1(X0)) )
            & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_orders_1)).

fof(f790,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ spl4_80 ),
    inference(avatar_component_clause,[],[f789])).

fof(f932,plain,
    ( ~ spl4_31
    | ~ spl4_3
    | spl4_80
    | ~ spl4_59 ),
    inference(avatar_split_clause,[],[f928,f501,f789,f101,f264])).

fof(f264,plain,
    ( spl4_31
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f101,plain,
    ( spl4_3
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f501,plain,
    ( spl4_59
  <=> r1_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f928,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_59 ),
    inference(resolution,[],[f503,f152])).

fof(f152,plain,(
    ! [X4,X5] :
      ( ~ r1_orders_2(sK0,X4,X5)
      | r2_hidden(k4_tarski(X4,X5),u1_orders_2(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f62,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

fof(f62,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( ( r2_orders_2(sK0,sK1,sK2)
        & m1_subset_1(sK2,u1_struct_0(sK0)) )
      | ~ r6_orders_1(u1_orders_2(sK0),sK1) )
    & ( ! [X3] :
          ( ~ r2_orders_2(sK0,sK1,X3)
          | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
      | r6_orders_1(u1_orders_2(sK0),sK1) )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f45,f48,f47,f46])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( r2_orders_2(X0,X1,X2)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ r6_orders_1(u1_orders_2(X0),X1) )
            & ( ! [X3] :
                  ( ~ r2_orders_2(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | r6_orders_1(u1_orders_2(X0),X1) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( r2_orders_2(sK0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(sK0)) )
            | ~ r6_orders_1(u1_orders_2(sK0),X1) )
          & ( ! [X3] :
                ( ~ r2_orders_2(sK0,X1,X3)
                | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
            | r6_orders_1(u1_orders_2(sK0),X1) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X1] :
        ( ( ? [X2] :
              ( r2_orders_2(sK0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          | ~ r6_orders_1(u1_orders_2(sK0),X1) )
        & ( ! [X3] :
              ( ~ r2_orders_2(sK0,X1,X3)
              | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
          | r6_orders_1(u1_orders_2(sK0),X1) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ( ? [X2] :
            ( r2_orders_2(sK0,sK1,X2)
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        | ~ r6_orders_1(u1_orders_2(sK0),sK1) )
      & ( ! [X3] :
            ( ~ r2_orders_2(sK0,sK1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
        | r6_orders_1(u1_orders_2(sK0),sK1) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X2] :
        ( r2_orders_2(sK0,sK1,X2)
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( r2_orders_2(sK0,sK1,sK2)
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( r2_orders_2(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r6_orders_1(u1_orders_2(X0),X1) )
          & ( ! [X3] :
                ( ~ r2_orders_2(X0,X1,X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            | r6_orders_1(u1_orders_2(X0),X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( r2_orders_2(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r6_orders_1(u1_orders_2(X0),X1) )
          & ( ! [X2] :
                ( ~ r2_orders_2(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | r6_orders_1(u1_orders_2(X0),X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( r2_orders_2(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r6_orders_1(u1_orders_2(X0),X1) )
          & ( ! [X2] :
                ( ~ r2_orders_2(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | r6_orders_1(u1_orders_2(X0),X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r6_orders_1(u1_orders_2(X0),X1)
          <~> ! [X2] :
                ( ~ r2_orders_2(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r6_orders_1(u1_orders_2(X0),X1)
          <~> ! [X2] :
                ( ~ r2_orders_2(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( r6_orders_1(u1_orders_2(X0),X1)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ r2_orders_2(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r6_orders_1(u1_orders_2(X0),X1)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ r2_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_orders_2)).

fof(f503,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ spl4_59 ),
    inference(avatar_component_clause,[],[f501])).

fof(f925,plain,
    ( spl4_6
    | spl4_92
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f913,f101,f840,f115])).

fof(f115,plain,
    ( spl4_6
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f913,plain,
    ( r2_hidden(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_3 ),
    inference(resolution,[],[f103,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f103,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f900,plain,
    ( ~ spl4_7
    | ~ spl4_31
    | ~ spl4_3
    | spl4_59
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f898,f96,f501,f101,f264,f122])).

fof(f122,plain,
    ( spl4_7
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f96,plain,
    ( spl4_2
  <=> r2_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f898,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f98,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

fof(f98,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f895,plain,
    ( ~ spl4_7
    | ~ spl4_31
    | ~ spl4_2
    | ~ spl4_95 ),
    inference(avatar_split_clause,[],[f882,f860,f96,f264,f122])).

fof(f882,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl4_2
    | ~ spl4_95 ),
    inference(resolution,[],[f871,f90])).

fof(f90,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f871,plain,
    ( r2_orders_2(sK0,sK1,sK1)
    | ~ spl4_2
    | ~ spl4_95 ),
    inference(backward_demodulation,[],[f98,f862])).

fof(f862,plain,
    ( sK1 = sK2
    | ~ spl4_95 ),
    inference(avatar_component_clause,[],[f860])).

fof(f752,plain,
    ( spl4_29
    | ~ spl4_55
    | ~ spl4_32
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f747,f475,f268,f471,f249])).

fof(f249,plain,
    ( spl4_29
  <=> sK1 = sK3(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f471,plain,
    ( spl4_55
  <=> m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f268,plain,
    ( spl4_32
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | sK1 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f475,plain,
    ( spl4_56
  <=> r1_orders_2(sK0,sK1,sK3(u1_orders_2(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f747,plain,
    ( ~ m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | sK1 = sK3(u1_orders_2(sK0),sK1)
    | ~ spl4_32
    | ~ spl4_56 ),
    inference(resolution,[],[f477,f269])).

fof(f269,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK1 = X0 )
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f268])).

fof(f477,plain,
    ( r1_orders_2(sK0,sK1,sK3(u1_orders_2(sK0),sK1))
    | ~ spl4_56 ),
    inference(avatar_component_clause,[],[f475])).

fof(f745,plain,
    ( ~ spl4_28
    | ~ spl4_36
    | spl4_55 ),
    inference(avatar_contradiction_clause,[],[f743])).

fof(f743,plain,
    ( $false
    | ~ spl4_28
    | ~ spl4_36
    | spl4_55 ),
    inference(unit_resulting_resolution,[],[f579,f473,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f473,plain,
    ( ~ m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | spl4_55 ),
    inference(avatar_component_clause,[],[f471])).

fof(f579,plain,
    ( r2_hidden(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | ~ spl4_28
    | ~ spl4_36 ),
    inference(backward_demodulation,[],[f246,f320])).

fof(f246,plain,
    ( r2_hidden(sK3(u1_orders_2(sK0),sK1),k3_relat_1(u1_orders_2(sK0)))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl4_28
  <=> r2_hidden(sK3(u1_orders_2(sK0),sK1),k3_relat_1(u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f656,plain,
    ( ~ spl4_36
    | spl4_39 ),
    inference(avatar_contradiction_clause,[],[f651])).

fof(f651,plain,
    ( $false
    | ~ spl4_36
    | spl4_39 ),
    inference(unit_resulting_resolution,[],[f63,f578])).

fof(f578,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_36
    | spl4_39 ),
    inference(backward_demodulation,[],[f350,f320])).

fof(f350,plain,
    ( ~ m1_subset_1(sK1,k3_relat_1(u1_orders_2(sK0)))
    | spl4_39 ),
    inference(avatar_component_clause,[],[f348])).

fof(f348,plain,
    ( spl4_39
  <=> m1_subset_1(sK1,k3_relat_1(u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f63,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f636,plain,
    ( ~ spl4_5
    | ~ spl4_36
    | ~ spl4_40 ),
    inference(avatar_contradiction_clause,[],[f631])).

fof(f631,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_36
    | ~ spl4_40 ),
    inference(unit_resulting_resolution,[],[f58,f112,f581,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f581,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_36
    | ~ spl4_40 ),
    inference(backward_demodulation,[],[f354,f320])).

fof(f354,plain,
    ( v1_xboole_0(k3_relat_1(u1_orders_2(sK0)))
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f352])).

fof(f352,plain,
    ( spl4_40
  <=> v1_xboole_0(k3_relat_1(u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f112,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl4_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f58,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f567,plain,
    ( ~ spl4_7
    | ~ spl4_31
    | ~ spl4_55
    | spl4_56
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f564,f254,f475,f471,f264,f122])).

fof(f254,plain,
    ( spl4_30
  <=> r2_hidden(k4_tarski(sK1,sK3(u1_orders_2(sK0),sK1)),u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f564,plain,
    ( r1_orders_2(sK0,sK1,sK3(u1_orders_2(sK0),sK1))
    | ~ m1_subset_1(sK3(u1_orders_2(sK0),sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ spl4_30 ),
    inference(resolution,[],[f256,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f256,plain,
    ( r2_hidden(k4_tarski(sK1,sK3(u1_orders_2(sK0),sK1)),u1_orders_2(sK0))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f254])).

fof(f509,plain,
    ( ~ spl4_7
    | ~ spl4_31
    | spl4_32
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f508,f106,f268,f264,f122])).

fof(f106,plain,
    ( spl4_4
  <=> ! [X3] :
        ( ~ r2_orders_2(sK0,sK1,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f508,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK1 = X0
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl4_4 ),
    inference(duplicate_literal_removal,[],[f507])).

fof(f507,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sK1 = X0
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f107,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(X0,X1,X2)
      | X1 = X2
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f107,plain,
    ( ! [X3] :
        ( ~ r2_orders_2(sK0,sK1,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f498,plain,
    ( ~ spl4_26
    | ~ spl4_27
    | ~ spl4_29
    | spl4_1 ),
    inference(avatar_split_clause,[],[f496,f92,f249,f240,f236])).

fof(f240,plain,
    ( spl4_27
  <=> r2_hidden(sK1,k3_relat_1(u1_orders_2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f496,plain,
    ( sK1 != sK3(u1_orders_2(sK0),sK1)
    | ~ r2_hidden(sK1,k3_relat_1(u1_orders_2(sK0)))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | spl4_1 ),
    inference(resolution,[],[f94,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r6_orders_1(X0,X1)
      | sK3(X0,X1) != X1
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f94,plain,
    ( ~ r6_orders_1(u1_orders_2(sK0),sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f448,plain,
    ( ~ spl4_26
    | spl4_30
    | spl4_1
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f443,f240,f92,f254,f236])).

fof(f443,plain,
    ( r6_orders_1(u1_orders_2(sK0),sK1)
    | r2_hidden(k4_tarski(sK1,sK3(u1_orders_2(sK0),sK1)),u1_orders_2(sK0))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl4_27 ),
    inference(resolution,[],[f241,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r6_orders_1(X0,X1)
      | r2_hidden(k4_tarski(X1,sK3(X0,X1)),X0)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f241,plain,
    ( r2_hidden(sK1,k3_relat_1(u1_orders_2(sK0)))
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f240])).

fof(f447,plain,
    ( ~ spl4_26
    | spl4_28
    | spl4_1
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f441,f240,f92,f244,f236])).

fof(f441,plain,
    ( r6_orders_1(u1_orders_2(sK0),sK1)
    | r2_hidden(sK3(u1_orders_2(sK0),sK1),k3_relat_1(u1_orders_2(sK0)))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl4_27 ),
    inference(resolution,[],[f241,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r6_orders_1(X0,X1)
      | r2_hidden(sK3(X0,X1),k3_relat_1(X0))
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f380,plain,
    ( ~ spl4_39
    | spl4_40
    | spl4_27 ),
    inference(avatar_split_clause,[],[f378,f240,f352,f348])).

fof(f378,plain,
    ( v1_xboole_0(k3_relat_1(u1_orders_2(sK0)))
    | ~ m1_subset_1(sK1,k3_relat_1(u1_orders_2(sK0)))
    | spl4_27 ),
    inference(resolution,[],[f242,f84])).

fof(f242,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(u1_orders_2(sK0)))
    | spl4_27 ),
    inference(avatar_component_clause,[],[f240])).

fof(f329,plain,
    ( ~ spl4_8
    | ~ spl4_11
    | ~ spl4_10
    | ~ spl4_15
    | spl4_36 ),
    inference(avatar_split_clause,[],[f325,f318,f175,f137,f143,f126])).

fof(f126,plain,
    ( spl4_8
  <=> v1_relat_2(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f143,plain,
    ( spl4_11
  <=> v4_relat_2(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f137,plain,
    ( spl4_10
  <=> v8_relat_2(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f175,plain,
    ( spl4_15
  <=> v1_partfun1(u1_orders_2(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f325,plain,
    ( u1_struct_0(sK0) = k3_relat_1(u1_orders_2(sK0))
    | ~ v1_partfun1(u1_orders_2(sK0),u1_struct_0(sK0))
    | ~ v8_relat_2(u1_orders_2(sK0))
    | ~ v4_relat_2(u1_orders_2(sK0))
    | ~ v1_relat_2(u1_orders_2(sK0)) ),
    inference(resolution,[],[f155,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v4_relat_2(X1)
      | ~ v1_relat_2(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v4_relat_2(X1)
      | ~ v1_relat_2(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_partfun1(X1,X0)
      | ~ v8_relat_2(X1)
      | ~ v4_relat_2(X1)
      | ~ v1_relat_2(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_partfun1(X1,X0)
        & v8_relat_2(X1)
        & v4_relat_2(X1)
        & v1_relat_2(X1) )
     => k3_relat_1(X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_orders_1)).

fof(f155,plain,(
    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f62,f86])).

fof(f86,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f328,plain,(
    spl4_26 ),
    inference(avatar_contradiction_clause,[],[f324])).

fof(f324,plain,
    ( $false
    | spl4_26 ),
    inference(unit_resulting_resolution,[],[f238,f155,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f238,plain,
    ( ~ v1_relat_1(u1_orders_2(sK0))
    | spl4_26 ),
    inference(avatar_component_clause,[],[f236])).

fof(f310,plain,(
    spl4_31 ),
    inference(avatar_contradiction_clause,[],[f305])).

fof(f305,plain,
    ( $false
    | spl4_31 ),
    inference(unit_resulting_resolution,[],[f63,f266])).

fof(f266,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl4_31 ),
    inference(avatar_component_clause,[],[f264])).

fof(f290,plain,(
    spl4_14 ),
    inference(avatar_contradiction_clause,[],[f287])).

fof(f287,plain,
    ( $false
    | spl4_14 ),
    inference(unit_resulting_resolution,[],[f59,f172])).

fof(f172,plain,
    ( ~ v3_orders_2(sK0)
    | spl4_14 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl4_14
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f59,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f280,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | spl4_7 ),
    inference(unit_resulting_resolution,[],[f62,f124])).

fof(f124,plain,
    ( ~ l1_orders_2(sK0)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f122])).

fof(f260,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f258])).

fof(f258,plain,
    ( $false
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f62,f113,f85])).

fof(f85,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f113,plain,
    ( ~ l1_struct_0(sK0)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f111])).

fof(f179,plain,
    ( ~ spl4_14
    | spl4_8 ),
    inference(avatar_split_clause,[],[f157,f126,f170])).

fof(f157,plain,
    ( v1_relat_2(u1_orders_2(sK0))
    | ~ v3_orders_2(sK0) ),
    inference(resolution,[],[f62,f88])).

fof(f88,plain,(
    ! [X0] :
      ( v1_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( v1_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( v1_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => v1_relat_2(u1_orders_2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_orders_2)).

fof(f178,plain,
    ( ~ spl4_9
    | spl4_15 ),
    inference(avatar_split_clause,[],[f156,f175,f131])).

fof(f131,plain,
    ( spl4_9
  <=> v2_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f156,plain,
    ( v1_partfun1(u1_orders_2(sK0),u1_struct_0(sK0))
    | ~ v2_orders_2(sK0) ),
    inference(resolution,[],[f62,f87])).

fof(f87,plain,(
    ! [X0] :
      ( v1_partfun1(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( v1_partfun1(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( v1_partfun1(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_orders_2(X0) )
     => v1_partfun1(u1_orders_2(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_orders_2)).

fof(f173,plain,
    ( ~ spl4_14
    | spl4_9 ),
    inference(avatar_split_clause,[],[f151,f131,f170])).

fof(f151,plain,
    ( v2_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(resolution,[],[f62,f77])).

fof(f77,plain,(
    ! [X0] :
      ( v2_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v2_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v2_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v3_orders_2(X0)
       => v2_orders_2(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_orders_2)).

fof(f146,plain,
    ( ~ spl4_9
    | ~ spl4_7
    | spl4_11 ),
    inference(avatar_split_clause,[],[f141,f143,f122,f131])).

fof(f141,plain,
    ( v4_relat_2(u1_orders_2(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_orders_2(sK0) ),
    inference(resolution,[],[f61,f75])).

fof(f75,plain,(
    ! [X0] :
      ( v4_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v4_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v4_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v2_orders_2(X0) )
     => v4_relat_2(u1_orders_2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_orders_2)).

fof(f61,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f140,plain,
    ( ~ spl4_9
    | ~ spl4_7
    | spl4_10 ),
    inference(avatar_split_clause,[],[f135,f137,f122,f131])).

fof(f135,plain,
    ( v8_relat_2(u1_orders_2(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_orders_2(sK0) ),
    inference(resolution,[],[f60,f76])).

fof(f76,plain,(
    ! [X0] :
      ( v8_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v8_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v8_relat_2(u1_orders_2(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v2_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v2_orders_2(X0) )
     => v8_relat_2(u1_orders_2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_orders_2)).

fof(f60,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f118,plain,
    ( ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f109,f115,f111])).

fof(f109,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f58,f78])).

fof(f108,plain,
    ( spl4_1
    | spl4_4 ),
    inference(avatar_split_clause,[],[f64,f106,f92])).

fof(f64,plain,(
    ! [X3] :
      ( ~ r2_orders_2(sK0,sK1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r6_orders_1(u1_orders_2(sK0),sK1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f104,plain,
    ( ~ spl4_1
    | spl4_3 ),
    inference(avatar_split_clause,[],[f65,f101,f92])).

fof(f65,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r6_orders_1(u1_orders_2(sK0),sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f99,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f66,f96,f92])).

fof(f66,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ r6_orders_1(u1_orders_2(sK0),sK1) ),
    inference(cnf_transformation,[],[f49])).

%------------------------------------------------------------------------------
