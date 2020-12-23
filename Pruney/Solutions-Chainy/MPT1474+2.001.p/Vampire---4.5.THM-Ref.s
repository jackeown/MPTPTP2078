%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  245 ( 583 expanded)
%              Number of leaves         :   49 ( 245 expanded)
%              Depth                    :   15
%              Number of atoms          : 1058 (2952 expanded)
%              Number of equality atoms :   63 ( 142 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f428,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f119,f120,f135,f137,f139,f174,f176,f181,f191,f196,f220,f225,f230,f280,f297,f338,f358,f363,f365,f367,f370,f380,f387,f393,f395,f400,f402,f411,f415,f423,f427])).

fof(f427,plain,
    ( spl7_22
    | ~ spl7_34
    | ~ spl7_33
    | ~ spl7_35
    | spl7_39 ),
    inference(avatar_split_clause,[],[f426,f420,f377,f351,f355,f254])).

fof(f254,plain,
    ( spl7_22
  <=> v1_xboole_0(u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f355,plain,
    ( spl7_34
  <=> m1_subset_1(sK4,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f351,plain,
    ( spl7_33
  <=> m1_subset_1(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f377,plain,
    ( spl7_35
  <=> r2_hidden(k4_tarski(sK4,sK5),k8_filter_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f420,plain,
    ( spl7_39
  <=> r2_hidden(k1_domain_1(u1_struct_0(sK3),u1_struct_0(sK3),sK4,sK5),k8_filter_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f426,plain,
    ( ~ r2_hidden(k4_tarski(sK4,sK5),k8_filter_1(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | spl7_39 ),
    inference(duplicate_literal_removal,[],[f425])).

fof(f425,plain,
    ( ~ r2_hidden(k4_tarski(sK4,sK5),k8_filter_1(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | spl7_39 ),
    inference(superposition,[],[f422,f110])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X1)
        & m1_subset_1(X2,X0)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_domain_1)).

fof(f422,plain,
    ( ~ r2_hidden(k1_domain_1(u1_struct_0(sK3),u1_struct_0(sK3),sK4,sK5),k8_filter_1(sK3))
    | spl7_39 ),
    inference(avatar_component_clause,[],[f420])).

fof(f423,plain,
    ( spl7_3
    | ~ spl7_4
    | ~ spl7_11
    | ~ spl7_34
    | ~ spl7_33
    | ~ spl7_39
    | spl7_1 ),
    inference(avatar_split_clause,[],[f418,f112,f420,f351,f355,f171,f128,f124])).

fof(f124,plain,
    ( spl7_3
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f128,plain,
    ( spl7_4
  <=> v10_lattices(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f171,plain,
    ( spl7_11
  <=> l3_lattices(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f112,plain,
    ( spl7_1
  <=> r3_lattices(sK3,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f418,plain,
    ( ~ r2_hidden(k1_domain_1(u1_struct_0(sK3),u1_struct_0(sK3),sK4,sK5),k8_filter_1(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ l3_lattices(sK3)
    | ~ v10_lattices(sK3)
    | v2_struct_0(sK3)
    | spl7_1 ),
    inference(resolution,[],[f114,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,X2)
      | ~ r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
                  | ~ r3_lattices(X0,X1,X2) )
                & ( r3_lattices(X0,X1,X2)
                  | ~ r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
              <=> r3_lattices(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
              <=> r3_lattices(X0,X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
              <=> r3_lattices(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_filter_1)).

fof(f114,plain,
    ( ~ r3_lattices(sK3,sK4,sK5)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f112])).

fof(f415,plain,
    ( spl7_2
    | ~ spl7_14
    | ~ spl7_38 ),
    inference(avatar_contradiction_clause,[],[f413])).

fof(f413,plain,
    ( $false
    | spl7_2
    | ~ spl7_14
    | ~ spl7_38 ),
    inference(resolution,[],[f410,f382])).

fof(f382,plain,
    ( ~ r3_orders_2(k3_lattice3(sK3),sK4,sK5)
    | spl7_2
    | ~ spl7_14 ),
    inference(forward_demodulation,[],[f381,f200])).

fof(f200,plain,
    ( sK4 = k4_lattice3(sK3,sK4)
    | ~ spl7_14 ),
    inference(resolution,[],[f195,f70])).

% (31584)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f70,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,
    ( ( ~ r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK4),k4_lattice3(sK3,sK5))
      | ~ r3_lattices(sK3,sK4,sK5) )
    & ( r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK4),k4_lattice3(sK3,sK5))
      | r3_lattices(sK3,sK4,sK5) )
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l3_lattices(sK3)
    & v10_lattices(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f54,f57,f56,f55])).

fof(f55,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
                  | ~ r3_lattices(X0,X1,X2) )
                & ( r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
                  | r3_lattices(X0,X1,X2) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,X1),k4_lattice3(sK3,X2))
                | ~ r3_lattices(sK3,X1,X2) )
              & ( r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,X1),k4_lattice3(sK3,X2))
                | r3_lattices(sK3,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(sK3)) )
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l3_lattices(sK3)
      & v10_lattices(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,X1),k4_lattice3(sK3,X2))
              | ~ r3_lattices(sK3,X1,X2) )
            & ( r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,X1),k4_lattice3(sK3,X2))
              | r3_lattices(sK3,X1,X2) )
            & m1_subset_1(X2,u1_struct_0(sK3)) )
        & m1_subset_1(X1,u1_struct_0(sK3)) )
   => ( ? [X2] :
          ( ( ~ r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK4),k4_lattice3(sK3,X2))
            | ~ r3_lattices(sK3,sK4,X2) )
          & ( r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK4),k4_lattice3(sK3,X2))
            | r3_lattices(sK3,sK4,X2) )
          & m1_subset_1(X2,u1_struct_0(sK3)) )
      & m1_subset_1(sK4,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ? [X2] :
        ( ( ~ r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK4),k4_lattice3(sK3,X2))
          | ~ r3_lattices(sK3,sK4,X2) )
        & ( r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK4),k4_lattice3(sK3,X2))
          | r3_lattices(sK3,sK4,X2) )
        & m1_subset_1(X2,u1_struct_0(sK3)) )
   => ( ( ~ r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK4),k4_lattice3(sK3,sK5))
        | ~ r3_lattices(sK3,sK4,sK5) )
      & ( r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK4),k4_lattice3(sK3,sK5))
        | r3_lattices(sK3,sK4,sK5) )
      & m1_subset_1(sK5,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
                | ~ r3_lattices(X0,X1,X2) )
              & ( r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
                | r3_lattices(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
                | ~ r3_lattices(X0,X1,X2) )
              & ( r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
                | r3_lattices(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_lattices(X0,X1,X2)
              <~> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_lattices(X0,X1,X2)
              <~> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r3_lattices(X0,X1,X2)
                <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_lattices(X0,X1,X2)
              <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_lattice3)).

fof(f195,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | k4_lattice3(sK3,X0) = X0 )
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl7_14
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | k4_lattice3(sK3,X0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f381,plain,
    ( ~ r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK4),sK5)
    | spl7_2
    | ~ spl7_14 ),
    inference(forward_demodulation,[],[f118,f201])).

fof(f201,plain,
    ( sK5 = k4_lattice3(sK3,sK5)
    | ~ spl7_14 ),
    inference(resolution,[],[f195,f71])).

fof(f71,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f58])).

fof(f118,plain,
    ( ~ r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK4),k4_lattice3(sK3,sK5))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl7_2
  <=> r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK4),k4_lattice3(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f410,plain,
    ( r3_orders_2(k3_lattice3(sK3),sK4,sK5)
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f408])).

fof(f408,plain,
    ( spl7_38
  <=> r3_orders_2(k3_lattice3(sK3),sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f411,plain,
    ( spl7_18
    | ~ spl7_31
    | ~ spl7_26
    | spl7_38
    | ~ spl7_33
    | ~ spl7_34
    | ~ spl7_16
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f406,f347,f213,f355,f351,f408,f273,f343,f238])).

fof(f238,plain,
    ( spl7_18
  <=> v2_struct_0(k3_lattice3(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f343,plain,
    ( spl7_31
  <=> v3_orders_2(k3_lattice3(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f273,plain,
    ( spl7_26
  <=> l1_orders_2(k3_lattice3(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f213,plain,
    ( spl7_16
  <=> u1_struct_0(sK3) = u1_struct_0(k3_lattice3(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f347,plain,
    ( spl7_32
  <=> r1_orders_2(k3_lattice3(sK3),sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f406,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | r3_orders_2(k3_lattice3(sK3),sK4,sK5)
    | ~ l1_orders_2(k3_lattice3(sK3))
    | ~ v3_orders_2(k3_lattice3(sK3))
    | v2_struct_0(k3_lattice3(sK3))
    | ~ spl7_16
    | ~ spl7_32 ),
    inference(forward_demodulation,[],[f405,f215])).

fof(f215,plain,
    ( u1_struct_0(sK3) = u1_struct_0(k3_lattice3(sK3))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f213])).

fof(f405,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | r3_orders_2(k3_lattice3(sK3),sK4,sK5)
    | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(sK3)))
    | ~ l1_orders_2(k3_lattice3(sK3))
    | ~ v3_orders_2(k3_lattice3(sK3))
    | v2_struct_0(k3_lattice3(sK3))
    | ~ spl7_16
    | ~ spl7_32 ),
    inference(forward_demodulation,[],[f403,f215])).

fof(f403,plain,
    ( r3_orders_2(k3_lattice3(sK3),sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(k3_lattice3(sK3)))
    | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(sK3)))
    | ~ l1_orders_2(k3_lattice3(sK3))
    | ~ v3_orders_2(k3_lattice3(sK3))
    | v2_struct_0(k3_lattice3(sK3))
    | ~ spl7_32 ),
    inference(resolution,[],[f349,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
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
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
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

fof(f349,plain,
    ( r1_orders_2(k3_lattice3(sK3),sK4,sK5)
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f347])).

fof(f402,plain,
    ( ~ spl7_33
    | ~ spl7_34
    | spl7_32
    | ~ spl7_30
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f401,f377,f336,f347,f355,f351])).

fof(f336,plain,
    ( spl7_30
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | r1_orders_2(k3_lattice3(sK3),X0,X1)
        | ~ r2_hidden(k4_tarski(X0,X1),k8_filter_1(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f401,plain,
    ( r1_orders_2(k3_lattice3(sK3),sK4,sK5)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl7_30
    | ~ spl7_35 ),
    inference(resolution,[],[f379,f337])).

fof(f337,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k8_filter_1(sK3))
        | r1_orders_2(k3_lattice3(sK3),X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK3)) )
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f336])).

fof(f379,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),k8_filter_1(sK3))
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f377])).

fof(f400,plain,
    ( ~ spl7_1
    | ~ spl7_34
    | ~ spl7_33
    | spl7_35
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f398,f391,f377,f351,f355,f112])).

fof(f391,plain,
    ( spl7_37
  <=> ! [X1,X0] :
        ( r2_hidden(k4_tarski(X0,X1),k8_filter_1(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r3_lattices(sK3,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f398,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r3_lattices(sK3,sK4,sK5)
    | spl7_35
    | ~ spl7_37 ),
    inference(resolution,[],[f392,f378])).

fof(f378,plain,
    ( ~ r2_hidden(k4_tarski(sK4,sK5),k8_filter_1(sK3))
    | spl7_35 ),
    inference(avatar_component_clause,[],[f377])).

fof(f392,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),k8_filter_1(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ r3_lattices(sK3,X0,X1) )
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f391])).

fof(f395,plain,
    ( ~ spl7_4
    | ~ spl7_11
    | spl7_3
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f394,f254,f124,f171,f128])).

fof(f394,plain,
    ( v2_struct_0(sK3)
    | ~ l3_lattices(sK3)
    | ~ v10_lattices(sK3)
    | ~ spl7_22 ),
    inference(resolution,[],[f255,f183])).

fof(f183,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f182])).

fof(f182,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f121,f101])).

fof(f101,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ( v19_lattices(sK6(X0),X0)
        & v18_lattices(sK6(X0),X0)
        & ~ v1_xboole_0(sK6(X0))
        & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f39,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v19_lattices(X1,X0)
          & v18_lattices(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v19_lattices(sK6(X0),X0)
        & v18_lattices(sK6(X0),X0)
        & ~ v1_xboole_0(sK6(X0))
        & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v19_lattices(X1,X0)
          & v18_lattices(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v19_lattices(X1,X0)
          & v18_lattices(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v19_lattices(X1,X0)
          & v18_lattices(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc14_lattices)).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK6(X0),k1_zfmisc_1(X1))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f102,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f102,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK6(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f255,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f254])).

fof(f393,plain,
    ( spl7_22
    | spl7_37
    | ~ spl7_36 ),
    inference(avatar_split_clause,[],[f389,f385,f391,f254])).

fof(f385,plain,
    ( spl7_36
  <=> ! [X1,X0] :
        ( ~ r3_lattices(sK3,X0,X1)
        | r2_hidden(k1_domain_1(u1_struct_0(sK3),u1_struct_0(sK3),X0,X1),k8_filter_1(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f389,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),k8_filter_1(sK3))
        | ~ r3_lattices(sK3,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | v1_xboole_0(u1_struct_0(sK3)) )
    | ~ spl7_36 ),
    inference(duplicate_literal_removal,[],[f388])).

fof(f388,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),k8_filter_1(sK3))
        | ~ r3_lattices(sK3,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | v1_xboole_0(u1_struct_0(sK3))
        | v1_xboole_0(u1_struct_0(sK3)) )
    | ~ spl7_36 ),
    inference(superposition,[],[f386,f110])).

fof(f386,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k1_domain_1(u1_struct_0(sK3),u1_struct_0(sK3),X0,X1),k8_filter_1(sK3))
        | ~ r3_lattices(sK3,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK3)) )
    | ~ spl7_36 ),
    inference(avatar_component_clause,[],[f385])).

fof(f387,plain,
    ( spl7_3
    | ~ spl7_4
    | spl7_36 ),
    inference(avatar_split_clause,[],[f383,f385,f128,f124])).

fof(f383,plain,(
    ! [X0,X1] :
      ( ~ r3_lattices(sK3,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | r2_hidden(k1_domain_1(u1_struct_0(sK3),u1_struct_0(sK3),X0,X1),k8_filter_1(sK3))
      | ~ v10_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f100,f69])).

fof(f69,plain,(
    l3_lattices(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f380,plain,
    ( ~ spl7_26
    | spl7_35
    | ~ spl7_33
    | ~ spl7_34
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_16
    | ~ spl7_27
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f375,f347,f277,f213,f188,f178,f355,f351,f377,f273])).

fof(f178,plain,
    ( spl7_12
  <=> m1_subset_1(k8_filter_1(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f188,plain,
    ( spl7_13
  <=> k3_lattice3(sK3) = g1_orders_2(u1_struct_0(sK3),k8_filter_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f277,plain,
    ( spl7_27
  <=> k3_lattice3(sK3) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(k3_lattice3(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f375,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | r2_hidden(k4_tarski(sK4,sK5),k8_filter_1(sK3))
    | ~ l1_orders_2(k3_lattice3(sK3))
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_16
    | ~ spl7_27
    | ~ spl7_32 ),
    inference(forward_demodulation,[],[f374,f215])).

fof(f374,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | r2_hidden(k4_tarski(sK4,sK5),k8_filter_1(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(sK3)))
    | ~ l1_orders_2(k3_lattice3(sK3))
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_16
    | ~ spl7_27
    | ~ spl7_32 ),
    inference(forward_demodulation,[],[f373,f215])).

fof(f373,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),k8_filter_1(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(k3_lattice3(sK3)))
    | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(sK3)))
    | ~ l1_orders_2(k3_lattice3(sK3))
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_27
    | ~ spl7_32 ),
    inference(forward_demodulation,[],[f372,f308])).

fof(f308,plain,
    ( k8_filter_1(sK3) = u1_orders_2(k3_lattice3(sK3))
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_27 ),
    inference(trivial_inequality_removal,[],[f306])).

fof(f306,plain,
    ( k3_lattice3(sK3) != k3_lattice3(sK3)
    | k8_filter_1(sK3) = u1_orders_2(k3_lattice3(sK3))
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_27 ),
    inference(superposition,[],[f223,f279])).

fof(f279,plain,
    ( k3_lattice3(sK3) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(k3_lattice3(sK3)))
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f277])).

fof(f223,plain,
    ( ! [X4,X3] :
        ( k3_lattice3(sK3) != g1_orders_2(X3,X4)
        | k8_filter_1(sK3) = X4 )
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(forward_demodulation,[],[f222,f190])).

fof(f190,plain,
    ( k3_lattice3(sK3) = g1_orders_2(u1_struct_0(sK3),k8_filter_1(sK3))
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f188])).

fof(f222,plain,
    ( ! [X4,X3] :
        ( g1_orders_2(u1_struct_0(sK3),k8_filter_1(sK3)) != g1_orders_2(X3,X4)
        | k8_filter_1(sK3) = X4 )
    | ~ spl7_12 ),
    inference(resolution,[],[f106,f180])).

fof(f180,plain,
    ( m1_subset_1(k8_filter_1(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f178])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).

fof(f372,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(k3_lattice3(sK3)))
    | ~ m1_subset_1(sK5,u1_struct_0(k3_lattice3(sK3)))
    | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(sK3)))
    | ~ l1_orders_2(k3_lattice3(sK3))
    | ~ spl7_32 ),
    inference(resolution,[],[f349,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
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
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

fof(f370,plain,
    ( spl7_3
    | ~ spl7_4
    | ~ spl7_11
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f369,f238,f171,f128,f124])).

fof(f369,plain,
    ( ~ l3_lattices(sK3)
    | ~ v10_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ spl7_18 ),
    inference(resolution,[],[f368,f85])).

fof(f85,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f29,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0))
        & ~ v2_struct_0(k3_lattice3(X0)) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f29,plain,(
    ! [X0] :
      ( ( v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0))
        & ~ v2_struct_0(k3_lattice3(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0))
        & ~ v2_struct_0(k3_lattice3(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0))
        & ~ v2_struct_0(k3_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_lattice3)).

fof(f368,plain,
    ( ~ sP0(sK3)
    | ~ spl7_18 ),
    inference(resolution,[],[f240,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k3_lattice3(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ( v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0))
        & ~ v2_struct_0(k3_lattice3(X0)) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f240,plain,
    ( v2_struct_0(k3_lattice3(sK3))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f238])).

fof(f367,plain,(
    spl7_34 ),
    inference(avatar_contradiction_clause,[],[f366])).

fof(f366,plain,
    ( $false
    | spl7_34 ),
    inference(resolution,[],[f357,f70])).

fof(f357,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | spl7_34 ),
    inference(avatar_component_clause,[],[f355])).

fof(f365,plain,(
    spl7_33 ),
    inference(avatar_contradiction_clause,[],[f364])).

fof(f364,plain,
    ( $false
    | spl7_33 ),
    inference(resolution,[],[f353,f71])).

fof(f353,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | spl7_33 ),
    inference(avatar_component_clause,[],[f351])).

fof(f363,plain,
    ( ~ spl7_15
    | spl7_31 ),
    inference(avatar_contradiction_clause,[],[f361])).

fof(f361,plain,
    ( $false
    | ~ spl7_15
    | spl7_31 ),
    inference(resolution,[],[f359,f210])).

fof(f210,plain,
    ( sP1(sK3)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl7_15
  <=> sP1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f359,plain,
    ( ~ sP1(sK3)
    | spl7_31 ),
    inference(resolution,[],[f345,f87])).

fof(f87,plain,(
    ! [X0] :
      ( v3_orders_2(k3_lattice3(X0))
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ( l1_orders_2(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0)) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( l1_orders_2(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0)) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f345,plain,
    ( ~ v3_orders_2(k3_lattice3(sK3))
    | spl7_31 ),
    inference(avatar_component_clause,[],[f343])).

fof(f358,plain,
    ( spl7_18
    | ~ spl7_31
    | ~ spl7_26
    | spl7_32
    | ~ spl7_33
    | ~ spl7_34
    | ~ spl7_2
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f341,f213,f194,f116,f355,f351,f347,f273,f343,f238])).

fof(f341,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | r1_orders_2(k3_lattice3(sK3),sK4,sK5)
    | ~ l1_orders_2(k3_lattice3(sK3))
    | ~ v3_orders_2(k3_lattice3(sK3))
    | v2_struct_0(k3_lattice3(sK3))
    | ~ spl7_2
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(forward_demodulation,[],[f340,f215])).

fof(f340,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | r1_orders_2(k3_lattice3(sK3),sK4,sK5)
    | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(sK3)))
    | ~ l1_orders_2(k3_lattice3(sK3))
    | ~ v3_orders_2(k3_lattice3(sK3))
    | v2_struct_0(k3_lattice3(sK3))
    | ~ spl7_2
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(forward_demodulation,[],[f339,f215])).

fof(f339,plain,
    ( r1_orders_2(k3_lattice3(sK3),sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(k3_lattice3(sK3)))
    | ~ m1_subset_1(sK4,u1_struct_0(k3_lattice3(sK3)))
    | ~ l1_orders_2(k3_lattice3(sK3))
    | ~ v3_orders_2(k3_lattice3(sK3))
    | v2_struct_0(k3_lattice3(sK3))
    | ~ spl7_2
    | ~ spl7_14 ),
    inference(resolution,[],[f108,f203])).

fof(f203,plain,
    ( r3_orders_2(k3_lattice3(sK3),sK4,sK5)
    | ~ spl7_2
    | ~ spl7_14 ),
    inference(backward_demodulation,[],[f202,f201])).

fof(f202,plain,
    ( r3_orders_2(k3_lattice3(sK3),sK4,k4_lattice3(sK3,sK5))
    | ~ spl7_2
    | ~ spl7_14 ),
    inference(backward_demodulation,[],[f117,f200])).

fof(f117,plain,
    ( r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK4),k4_lattice3(sK3,sK5))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f116])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X1,X2)
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f338,plain,
    ( ~ spl7_26
    | spl7_30
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_16
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f334,f277,f213,f188,f178,f336,f273])).

fof(f334,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ r2_hidden(k4_tarski(X0,X1),k8_filter_1(sK3))
        | r1_orders_2(k3_lattice3(sK3),X0,X1)
        | ~ l1_orders_2(k3_lattice3(sK3)) )
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_16
    | ~ spl7_27 ),
    inference(forward_demodulation,[],[f333,f215])).

fof(f333,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ r2_hidden(k4_tarski(X0,X1),k8_filter_1(sK3))
        | r1_orders_2(k3_lattice3(sK3),X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(sK3)))
        | ~ l1_orders_2(k3_lattice3(sK3)) )
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_16
    | ~ spl7_27 ),
    inference(forward_demodulation,[],[f332,f215])).

fof(f332,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),k8_filter_1(sK3))
        | r1_orders_2(k3_lattice3(sK3),X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(sK3)))
        | ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(sK3)))
        | ~ l1_orders_2(k3_lattice3(sK3)) )
    | ~ spl7_12
    | ~ spl7_13
    | ~ spl7_27 ),
    inference(superposition,[],[f76,f308])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f297,plain,
    ( ~ spl7_15
    | spl7_26 ),
    inference(avatar_contradiction_clause,[],[f295])).

fof(f295,plain,
    ( $false
    | ~ spl7_15
    | spl7_26 ),
    inference(resolution,[],[f294,f210])).

fof(f294,plain,
    ( ~ sP1(sK3)
    | spl7_26 ),
    inference(resolution,[],[f275,f90])).

fof(f90,plain,(
    ! [X0] :
      ( l1_orders_2(k3_lattice3(X0))
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f275,plain,
    ( ~ l1_orders_2(k3_lattice3(sK3))
    | spl7_26 ),
    inference(avatar_component_clause,[],[f273])).

fof(f280,plain,
    ( ~ spl7_26
    | ~ spl7_17
    | spl7_27
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f235,f213,f277,f217,f273])).

fof(f217,plain,
    ( spl7_17
  <=> v1_orders_2(k3_lattice3(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f235,plain,
    ( k3_lattice3(sK3) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(k3_lattice3(sK3)))
    | ~ v1_orders_2(k3_lattice3(sK3))
    | ~ l1_orders_2(k3_lattice3(sK3))
    | ~ spl7_16 ),
    inference(superposition,[],[f74,f215])).

fof(f74,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0
      | ~ v1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_orders_2(X0)
       => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).

fof(f230,plain,
    ( ~ spl7_15
    | spl7_17 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | ~ spl7_15
    | spl7_17 ),
    inference(resolution,[],[f226,f210])).

fof(f226,plain,
    ( ~ sP1(sK3)
    | spl7_17 ),
    inference(resolution,[],[f219,f86])).

fof(f86,plain,(
    ! [X0] :
      ( v1_orders_2(k3_lattice3(X0))
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f219,plain,
    ( ~ v1_orders_2(k3_lattice3(sK3))
    | spl7_17 ),
    inference(avatar_component_clause,[],[f217])).

fof(f225,plain,
    ( spl7_3
    | ~ spl7_4
    | ~ spl7_11
    | spl7_15 ),
    inference(avatar_split_clause,[],[f224,f209,f171,f128,f124])).

fof(f224,plain,
    ( ~ l3_lattices(sK3)
    | ~ v10_lattices(sK3)
    | v2_struct_0(sK3)
    | spl7_15 ),
    inference(resolution,[],[f211,f91])).

fof(f91,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f31,f49])).

fof(f31,plain,(
    ! [X0] :
      ( ( l1_orders_2(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( l1_orders_2(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_orders_2(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_lattice3)).

fof(f211,plain,
    ( ~ sP1(sK3)
    | spl7_15 ),
    inference(avatar_component_clause,[],[f209])).

fof(f220,plain,
    ( ~ spl7_15
    | spl7_16
    | ~ spl7_17
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f207,f188,f178,f217,f213,f209])).

fof(f207,plain,
    ( ~ v1_orders_2(k3_lattice3(sK3))
    | u1_struct_0(sK3) = u1_struct_0(k3_lattice3(sK3))
    | ~ sP1(sK3)
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(equality_resolution,[],[f206])).

fof(f206,plain,
    ( ! [X0] :
        ( k3_lattice3(X0) != k3_lattice3(sK3)
        | ~ v1_orders_2(k3_lattice3(X0))
        | u1_struct_0(k3_lattice3(X0)) = u1_struct_0(sK3)
        | ~ sP1(X0) )
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(resolution,[],[f204,f90])).

fof(f204,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(X0)
        | u1_struct_0(X0) = u1_struct_0(sK3)
        | ~ v1_orders_2(X0)
        | k3_lattice3(sK3) != X0 )
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(superposition,[],[f199,f74])).

fof(f199,plain,
    ( ! [X4,X3] :
        ( k3_lattice3(sK3) != g1_orders_2(X3,X4)
        | u1_struct_0(sK3) = X3 )
    | ~ spl7_12
    | ~ spl7_13 ),
    inference(forward_demodulation,[],[f198,f190])).

fof(f198,plain,
    ( ! [X4,X3] :
        ( g1_orders_2(u1_struct_0(sK3),k8_filter_1(sK3)) != g1_orders_2(X3,X4)
        | u1_struct_0(sK3) = X3 )
    | ~ spl7_12 ),
    inference(resolution,[],[f105,f180])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f196,plain,
    ( spl7_3
    | ~ spl7_4
    | spl7_14 ),
    inference(avatar_split_clause,[],[f192,f194,f128,f124])).

fof(f192,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | k4_lattice3(sK3,X0) = X0
      | ~ v10_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f98,f69])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k4_lattice3(X0,X1) = X1
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattice3(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattice3)).

fof(f191,plain,
    ( spl7_3
    | ~ spl7_4
    | spl7_13
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f186,f132,f188,f128,f124])).

fof(f132,plain,
    ( spl7_5
  <=> k8_filter_1(sK3) = k2_lattice3(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f186,plain,
    ( k3_lattice3(sK3) = g1_orders_2(u1_struct_0(sK3),k8_filter_1(sK3))
    | ~ v10_lattices(sK3)
    | v2_struct_0(sK3)
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f185,f134])).

fof(f134,plain,
    ( k8_filter_1(sK3) = k2_lattice3(sK3)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f132])).

fof(f185,plain,
    ( k3_lattice3(sK3) = g1_orders_2(u1_struct_0(sK3),k2_lattice3(sK3))
    | ~ v10_lattices(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f79,f69])).

fof(f79,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | k3_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k2_lattice3(X0))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k3_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k2_lattice3(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k3_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k2_lattice3(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k2_lattice3(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_lattice3)).

fof(f181,plain,
    ( ~ spl7_6
    | spl7_12
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f168,f132,f178,f145])).

fof(f145,plain,
    ( spl7_6
  <=> sP2(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f168,plain,
    ( m1_subset_1(k8_filter_1(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))
    | ~ sP2(sK3)
    | ~ spl7_5 ),
    inference(superposition,[],[f96,f134])).

fof(f96,plain,(
    ! [X0] :
      ( m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ sP2(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ( m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v8_relat_2(k2_lattice3(X0))
        & v4_relat_2(k2_lattice3(X0))
        & v1_relat_2(k2_lattice3(X0))
        & v1_partfun1(k2_lattice3(X0),u1_struct_0(X0)) )
      | ~ sP2(X0) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v8_relat_2(k2_lattice3(X0))
        & v4_relat_2(k2_lattice3(X0))
        & v1_relat_2(k2_lattice3(X0))
        & v1_partfun1(k2_lattice3(X0),u1_struct_0(X0)) )
      | ~ sP2(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f176,plain,(
    spl7_11 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | spl7_11 ),
    inference(resolution,[],[f173,f69])).

fof(f173,plain,
    ( ~ l3_lattices(sK3)
    | spl7_11 ),
    inference(avatar_component_clause,[],[f171])).

fof(f174,plain,
    ( spl7_3
    | ~ spl7_4
    | ~ spl7_11
    | spl7_6 ),
    inference(avatar_split_clause,[],[f169,f145,f171,f128,f124])).

fof(f169,plain,
    ( ~ l3_lattices(sK3)
    | ~ v10_lattices(sK3)
    | v2_struct_0(sK3)
    | spl7_6 ),
    inference(resolution,[],[f147,f97])).

fof(f97,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( sP2(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f33,f51])).

fof(f33,plain,(
    ! [X0] :
      ( ( m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v8_relat_2(k2_lattice3(X0))
        & v4_relat_2(k2_lattice3(X0))
        & v1_relat_2(k2_lattice3(X0))
        & v1_partfun1(k2_lattice3(X0),u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v8_relat_2(k2_lattice3(X0))
        & v4_relat_2(k2_lattice3(X0))
        & v1_relat_2(k2_lattice3(X0))
        & v1_partfun1(k2_lattice3(X0),u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
        & v8_relat_2(k2_lattice3(X0))
        & v4_relat_2(k2_lattice3(X0))
        & v1_relat_2(k2_lattice3(X0))
        & v1_partfun1(k2_lattice3(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_lattice3)).

fof(f147,plain,
    ( ~ sP2(sK3)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f145])).

fof(f139,plain,(
    ~ spl7_3 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | ~ spl7_3 ),
    inference(resolution,[],[f126,f67])).

fof(f67,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f126,plain,
    ( v2_struct_0(sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f124])).

fof(f137,plain,(
    spl7_4 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | spl7_4 ),
    inference(resolution,[],[f130,f68])).

fof(f68,plain,(
    v10_lattices(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f130,plain,
    ( ~ v10_lattices(sK3)
    | spl7_4 ),
    inference(avatar_component_clause,[],[f128])).

fof(f135,plain,
    ( spl7_3
    | ~ spl7_4
    | spl7_5 ),
    inference(avatar_split_clause,[],[f122,f132,f128,f124])).

fof(f122,plain,
    ( k8_filter_1(sK3) = k2_lattice3(sK3)
    | ~ v10_lattices(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f78,f69])).

fof(f78,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | k8_filter_1(X0) = k2_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k8_filter_1(X0) = k2_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k8_filter_1(X0) = k2_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k8_filter_1(X0) = k2_lattice3(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_lattice3)).

fof(f120,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f72,f116,f112])).

fof(f72,plain,
    ( r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK4),k4_lattice3(sK3,sK5))
    | r3_lattices(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f58])).

fof(f119,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f73,f116,f112])).

fof(f73,plain,
    ( ~ r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK4),k4_lattice3(sK3,sK5))
    | ~ r3_lattices(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:46:05 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (31585)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (31585)Refutation not found, incomplete strategy% (31585)------------------------------
% 0.22/0.51  % (31585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (31603)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.52  % (31593)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (31593)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (31585)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (31585)Memory used [KB]: 6396
% 0.22/0.53  % (31585)Time elapsed: 0.097 s
% 0.22/0.53  % (31585)------------------------------
% 0.22/0.53  % (31585)------------------------------
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f428,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f119,f120,f135,f137,f139,f174,f176,f181,f191,f196,f220,f225,f230,f280,f297,f338,f358,f363,f365,f367,f370,f380,f387,f393,f395,f400,f402,f411,f415,f423,f427])).
% 0.22/0.53  fof(f427,plain,(
% 0.22/0.53    spl7_22 | ~spl7_34 | ~spl7_33 | ~spl7_35 | spl7_39),
% 0.22/0.53    inference(avatar_split_clause,[],[f426,f420,f377,f351,f355,f254])).
% 0.22/0.53  fof(f254,plain,(
% 0.22/0.53    spl7_22 <=> v1_xboole_0(u1_struct_0(sK3))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.22/0.53  fof(f355,plain,(
% 0.22/0.53    spl7_34 <=> m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 0.22/0.53  fof(f351,plain,(
% 0.22/0.53    spl7_33 <=> m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 0.22/0.53  fof(f377,plain,(
% 0.22/0.53    spl7_35 <=> r2_hidden(k4_tarski(sK4,sK5),k8_filter_1(sK3))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 0.22/0.53  fof(f420,plain,(
% 0.22/0.53    spl7_39 <=> r2_hidden(k1_domain_1(u1_struct_0(sK3),u1_struct_0(sK3),sK4,sK5),k8_filter_1(sK3))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).
% 0.22/0.53  fof(f426,plain,(
% 0.22/0.53    ~r2_hidden(k4_tarski(sK4,sK5),k8_filter_1(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK3)) | spl7_39),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f425])).
% 0.22/0.53  fof(f425,plain,(
% 0.22/0.53    ~r2_hidden(k4_tarski(sK4,sK5),k8_filter_1(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK3)) | spl7_39),
% 0.22/0.53    inference(superposition,[],[f422,f110])).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3) | ~m1_subset_1(X3,X1) | ~m1_subset_1(X2,X0) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3) | ~m1_subset_1(X3,X1) | ~m1_subset_1(X2,X0) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.22/0.53    inference(flattening,[],[f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ! [X0,X1,X2,X3] : (k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3) | (~m1_subset_1(X3,X1) | ~m1_subset_1(X2,X0) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X1) & m1_subset_1(X2,X0) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_domain_1)).
% 0.22/0.53  fof(f422,plain,(
% 0.22/0.53    ~r2_hidden(k1_domain_1(u1_struct_0(sK3),u1_struct_0(sK3),sK4,sK5),k8_filter_1(sK3)) | spl7_39),
% 0.22/0.53    inference(avatar_component_clause,[],[f420])).
% 0.22/0.53  fof(f423,plain,(
% 0.22/0.53    spl7_3 | ~spl7_4 | ~spl7_11 | ~spl7_34 | ~spl7_33 | ~spl7_39 | spl7_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f418,f112,f420,f351,f355,f171,f128,f124])).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    spl7_3 <=> v2_struct_0(sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.53  fof(f128,plain,(
% 0.22/0.53    spl7_4 <=> v10_lattices(sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.53  fof(f171,plain,(
% 0.22/0.53    spl7_11 <=> l3_lattices(sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    spl7_1 <=> r3_lattices(sK3,sK4,sK5)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.53  fof(f418,plain,(
% 0.22/0.53    ~r2_hidden(k1_domain_1(u1_struct_0(sK3),u1_struct_0(sK3),sK4,sK5),k8_filter_1(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~l3_lattices(sK3) | ~v10_lattices(sK3) | v2_struct_0(sK3) | spl7_1),
% 0.22/0.53    inference(resolution,[],[f114,f99])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,X2) | ~r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f63])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (((r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) | ~r3_lattices(X0,X1,X2)) & (r3_lattices(X0,X1,X2) | ~r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) <=> r3_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) <=> r3_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) <=> r3_lattices(X0,X1,X2)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_filter_1)).
% 0.22/0.53  fof(f114,plain,(
% 0.22/0.53    ~r3_lattices(sK3,sK4,sK5) | spl7_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f112])).
% 0.22/0.53  fof(f415,plain,(
% 0.22/0.53    spl7_2 | ~spl7_14 | ~spl7_38),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f413])).
% 0.22/0.53  fof(f413,plain,(
% 0.22/0.53    $false | (spl7_2 | ~spl7_14 | ~spl7_38)),
% 0.22/0.53    inference(resolution,[],[f410,f382])).
% 0.22/0.53  fof(f382,plain,(
% 0.22/0.53    ~r3_orders_2(k3_lattice3(sK3),sK4,sK5) | (spl7_2 | ~spl7_14)),
% 0.22/0.53    inference(forward_demodulation,[],[f381,f200])).
% 0.22/0.53  fof(f200,plain,(
% 0.22/0.53    sK4 = k4_lattice3(sK3,sK4) | ~spl7_14),
% 0.22/0.53    inference(resolution,[],[f195,f70])).
% 0.22/0.53  % (31584)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.22/0.53    inference(cnf_transformation,[],[f58])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    (((~r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK4),k4_lattice3(sK3,sK5)) | ~r3_lattices(sK3,sK4,sK5)) & (r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK4),k4_lattice3(sK3,sK5)) | r3_lattices(sK3,sK4,sK5)) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK3))) & l3_lattices(sK3) & v10_lattices(sK3) & ~v2_struct_0(sK3)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f54,f57,f56,f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : ((~r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) | ~r3_lattices(X0,X1,X2)) & (r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) | r3_lattices(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,X1),k4_lattice3(sK3,X2)) | ~r3_lattices(sK3,X1,X2)) & (r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,X1),k4_lattice3(sK3,X2)) | r3_lattices(sK3,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(X1,u1_struct_0(sK3))) & l3_lattices(sK3) & v10_lattices(sK3) & ~v2_struct_0(sK3))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ? [X1] : (? [X2] : ((~r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,X1),k4_lattice3(sK3,X2)) | ~r3_lattices(sK3,X1,X2)) & (r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,X1),k4_lattice3(sK3,X2)) | r3_lattices(sK3,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(X1,u1_struct_0(sK3))) => (? [X2] : ((~r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK4),k4_lattice3(sK3,X2)) | ~r3_lattices(sK3,sK4,X2)) & (r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK4),k4_lattice3(sK3,X2)) | r3_lattices(sK3,sK4,X2)) & m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK3)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ? [X2] : ((~r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK4),k4_lattice3(sK3,X2)) | ~r3_lattices(sK3,sK4,X2)) & (r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK4),k4_lattice3(sK3,X2)) | r3_lattices(sK3,sK4,X2)) & m1_subset_1(X2,u1_struct_0(sK3))) => ((~r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK4),k4_lattice3(sK3,sK5)) | ~r3_lattices(sK3,sK4,sK5)) & (r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK4),k4_lattice3(sK3,sK5)) | r3_lattices(sK3,sK4,sK5)) & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : ((~r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) | ~r3_lattices(X0,X1,X2)) & (r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) | r3_lattices(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f53])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (((~r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) | ~r3_lattices(X0,X1,X2)) & (r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) | r3_lattices(X0,X1,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : ((r3_lattices(X0,X1,X2) <~> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : ((r3_lattices(X0,X1,X2) <~> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))))))),
% 0.22/0.53    inference(negated_conjecture,[],[f16])).
% 0.22/0.53  fof(f16,conjecture,(
% 0.22/0.53    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_lattice3)).
% 0.22/0.53  fof(f195,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | k4_lattice3(sK3,X0) = X0) ) | ~spl7_14),
% 0.22/0.53    inference(avatar_component_clause,[],[f194])).
% 0.22/0.53  fof(f194,plain,(
% 0.22/0.53    spl7_14 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | k4_lattice3(sK3,X0) = X0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.22/0.53  fof(f381,plain,(
% 0.22/0.53    ~r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK4),sK5) | (spl7_2 | ~spl7_14)),
% 0.22/0.53    inference(forward_demodulation,[],[f118,f201])).
% 0.22/0.53  fof(f201,plain,(
% 0.22/0.53    sK5 = k4_lattice3(sK3,sK5) | ~spl7_14),
% 0.22/0.53    inference(resolution,[],[f195,f71])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.22/0.53    inference(cnf_transformation,[],[f58])).
% 0.22/0.53  fof(f118,plain,(
% 0.22/0.53    ~r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK4),k4_lattice3(sK3,sK5)) | spl7_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f116])).
% 0.22/0.53  fof(f116,plain,(
% 0.22/0.53    spl7_2 <=> r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK4),k4_lattice3(sK3,sK5))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.53  fof(f410,plain,(
% 0.22/0.53    r3_orders_2(k3_lattice3(sK3),sK4,sK5) | ~spl7_38),
% 0.22/0.53    inference(avatar_component_clause,[],[f408])).
% 0.22/0.53  fof(f408,plain,(
% 0.22/0.53    spl7_38 <=> r3_orders_2(k3_lattice3(sK3),sK4,sK5)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).
% 0.22/0.53  fof(f411,plain,(
% 0.22/0.53    spl7_18 | ~spl7_31 | ~spl7_26 | spl7_38 | ~spl7_33 | ~spl7_34 | ~spl7_16 | ~spl7_32),
% 0.22/0.53    inference(avatar_split_clause,[],[f406,f347,f213,f355,f351,f408,f273,f343,f238])).
% 0.22/0.53  fof(f238,plain,(
% 0.22/0.53    spl7_18 <=> v2_struct_0(k3_lattice3(sK3))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.22/0.53  fof(f343,plain,(
% 0.22/0.53    spl7_31 <=> v3_orders_2(k3_lattice3(sK3))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 0.22/0.53  fof(f273,plain,(
% 0.22/0.53    spl7_26 <=> l1_orders_2(k3_lattice3(sK3))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.22/0.53  fof(f213,plain,(
% 0.22/0.53    spl7_16 <=> u1_struct_0(sK3) = u1_struct_0(k3_lattice3(sK3))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.22/0.53  fof(f347,plain,(
% 0.22/0.53    spl7_32 <=> r1_orders_2(k3_lattice3(sK3),sK4,sK5)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 0.22/0.53  fof(f406,plain,(
% 0.22/0.53    ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | r3_orders_2(k3_lattice3(sK3),sK4,sK5) | ~l1_orders_2(k3_lattice3(sK3)) | ~v3_orders_2(k3_lattice3(sK3)) | v2_struct_0(k3_lattice3(sK3)) | (~spl7_16 | ~spl7_32)),
% 0.22/0.53    inference(forward_demodulation,[],[f405,f215])).
% 0.22/0.53  fof(f215,plain,(
% 0.22/0.53    u1_struct_0(sK3) = u1_struct_0(k3_lattice3(sK3)) | ~spl7_16),
% 0.22/0.53    inference(avatar_component_clause,[],[f213])).
% 0.22/0.53  fof(f405,plain,(
% 0.22/0.53    ~m1_subset_1(sK5,u1_struct_0(sK3)) | r3_orders_2(k3_lattice3(sK3),sK4,sK5) | ~m1_subset_1(sK4,u1_struct_0(k3_lattice3(sK3))) | ~l1_orders_2(k3_lattice3(sK3)) | ~v3_orders_2(k3_lattice3(sK3)) | v2_struct_0(k3_lattice3(sK3)) | (~spl7_16 | ~spl7_32)),
% 0.22/0.53    inference(forward_demodulation,[],[f403,f215])).
% 0.22/0.53  fof(f403,plain,(
% 0.22/0.53    r3_orders_2(k3_lattice3(sK3),sK4,sK5) | ~m1_subset_1(sK5,u1_struct_0(k3_lattice3(sK3))) | ~m1_subset_1(sK4,u1_struct_0(k3_lattice3(sK3))) | ~l1_orders_2(k3_lattice3(sK3)) | ~v3_orders_2(k3_lattice3(sK3)) | v2_struct_0(k3_lattice3(sK3)) | ~spl7_32),
% 0.22/0.53    inference(resolution,[],[f349,f109])).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f66])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.22/0.53  fof(f349,plain,(
% 0.22/0.53    r1_orders_2(k3_lattice3(sK3),sK4,sK5) | ~spl7_32),
% 0.22/0.53    inference(avatar_component_clause,[],[f347])).
% 0.22/0.53  fof(f402,plain,(
% 0.22/0.53    ~spl7_33 | ~spl7_34 | spl7_32 | ~spl7_30 | ~spl7_35),
% 0.22/0.53    inference(avatar_split_clause,[],[f401,f377,f336,f347,f355,f351])).
% 0.22/0.53  fof(f336,plain,(
% 0.22/0.53    spl7_30 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | r1_orders_2(k3_lattice3(sK3),X0,X1) | ~r2_hidden(k4_tarski(X0,X1),k8_filter_1(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK3)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 0.22/0.53  fof(f401,plain,(
% 0.22/0.53    r1_orders_2(k3_lattice3(sK3),sK4,sK5) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | (~spl7_30 | ~spl7_35)),
% 0.22/0.53    inference(resolution,[],[f379,f337])).
% 0.22/0.53  fof(f337,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k8_filter_1(sK3)) | r1_orders_2(k3_lattice3(sK3),X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK3))) ) | ~spl7_30),
% 0.22/0.53    inference(avatar_component_clause,[],[f336])).
% 0.22/0.53  fof(f379,plain,(
% 0.22/0.53    r2_hidden(k4_tarski(sK4,sK5),k8_filter_1(sK3)) | ~spl7_35),
% 0.22/0.53    inference(avatar_component_clause,[],[f377])).
% 0.22/0.53  fof(f400,plain,(
% 0.22/0.53    ~spl7_1 | ~spl7_34 | ~spl7_33 | spl7_35 | ~spl7_37),
% 0.22/0.53    inference(avatar_split_clause,[],[f398,f391,f377,f351,f355,f112])).
% 0.22/0.53  fof(f391,plain,(
% 0.22/0.53    spl7_37 <=> ! [X1,X0] : (r2_hidden(k4_tarski(X0,X1),k8_filter_1(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r3_lattices(sK3,X0,X1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).
% 0.22/0.53  fof(f398,plain,(
% 0.22/0.53    ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~r3_lattices(sK3,sK4,sK5) | (spl7_35 | ~spl7_37)),
% 0.22/0.53    inference(resolution,[],[f392,f378])).
% 0.22/0.53  fof(f378,plain,(
% 0.22/0.53    ~r2_hidden(k4_tarski(sK4,sK5),k8_filter_1(sK3)) | spl7_35),
% 0.22/0.53    inference(avatar_component_clause,[],[f377])).
% 0.22/0.53  fof(f392,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),k8_filter_1(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~r3_lattices(sK3,X0,X1)) ) | ~spl7_37),
% 0.22/0.53    inference(avatar_component_clause,[],[f391])).
% 0.22/0.53  fof(f395,plain,(
% 0.22/0.53    ~spl7_4 | ~spl7_11 | spl7_3 | ~spl7_22),
% 0.22/0.53    inference(avatar_split_clause,[],[f394,f254,f124,f171,f128])).
% 0.22/0.53  fof(f394,plain,(
% 0.22/0.53    v2_struct_0(sK3) | ~l3_lattices(sK3) | ~v10_lattices(sK3) | ~spl7_22),
% 0.22/0.53    inference(resolution,[],[f255,f183])).
% 0.22/0.53  fof(f183,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | v2_struct_0(X0) | ~l3_lattices(X0) | ~v10_lattices(X0)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f182])).
% 0.22/0.53  fof(f182,plain,(
% 0.22/0.53    ( ! [X0] : (~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~v1_xboole_0(u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(resolution,[],[f121,f101])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f65])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ! [X0] : ((v19_lattices(sK6(X0),X0) & v18_lattices(sK6(X0),X0) & ~v1_xboole_0(sK6(X0)) & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f39,f64])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ! [X0] : (? [X1] : (v19_lattices(X1,X0) & v18_lattices(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v19_lattices(sK6(X0),X0) & v18_lattices(sK6(X0),X0) & ~v1_xboole_0(sK6(X0)) & m1_subset_1(sK6(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ! [X0] : (? [X1] : (v19_lattices(X1,X0) & v18_lattices(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ! [X0] : (? [X1] : (v19_lattices(X1,X0) & v18_lattices(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ? [X1] : (v19_lattices(X1,X0) & v18_lattices(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc14_lattices)).
% 0.22/0.53  fof(f121,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(sK6(X0),k1_zfmisc_1(X1)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~v1_xboole_0(X1)) )),
% 0.22/0.53    inference(resolution,[],[f102,f77])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_xboole_0(sK6(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f65])).
% 0.22/0.53  fof(f255,plain,(
% 0.22/0.53    v1_xboole_0(u1_struct_0(sK3)) | ~spl7_22),
% 0.22/0.53    inference(avatar_component_clause,[],[f254])).
% 0.22/0.53  fof(f393,plain,(
% 0.22/0.53    spl7_22 | spl7_37 | ~spl7_36),
% 0.22/0.53    inference(avatar_split_clause,[],[f389,f385,f391,f254])).
% 0.22/0.53  fof(f385,plain,(
% 0.22/0.53    spl7_36 <=> ! [X1,X0] : (~r3_lattices(sK3,X0,X1) | r2_hidden(k1_domain_1(u1_struct_0(sK3),u1_struct_0(sK3),X0,X1),k8_filter_1(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK3)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).
% 0.22/0.53  fof(f389,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),k8_filter_1(sK3)) | ~r3_lattices(sK3,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK3))) ) | ~spl7_36),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f388])).
% 0.22/0.53  fof(f388,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),k8_filter_1(sK3)) | ~r3_lattices(sK3,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK3))) ) | ~spl7_36),
% 0.22/0.53    inference(superposition,[],[f386,f110])).
% 0.22/0.53  fof(f386,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(k1_domain_1(u1_struct_0(sK3),u1_struct_0(sK3),X0,X1),k8_filter_1(sK3)) | ~r3_lattices(sK3,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK3))) ) | ~spl7_36),
% 0.22/0.53    inference(avatar_component_clause,[],[f385])).
% 0.22/0.53  fof(f387,plain,(
% 0.22/0.53    spl7_3 | ~spl7_4 | spl7_36),
% 0.22/0.53    inference(avatar_split_clause,[],[f383,f385,f128,f124])).
% 0.22/0.53  fof(f383,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r3_lattices(sK3,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | r2_hidden(k1_domain_1(u1_struct_0(sK3),u1_struct_0(sK3),X0,X1),k8_filter_1(sK3)) | ~v10_lattices(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.53    inference(resolution,[],[f100,f69])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    l3_lattices(sK3)),
% 0.22/0.53    inference(cnf_transformation,[],[f58])).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~l3_lattices(X0) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_hidden(k1_domain_1(u1_struct_0(X0),u1_struct_0(X0),X1,X2),k8_filter_1(X0)) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f63])).
% 0.22/0.53  fof(f380,plain,(
% 0.22/0.53    ~spl7_26 | spl7_35 | ~spl7_33 | ~spl7_34 | ~spl7_12 | ~spl7_13 | ~spl7_16 | ~spl7_27 | ~spl7_32),
% 0.22/0.53    inference(avatar_split_clause,[],[f375,f347,f277,f213,f188,f178,f355,f351,f377,f273])).
% 0.22/0.53  fof(f178,plain,(
% 0.22/0.53    spl7_12 <=> m1_subset_1(k8_filter_1(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3))))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.22/0.53  fof(f188,plain,(
% 0.22/0.53    spl7_13 <=> k3_lattice3(sK3) = g1_orders_2(u1_struct_0(sK3),k8_filter_1(sK3))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.22/0.53  fof(f277,plain,(
% 0.22/0.53    spl7_27 <=> k3_lattice3(sK3) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(k3_lattice3(sK3)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.22/0.53  fof(f375,plain,(
% 0.22/0.53    ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | r2_hidden(k4_tarski(sK4,sK5),k8_filter_1(sK3)) | ~l1_orders_2(k3_lattice3(sK3)) | (~spl7_12 | ~spl7_13 | ~spl7_16 | ~spl7_27 | ~spl7_32)),
% 0.22/0.53    inference(forward_demodulation,[],[f374,f215])).
% 0.22/0.53  fof(f374,plain,(
% 0.22/0.53    ~m1_subset_1(sK5,u1_struct_0(sK3)) | r2_hidden(k4_tarski(sK4,sK5),k8_filter_1(sK3)) | ~m1_subset_1(sK4,u1_struct_0(k3_lattice3(sK3))) | ~l1_orders_2(k3_lattice3(sK3)) | (~spl7_12 | ~spl7_13 | ~spl7_16 | ~spl7_27 | ~spl7_32)),
% 0.22/0.53    inference(forward_demodulation,[],[f373,f215])).
% 0.22/0.53  fof(f373,plain,(
% 0.22/0.53    r2_hidden(k4_tarski(sK4,sK5),k8_filter_1(sK3)) | ~m1_subset_1(sK5,u1_struct_0(k3_lattice3(sK3))) | ~m1_subset_1(sK4,u1_struct_0(k3_lattice3(sK3))) | ~l1_orders_2(k3_lattice3(sK3)) | (~spl7_12 | ~spl7_13 | ~spl7_27 | ~spl7_32)),
% 0.22/0.53    inference(forward_demodulation,[],[f372,f308])).
% 0.22/0.53  fof(f308,plain,(
% 0.22/0.53    k8_filter_1(sK3) = u1_orders_2(k3_lattice3(sK3)) | (~spl7_12 | ~spl7_13 | ~spl7_27)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f306])).
% 0.22/0.53  fof(f306,plain,(
% 0.22/0.53    k3_lattice3(sK3) != k3_lattice3(sK3) | k8_filter_1(sK3) = u1_orders_2(k3_lattice3(sK3)) | (~spl7_12 | ~spl7_13 | ~spl7_27)),
% 0.22/0.53    inference(superposition,[],[f223,f279])).
% 0.22/0.53  fof(f279,plain,(
% 0.22/0.53    k3_lattice3(sK3) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(k3_lattice3(sK3))) | ~spl7_27),
% 0.22/0.53    inference(avatar_component_clause,[],[f277])).
% 0.22/0.53  fof(f223,plain,(
% 0.22/0.53    ( ! [X4,X3] : (k3_lattice3(sK3) != g1_orders_2(X3,X4) | k8_filter_1(sK3) = X4) ) | (~spl7_12 | ~spl7_13)),
% 0.22/0.53    inference(forward_demodulation,[],[f222,f190])).
% 0.22/0.53  fof(f190,plain,(
% 0.22/0.53    k3_lattice3(sK3) = g1_orders_2(u1_struct_0(sK3),k8_filter_1(sK3)) | ~spl7_13),
% 0.22/0.53    inference(avatar_component_clause,[],[f188])).
% 0.22/0.53  fof(f222,plain,(
% 0.22/0.53    ( ! [X4,X3] : (g1_orders_2(u1_struct_0(sK3),k8_filter_1(sK3)) != g1_orders_2(X3,X4) | k8_filter_1(sK3) = X4) ) | ~spl7_12),
% 0.22/0.53    inference(resolution,[],[f106,f180])).
% 0.22/0.53  fof(f180,plain,(
% 0.22/0.53    m1_subset_1(k8_filter_1(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) | ~spl7_12),
% 0.22/0.53    inference(avatar_component_clause,[],[f178])).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X1 = X3) )),
% 0.22/0.53    inference(cnf_transformation,[],[f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2,X3] : (g1_orders_2(X0,X1) = g1_orders_2(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_orders_2)).
% 0.22/0.53  fof(f372,plain,(
% 0.22/0.53    r2_hidden(k4_tarski(sK4,sK5),u1_orders_2(k3_lattice3(sK3))) | ~m1_subset_1(sK5,u1_struct_0(k3_lattice3(sK3))) | ~m1_subset_1(sK4,u1_struct_0(k3_lattice3(sK3))) | ~l1_orders_2(k3_lattice3(sK3)) | ~spl7_32),
% 0.22/0.53    inference(resolution,[],[f349,f75])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (((r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) & (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).
% 0.22/0.53  fof(f370,plain,(
% 0.22/0.53    spl7_3 | ~spl7_4 | ~spl7_11 | ~spl7_18),
% 0.22/0.53    inference(avatar_split_clause,[],[f369,f238,f171,f128,f124])).
% 0.22/0.53  fof(f369,plain,(
% 0.22/0.53    ~l3_lattices(sK3) | ~v10_lattices(sK3) | v2_struct_0(sK3) | ~spl7_18),
% 0.22/0.53    inference(resolution,[],[f368,f85])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    ( ! [X0] : (sP0(X0) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ! [X0] : (sP0(X0) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(definition_folding,[],[f29,f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ! [X0] : ((v5_orders_2(k3_lattice3(X0)) & v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0)) & ~v2_struct_0(k3_lattice3(X0))) | ~sP0(X0))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0] : ((v5_orders_2(k3_lattice3(X0)) & v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0)) & ~v2_struct_0(k3_lattice3(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0] : ((v5_orders_2(k3_lattice3(X0)) & v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0)) & ~v2_struct_0(k3_lattice3(X0))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,axiom,(
% 0.22/0.53    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (v5_orders_2(k3_lattice3(X0)) & v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0)) & ~v2_struct_0(k3_lattice3(X0))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_lattice3)).
% 0.22/0.53  fof(f368,plain,(
% 0.22/0.53    ~sP0(sK3) | ~spl7_18),
% 0.22/0.53    inference(resolution,[],[f240,f80])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    ( ! [X0] : (~v2_struct_0(k3_lattice3(X0)) | ~sP0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f60])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    ! [X0] : ((v5_orders_2(k3_lattice3(X0)) & v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0)) & ~v2_struct_0(k3_lattice3(X0))) | ~sP0(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f47])).
% 0.22/0.53  fof(f240,plain,(
% 0.22/0.53    v2_struct_0(k3_lattice3(sK3)) | ~spl7_18),
% 0.22/0.53    inference(avatar_component_clause,[],[f238])).
% 0.22/0.53  fof(f367,plain,(
% 0.22/0.53    spl7_34),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f366])).
% 0.22/0.53  fof(f366,plain,(
% 0.22/0.53    $false | spl7_34),
% 0.22/0.53    inference(resolution,[],[f357,f70])).
% 0.22/0.53  fof(f357,plain,(
% 0.22/0.53    ~m1_subset_1(sK4,u1_struct_0(sK3)) | spl7_34),
% 0.22/0.53    inference(avatar_component_clause,[],[f355])).
% 0.22/0.53  fof(f365,plain,(
% 0.22/0.53    spl7_33),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f364])).
% 0.22/0.53  fof(f364,plain,(
% 0.22/0.53    $false | spl7_33),
% 0.22/0.53    inference(resolution,[],[f353,f71])).
% 0.22/0.53  fof(f353,plain,(
% 0.22/0.53    ~m1_subset_1(sK5,u1_struct_0(sK3)) | spl7_33),
% 0.22/0.53    inference(avatar_component_clause,[],[f351])).
% 0.22/0.53  fof(f363,plain,(
% 0.22/0.53    ~spl7_15 | spl7_31),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f361])).
% 0.22/0.53  fof(f361,plain,(
% 0.22/0.53    $false | (~spl7_15 | spl7_31)),
% 0.22/0.53    inference(resolution,[],[f359,f210])).
% 0.22/0.53  fof(f210,plain,(
% 0.22/0.53    sP1(sK3) | ~spl7_15),
% 0.22/0.53    inference(avatar_component_clause,[],[f209])).
% 0.22/0.53  fof(f209,plain,(
% 0.22/0.53    spl7_15 <=> sP1(sK3)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.22/0.53  fof(f359,plain,(
% 0.22/0.53    ~sP1(sK3) | spl7_31),
% 0.22/0.53    inference(resolution,[],[f345,f87])).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    ( ! [X0] : (v3_orders_2(k3_lattice3(X0)) | ~sP1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f61])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ! [X0] : ((l1_orders_2(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0)) & v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0))) | ~sP1(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ! [X0] : ((l1_orders_2(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0)) & v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0))) | ~sP1(X0))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.53  fof(f345,plain,(
% 0.22/0.53    ~v3_orders_2(k3_lattice3(sK3)) | spl7_31),
% 0.22/0.53    inference(avatar_component_clause,[],[f343])).
% 0.22/0.53  fof(f358,plain,(
% 0.22/0.53    spl7_18 | ~spl7_31 | ~spl7_26 | spl7_32 | ~spl7_33 | ~spl7_34 | ~spl7_2 | ~spl7_14 | ~spl7_16),
% 0.22/0.53    inference(avatar_split_clause,[],[f341,f213,f194,f116,f355,f351,f347,f273,f343,f238])).
% 0.22/0.53  fof(f341,plain,(
% 0.22/0.53    ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | r1_orders_2(k3_lattice3(sK3),sK4,sK5) | ~l1_orders_2(k3_lattice3(sK3)) | ~v3_orders_2(k3_lattice3(sK3)) | v2_struct_0(k3_lattice3(sK3)) | (~spl7_2 | ~spl7_14 | ~spl7_16)),
% 0.22/0.53    inference(forward_demodulation,[],[f340,f215])).
% 0.22/0.53  fof(f340,plain,(
% 0.22/0.53    ~m1_subset_1(sK5,u1_struct_0(sK3)) | r1_orders_2(k3_lattice3(sK3),sK4,sK5) | ~m1_subset_1(sK4,u1_struct_0(k3_lattice3(sK3))) | ~l1_orders_2(k3_lattice3(sK3)) | ~v3_orders_2(k3_lattice3(sK3)) | v2_struct_0(k3_lattice3(sK3)) | (~spl7_2 | ~spl7_14 | ~spl7_16)),
% 0.22/0.53    inference(forward_demodulation,[],[f339,f215])).
% 0.22/0.53  fof(f339,plain,(
% 0.22/0.53    r1_orders_2(k3_lattice3(sK3),sK4,sK5) | ~m1_subset_1(sK5,u1_struct_0(k3_lattice3(sK3))) | ~m1_subset_1(sK4,u1_struct_0(k3_lattice3(sK3))) | ~l1_orders_2(k3_lattice3(sK3)) | ~v3_orders_2(k3_lattice3(sK3)) | v2_struct_0(k3_lattice3(sK3)) | (~spl7_2 | ~spl7_14)),
% 0.22/0.53    inference(resolution,[],[f108,f203])).
% 0.22/0.53  fof(f203,plain,(
% 0.22/0.53    r3_orders_2(k3_lattice3(sK3),sK4,sK5) | (~spl7_2 | ~spl7_14)),
% 0.22/0.53    inference(backward_demodulation,[],[f202,f201])).
% 0.22/0.53  fof(f202,plain,(
% 0.22/0.53    r3_orders_2(k3_lattice3(sK3),sK4,k4_lattice3(sK3,sK5)) | (~spl7_2 | ~spl7_14)),
% 0.22/0.53    inference(backward_demodulation,[],[f117,f200])).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK4),k4_lattice3(sK3,sK5)) | ~spl7_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f116])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r3_orders_2(X0,X1,X2) | r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f66])).
% 0.22/0.53  fof(f338,plain,(
% 0.22/0.53    ~spl7_26 | spl7_30 | ~spl7_12 | ~spl7_13 | ~spl7_16 | ~spl7_27),
% 0.22/0.53    inference(avatar_split_clause,[],[f334,f277,f213,f188,f178,f336,f273])).
% 0.22/0.53  fof(f334,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~r2_hidden(k4_tarski(X0,X1),k8_filter_1(sK3)) | r1_orders_2(k3_lattice3(sK3),X0,X1) | ~l1_orders_2(k3_lattice3(sK3))) ) | (~spl7_12 | ~spl7_13 | ~spl7_16 | ~spl7_27)),
% 0.22/0.53    inference(forward_demodulation,[],[f333,f215])).
% 0.22/0.53  fof(f333,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK3)) | ~r2_hidden(k4_tarski(X0,X1),k8_filter_1(sK3)) | r1_orders_2(k3_lattice3(sK3),X0,X1) | ~m1_subset_1(X0,u1_struct_0(k3_lattice3(sK3))) | ~l1_orders_2(k3_lattice3(sK3))) ) | (~spl7_12 | ~spl7_13 | ~spl7_16 | ~spl7_27)),
% 0.22/0.53    inference(forward_demodulation,[],[f332,f215])).
% 0.22/0.54  fof(f332,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k8_filter_1(sK3)) | r1_orders_2(k3_lattice3(sK3),X0,X1) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(sK3))) | ~m1_subset_1(X0,u1_struct_0(k3_lattice3(sK3))) | ~l1_orders_2(k3_lattice3(sK3))) ) | (~spl7_12 | ~spl7_13 | ~spl7_27)),
% 0.22/0.54    inference(superposition,[],[f76,f308])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f59])).
% 0.22/0.54  fof(f297,plain,(
% 0.22/0.54    ~spl7_15 | spl7_26),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f295])).
% 0.22/0.54  fof(f295,plain,(
% 0.22/0.54    $false | (~spl7_15 | spl7_26)),
% 0.22/0.54    inference(resolution,[],[f294,f210])).
% 0.22/0.54  fof(f294,plain,(
% 0.22/0.54    ~sP1(sK3) | spl7_26),
% 0.22/0.54    inference(resolution,[],[f275,f90])).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    ( ! [X0] : (l1_orders_2(k3_lattice3(X0)) | ~sP1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f61])).
% 0.22/0.54  fof(f275,plain,(
% 0.22/0.54    ~l1_orders_2(k3_lattice3(sK3)) | spl7_26),
% 0.22/0.54    inference(avatar_component_clause,[],[f273])).
% 0.22/0.54  fof(f280,plain,(
% 0.22/0.54    ~spl7_26 | ~spl7_17 | spl7_27 | ~spl7_16),
% 0.22/0.54    inference(avatar_split_clause,[],[f235,f213,f277,f217,f273])).
% 0.22/0.54  fof(f217,plain,(
% 0.22/0.54    spl7_17 <=> v1_orders_2(k3_lattice3(sK3))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.22/0.54  fof(f235,plain,(
% 0.22/0.54    k3_lattice3(sK3) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(k3_lattice3(sK3))) | ~v1_orders_2(k3_lattice3(sK3)) | ~l1_orders_2(k3_lattice3(sK3)) | ~spl7_16),
% 0.22/0.54    inference(superposition,[],[f74,f215])).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    ( ! [X0] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0) | ~l1_orders_2(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0] : (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(flattening,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0] : ((g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0 | ~v1_orders_2(X0)) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0] : (l1_orders_2(X0) => (v1_orders_2(X0) => g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_orders_2)).
% 0.22/0.54  fof(f230,plain,(
% 0.22/0.54    ~spl7_15 | spl7_17),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f228])).
% 0.22/0.54  fof(f228,plain,(
% 0.22/0.54    $false | (~spl7_15 | spl7_17)),
% 0.22/0.54    inference(resolution,[],[f226,f210])).
% 0.22/0.54  fof(f226,plain,(
% 0.22/0.54    ~sP1(sK3) | spl7_17),
% 0.22/0.54    inference(resolution,[],[f219,f86])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    ( ! [X0] : (v1_orders_2(k3_lattice3(X0)) | ~sP1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f61])).
% 0.22/0.54  fof(f219,plain,(
% 0.22/0.54    ~v1_orders_2(k3_lattice3(sK3)) | spl7_17),
% 0.22/0.54    inference(avatar_component_clause,[],[f217])).
% 0.22/0.54  fof(f225,plain,(
% 0.22/0.54    spl7_3 | ~spl7_4 | ~spl7_11 | spl7_15),
% 0.22/0.54    inference(avatar_split_clause,[],[f224,f209,f171,f128,f124])).
% 0.22/0.54  fof(f224,plain,(
% 0.22/0.54    ~l3_lattices(sK3) | ~v10_lattices(sK3) | v2_struct_0(sK3) | spl7_15),
% 0.22/0.54    inference(resolution,[],[f211,f91])).
% 0.22/0.54  fof(f91,plain,(
% 0.22/0.54    ( ! [X0] : (sP1(X0) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ! [X0] : (sP1(X0) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(definition_folding,[],[f31,f49])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0] : ((l1_orders_2(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0)) & v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0] : ((l1_orders_2(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0)) & v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (l1_orders_2(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0)) & v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_lattice3)).
% 0.22/0.54  fof(f211,plain,(
% 0.22/0.54    ~sP1(sK3) | spl7_15),
% 0.22/0.54    inference(avatar_component_clause,[],[f209])).
% 0.22/0.54  fof(f220,plain,(
% 0.22/0.54    ~spl7_15 | spl7_16 | ~spl7_17 | ~spl7_12 | ~spl7_13),
% 0.22/0.54    inference(avatar_split_clause,[],[f207,f188,f178,f217,f213,f209])).
% 0.22/0.54  fof(f207,plain,(
% 0.22/0.54    ~v1_orders_2(k3_lattice3(sK3)) | u1_struct_0(sK3) = u1_struct_0(k3_lattice3(sK3)) | ~sP1(sK3) | (~spl7_12 | ~spl7_13)),
% 0.22/0.54    inference(equality_resolution,[],[f206])).
% 0.22/0.54  fof(f206,plain,(
% 0.22/0.54    ( ! [X0] : (k3_lattice3(X0) != k3_lattice3(sK3) | ~v1_orders_2(k3_lattice3(X0)) | u1_struct_0(k3_lattice3(X0)) = u1_struct_0(sK3) | ~sP1(X0)) ) | (~spl7_12 | ~spl7_13)),
% 0.22/0.54    inference(resolution,[],[f204,f90])).
% 0.22/0.54  fof(f204,plain,(
% 0.22/0.54    ( ! [X0] : (~l1_orders_2(X0) | u1_struct_0(X0) = u1_struct_0(sK3) | ~v1_orders_2(X0) | k3_lattice3(sK3) != X0) ) | (~spl7_12 | ~spl7_13)),
% 0.22/0.54    inference(superposition,[],[f199,f74])).
% 0.22/0.54  fof(f199,plain,(
% 0.22/0.54    ( ! [X4,X3] : (k3_lattice3(sK3) != g1_orders_2(X3,X4) | u1_struct_0(sK3) = X3) ) | (~spl7_12 | ~spl7_13)),
% 0.22/0.54    inference(forward_demodulation,[],[f198,f190])).
% 0.22/0.54  fof(f198,plain,(
% 0.22/0.54    ( ! [X4,X3] : (g1_orders_2(u1_struct_0(sK3),k8_filter_1(sK3)) != g1_orders_2(X3,X4) | u1_struct_0(sK3) = X3) ) | ~spl7_12),
% 0.22/0.54    inference(resolution,[],[f105,f180])).
% 0.22/0.54  fof(f105,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | X0 = X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f40])).
% 0.22/0.54  fof(f196,plain,(
% 0.22/0.54    spl7_3 | ~spl7_4 | spl7_14),
% 0.22/0.54    inference(avatar_split_clause,[],[f192,f194,f128,f124])).
% 0.22/0.54  fof(f192,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3)) | k4_lattice3(sK3,X0) = X0 | ~v10_lattices(sK3) | v2_struct_0(sK3)) )),
% 0.22/0.54    inference(resolution,[],[f98,f69])).
% 0.22/0.54  fof(f98,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | k4_lattice3(X0,X1) = X1 | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (k4_lattice3(X0,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (k4_lattice3(X0,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k4_lattice3(X0,X1) = X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattice3)).
% 0.22/0.54  fof(f191,plain,(
% 0.22/0.54    spl7_3 | ~spl7_4 | spl7_13 | ~spl7_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f186,f132,f188,f128,f124])).
% 0.22/0.54  fof(f132,plain,(
% 0.22/0.54    spl7_5 <=> k8_filter_1(sK3) = k2_lattice3(sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.54  fof(f186,plain,(
% 0.22/0.54    k3_lattice3(sK3) = g1_orders_2(u1_struct_0(sK3),k8_filter_1(sK3)) | ~v10_lattices(sK3) | v2_struct_0(sK3) | ~spl7_5),
% 0.22/0.54    inference(forward_demodulation,[],[f185,f134])).
% 0.22/0.54  fof(f134,plain,(
% 0.22/0.54    k8_filter_1(sK3) = k2_lattice3(sK3) | ~spl7_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f132])).
% 0.22/0.54  fof(f185,plain,(
% 0.22/0.54    k3_lattice3(sK3) = g1_orders_2(u1_struct_0(sK3),k2_lattice3(sK3)) | ~v10_lattices(sK3) | v2_struct_0(sK3)),
% 0.22/0.54    inference(resolution,[],[f79,f69])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    ( ! [X0] : (~l3_lattices(X0) | k3_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k2_lattice3(X0)) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0] : (k3_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k2_lattice3(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0] : (k3_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k2_lattice3(X0)) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => k3_lattice3(X0) = g1_orders_2(u1_struct_0(X0),k2_lattice3(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_lattice3)).
% 0.22/0.54  fof(f181,plain,(
% 0.22/0.54    ~spl7_6 | spl7_12 | ~spl7_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f168,f132,f178,f145])).
% 0.22/0.54  fof(f145,plain,(
% 0.22/0.54    spl7_6 <=> sP2(sK3)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.54  fof(f168,plain,(
% 0.22/0.54    m1_subset_1(k8_filter_1(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK3),u1_struct_0(sK3)))) | ~sP2(sK3) | ~spl7_5),
% 0.22/0.54    inference(superposition,[],[f96,f134])).
% 0.22/0.54  fof(f96,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~sP2(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f62])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    ! [X0] : ((m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v8_relat_2(k2_lattice3(X0)) & v4_relat_2(k2_lattice3(X0)) & v1_relat_2(k2_lattice3(X0)) & v1_partfun1(k2_lattice3(X0),u1_struct_0(X0))) | ~sP2(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ! [X0] : ((m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v8_relat_2(k2_lattice3(X0)) & v4_relat_2(k2_lattice3(X0)) & v1_relat_2(k2_lattice3(X0)) & v1_partfun1(k2_lattice3(X0),u1_struct_0(X0))) | ~sP2(X0))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.54  fof(f176,plain,(
% 0.22/0.54    spl7_11),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f175])).
% 0.22/0.54  fof(f175,plain,(
% 0.22/0.54    $false | spl7_11),
% 0.22/0.54    inference(resolution,[],[f173,f69])).
% 0.22/0.54  fof(f173,plain,(
% 0.22/0.54    ~l3_lattices(sK3) | spl7_11),
% 0.22/0.54    inference(avatar_component_clause,[],[f171])).
% 0.22/0.54  fof(f174,plain,(
% 0.22/0.54    spl7_3 | ~spl7_4 | ~spl7_11 | spl7_6),
% 0.22/0.54    inference(avatar_split_clause,[],[f169,f145,f171,f128,f124])).
% 0.22/0.54  fof(f169,plain,(
% 0.22/0.54    ~l3_lattices(sK3) | ~v10_lattices(sK3) | v2_struct_0(sK3) | spl7_6),
% 0.22/0.54    inference(resolution,[],[f147,f97])).
% 0.22/0.54  fof(f97,plain,(
% 0.22/0.54    ( ! [X0] : (sP2(X0) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f52])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ! [X0] : (sP2(X0) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(definition_folding,[],[f33,f51])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0] : ((m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v8_relat_2(k2_lattice3(X0)) & v4_relat_2(k2_lattice3(X0)) & v1_relat_2(k2_lattice3(X0)) & v1_partfun1(k2_lattice3(X0),u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X0] : ((m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v8_relat_2(k2_lattice3(X0)) & v4_relat_2(k2_lattice3(X0)) & v1_relat_2(k2_lattice3(X0)) & v1_partfun1(k2_lattice3(X0),u1_struct_0(X0))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k2_lattice3(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) & v8_relat_2(k2_lattice3(X0)) & v4_relat_2(k2_lattice3(X0)) & v1_relat_2(k2_lattice3(X0)) & v1_partfun1(k2_lattice3(X0),u1_struct_0(X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_lattice3)).
% 0.22/0.54  fof(f147,plain,(
% 0.22/0.54    ~sP2(sK3) | spl7_6),
% 0.22/0.54    inference(avatar_component_clause,[],[f145])).
% 0.22/0.54  fof(f139,plain,(
% 0.22/0.54    ~spl7_3),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f138])).
% 0.22/0.54  fof(f138,plain,(
% 0.22/0.54    $false | ~spl7_3),
% 0.22/0.54    inference(resolution,[],[f126,f67])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    ~v2_struct_0(sK3)),
% 0.22/0.54    inference(cnf_transformation,[],[f58])).
% 0.22/0.54  fof(f126,plain,(
% 0.22/0.54    v2_struct_0(sK3) | ~spl7_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f124])).
% 0.22/0.54  fof(f137,plain,(
% 0.22/0.54    spl7_4),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f136])).
% 0.22/0.54  fof(f136,plain,(
% 0.22/0.54    $false | spl7_4),
% 0.22/0.54    inference(resolution,[],[f130,f68])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    v10_lattices(sK3)),
% 0.22/0.54    inference(cnf_transformation,[],[f58])).
% 0.22/0.54  fof(f130,plain,(
% 0.22/0.54    ~v10_lattices(sK3) | spl7_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f128])).
% 0.22/0.54  fof(f135,plain,(
% 0.22/0.54    spl7_3 | ~spl7_4 | spl7_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f122,f132,f128,f124])).
% 0.22/0.54  fof(f122,plain,(
% 0.22/0.54    k8_filter_1(sK3) = k2_lattice3(sK3) | ~v10_lattices(sK3) | v2_struct_0(sK3)),
% 0.22/0.54    inference(resolution,[],[f78,f69])).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    ( ! [X0] : (~l3_lattices(X0) | k8_filter_1(X0) = k2_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0] : (k8_filter_1(X0) = k2_lattice3(X0) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0] : (k8_filter_1(X0) = k2_lattice3(X0) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,axiom,(
% 0.22/0.54    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => k8_filter_1(X0) = k2_lattice3(X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_lattice3)).
% 0.22/0.54  fof(f120,plain,(
% 0.22/0.54    spl7_1 | spl7_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f72,f116,f112])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK4),k4_lattice3(sK3,sK5)) | r3_lattices(sK3,sK4,sK5)),
% 0.22/0.54    inference(cnf_transformation,[],[f58])).
% 0.22/0.54  fof(f119,plain,(
% 0.22/0.54    ~spl7_1 | ~spl7_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f73,f116,f112])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    ~r3_orders_2(k3_lattice3(sK3),k4_lattice3(sK3,sK4),k4_lattice3(sK3,sK5)) | ~r3_lattices(sK3,sK4,sK5)),
% 0.22/0.54    inference(cnf_transformation,[],[f58])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (31593)------------------------------
% 0.22/0.54  % (31593)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (31593)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (31593)Memory used [KB]: 6396
% 0.22/0.54  % (31593)Time elapsed: 0.118 s
% 0.22/0.54  % (31593)------------------------------
% 0.22/0.54  % (31593)------------------------------
% 0.22/0.54  % (31581)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (31580)Success in time 0.17 s
%------------------------------------------------------------------------------
