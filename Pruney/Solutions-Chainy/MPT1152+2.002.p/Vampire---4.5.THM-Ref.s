%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 202 expanded)
%              Number of leaves         :   23 (  55 expanded)
%              Depth                    :   24
%              Number of atoms          :  567 (1047 expanded)
%              Number of equality atoms :   73 ( 148 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f359,plain,(
    $false ),
    inference(subsumption_resolution,[],[f358,f62])).

fof(f62,plain,(
    l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( k1_xboole_0 != k2_orders_2(sK5,k2_struct_0(sK5))
    & l1_orders_2(sK5)
    & v5_orders_2(sK5)
    & v4_orders_2(sK5)
    & v3_orders_2(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f18,f39])).

fof(f39,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( k1_xboole_0 != k2_orders_2(sK5,k2_struct_0(sK5))
      & l1_orders_2(sK5)
      & v5_orders_2(sK5)
      & v4_orders_2(sK5)
      & v3_orders_2(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_orders_2)).

fof(f358,plain,(
    ~ l1_orders_2(sK5) ),
    inference(subsumption_resolution,[],[f357,f58])).

fof(f58,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f357,plain,
    ( v2_struct_0(sK5)
    | ~ l1_orders_2(sK5) ),
    inference(subsumption_resolution,[],[f356,f59])).

fof(f59,plain,(
    v3_orders_2(sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f356,plain,
    ( ~ v3_orders_2(sK5)
    | v2_struct_0(sK5)
    | ~ l1_orders_2(sK5) ),
    inference(subsumption_resolution,[],[f355,f60])).

fof(f60,plain,(
    v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f355,plain,
    ( ~ v4_orders_2(sK5)
    | ~ v3_orders_2(sK5)
    | v2_struct_0(sK5)
    | ~ l1_orders_2(sK5) ),
    inference(subsumption_resolution,[],[f354,f61])).

fof(f61,plain,(
    v5_orders_2(sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f354,plain,
    ( ~ v5_orders_2(sK5)
    | ~ v4_orders_2(sK5)
    | ~ v3_orders_2(sK5)
    | v2_struct_0(sK5)
    | ~ l1_orders_2(sK5) ),
    inference(trivial_inequality_removal,[],[f349])).

fof(f349,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v5_orders_2(sK5)
    | ~ v4_orders_2(sK5)
    | ~ v3_orders_2(sK5)
    | v2_struct_0(sK5)
    | ~ l1_orders_2(sK5) ),
    inference(superposition,[],[f63,f340])).

fof(f340,plain,(
    ! [X2] :
      ( k1_xboole_0 = k2_orders_2(X2,k2_struct_0(X2))
      | ~ v5_orders_2(X2)
      | ~ v4_orders_2(X2)
      | ~ v3_orders_2(X2)
      | v2_struct_0(X2)
      | ~ l1_orders_2(X2) ) ),
    inference(resolution,[],[f320,f78])).

fof(f78,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f27,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f320,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k2_orders_2(X0,k2_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f288,f319])).

fof(f319,plain,(
    ! [X0,X1] :
      ( ~ sP3(k2_struct_0(X0),X0,X1)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f318,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f318,plain,(
    ! [X0,X1] :
      ( ~ sP3(k2_struct_0(X0),X0,X1)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(superposition,[],[f314,f68])).

fof(f68,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f314,plain,(
    ! [X0,X1] :
      ( ~ sP3(u1_struct_0(X0),X0,X1)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f310])).

fof(f310,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ sP3(u1_struct_0(X0),X0,X1)
      | ~ sP3(u1_struct_0(X0),X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f225,f154])).

fof(f154,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(sK7(X4,X5,X6),X4)
      | ~ sP3(X4,X5,X6)
      | ~ l1_orders_2(X5) ) ),
    inference(subsumption_resolution,[],[f152,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ! [X3] :
            ( ~ sP2(X3,X1,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ( sP2(sK7(X0,X1,X2),X1,X0)
          & sK7(X0,X1,X2) = X2
          & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f51,f52])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( sP2(X4,X1,X0)
          & X2 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( sP2(sK7(X0,X1,X2),X1,X0)
        & sK7(X0,X1,X2) = X2
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ! [X3] :
            ( ~ sP2(X3,X1,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( sP2(X4,X1,X0)
            & X2 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ( sP3(X2,X1,X0)
        | ! [X3] :
            ( ~ sP2(X3,X1,X2)
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( sP2(X3,X1,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP3(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( sP3(X2,X1,X0)
    <=> ? [X3] :
          ( sP2(X3,X1,X2)
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f152,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(sK7(X4,X5,X6),u1_struct_0(X5))
      | ~ r2_hidden(sK7(X4,X5,X6),X4)
      | ~ sP3(X4,X5,X6)
      | ~ l1_orders_2(X5) ) ),
    inference(duplicate_literal_removal,[],[f149])).

fof(f149,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(sK7(X4,X5,X6),u1_struct_0(X5))
      | ~ r2_hidden(sK7(X4,X5,X6),X4)
      | ~ sP3(X4,X5,X6)
      | ~ l1_orders_2(X5)
      | ~ m1_subset_1(sK7(X4,X5,X6),u1_struct_0(X5)) ) ),
    inference(resolution,[],[f136,f147])).

% (12580)Refutation not found, incomplete strategy% (12580)------------------------------
% (12580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f147,plain,(
    ! [X0,X1] :
      ( ~ r2_orders_2(X1,X0,X0)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f143])).

% (12580)Termination reason: Refutation not found, incomplete strategy

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ r2_orders_2(X1,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f131,f95])).

% (12580)Memory used [KB]: 10490
% (12580)Time elapsed: 0.104 s
% (12580)------------------------------
% (12580)------------------------------
fof(f95,plain,(
    ! [X2,X1] : ~ sP0(X1,X1,X2) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( X0 != X1
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | X0 = X1
        | ~ r1_orders_2(X2,X1,X0) )
      & ( ( X0 != X1
          & r1_orders_2(X2,X1,X0) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ( sP0(X2,X1,X0)
        | X1 = X2
        | ~ r1_orders_2(X0,X1,X2) )
      & ( ( X1 != X2
          & r1_orders_2(X0,X1,X2) )
        | ~ sP0(X2,X1,X0) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ( sP0(X2,X1,X0)
        | X1 = X2
        | ~ r1_orders_2(X0,X1,X2) )
      & ( ( X1 != X2
          & r1_orders_2(X0,X1,X2) )
        | ~ sP0(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( sP0(X2,X1,X0)
    <=> ( X1 != X2
        & r1_orders_2(X0,X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f131,plain,(
    ! [X4,X5,X3] :
      ( sP0(X3,X5,X4)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ r2_orders_2(X4,X5,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X4)) ) ),
    inference(resolution,[],[f75,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_orders_2(X0,X1,X2)
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_orders_2(X0,X1,X2)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_orders_2(X0,X1,X2) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r2_orders_2(X0,X1,X2)
      <=> sP0(X2,X1,X0) )
      | ~ sP1(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f22,f33,f32])).

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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

fof(f136,plain,(
    ! [X6,X4,X5,X3] :
      ( r2_orders_2(X5,sK7(X4,X5,X6),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X5))
      | ~ r2_hidden(X3,X4)
      | ~ sP3(X4,X5,X6) ) ),
    inference(resolution,[],[f89,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( sP2(sK7(X0,X1,X2),X1,X0)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f89,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r2_orders_2(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ~ r2_orders_2(X1,X0,sK8(X0,X1,X2))
          & r2_hidden(sK8(X0,X1,X2),X2)
          & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r2_orders_2(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f55,f56])).

% (12581)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f56,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_orders_2(X1,X0,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X0,sK8(X0,X1,X2))
        & r2_hidden(sK8(X0,X1,X2),X2)
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ~ r2_orders_2(X1,X0,X3)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r2_orders_2(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X3,X1,X2] :
      ( ( sP2(X3,X1,X2)
        | ? [X4] :
            ( ~ r2_orders_2(X1,X3,X4)
            & r2_hidden(X4,X2)
            & m1_subset_1(X4,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r2_orders_2(X1,X3,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP2(X3,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X3,X1,X2] :
      ( sP2(X3,X1,X2)
    <=> ! [X4] :
          ( r2_orders_2(X1,X3,X4)
          | ~ r2_hidden(X4,X2)
          | ~ m1_subset_1(X4,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f225,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X1,X0,X2),u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ sP3(X1,X0,X2) ) ),
    inference(resolution,[],[f224,f85])).

fof(f224,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | r2_hidden(X0,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f223,f104])).

fof(f104,plain,(
    ! [X0,X1] : sP2(X0,X1,k1_xboole_0) ),
    inference(resolution,[],[f91,f101])).

fof(f101,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f79,f96])).

fof(f96,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f79,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X2),X2)
      | sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f223,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | ~ sP2(X0,X1,k1_xboole_0)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f222,f98])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( sP3(X0,X1,X3)
      | ~ sP2(X3,X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,X2)
      | ~ sP2(X3,X1,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f222,plain,(
    ! [X0,X1] :
      ( ~ sP3(k1_xboole_0,X0,X1)
      | r2_hidden(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f221])).

fof(f221,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,u1_struct_0(X0))
      | ~ sP3(k1_xboole_0,X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f210,f140])).

fof(f140,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_orders_2(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f139,f69])).

fof(f139,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_orders_2(X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(superposition,[],[f76,f67])).

fof(f67,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).

fof(f76,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_orders_2)).

fof(f210,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k2_orders_2(X0,k1_xboole_0))
      | ~ sP3(k1_xboole_0,X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f172,f65])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f172,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP3(X1,X0,X2)
      | r2_hidden(X2,k2_orders_2(X0,X1))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f170,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | sP4(X0,X1,X2)
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( sP4(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f29,f37,f36,f35])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> sP3(X2,X1,X0) )
      | ~ sP4(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X3,X4) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_orders_2(X0,X1))
      | ~ sP3(X1,X0,X2)
      | ~ sP4(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f84,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ sP3(X2,X1,X0)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ~ sP3(X2,X1,X0) )
        & ( sP3(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ sP4(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f288,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k2_orders_2(X0,k2_struct_0(X0)))
      | sP3(k2_struct_0(X0),X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f286,f69])).

fof(f286,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k2_orders_2(X0,k2_struct_0(X0)))
      | sP3(k2_struct_0(X0),X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(superposition,[],[f254,f68])).

fof(f254,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k2_orders_2(X2,u1_struct_0(X2)))
      | sP3(u1_struct_0(X2),X2,X3)
      | ~ l1_orders_2(X2)
      | ~ v5_orders_2(X2)
      | ~ v4_orders_2(X2)
      | ~ v3_orders_2(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f173,f100])).

fof(f100,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f66,f64])).

fof(f64,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f66,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f173,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
      | sP3(X4,X3,X5)
      | ~ r2_hidden(X5,k2_orders_2(X3,X4))
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f171,f93])).

fof(f171,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k2_orders_2(X3,X4))
      | sP3(X4,X3,X5)
      | ~ sP4(X5,X3,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3)
      | v2_struct_0(X3) ) ),
    inference(superposition,[],[f83,f77])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | sP3(X2,X1,X0)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f63,plain,(
    k1_xboole_0 != k2_orders_2(sK5,k2_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n019.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 18:51:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (12577)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.49  % (12593)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.49  % (12580)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.49  % (12590)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.50  % (12571)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (12572)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (12573)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (12576)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (12592)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (12582)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (12582)Refutation not found, incomplete strategy% (12582)------------------------------
% 0.21/0.51  % (12582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12582)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (12582)Memory used [KB]: 6140
% 0.21/0.51  % (12582)Time elapsed: 0.075 s
% 0.21/0.51  % (12582)------------------------------
% 0.21/0.51  % (12582)------------------------------
% 0.21/0.51  % (12584)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (12588)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (12579)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (12573)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f359,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f358,f62])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    l1_orders_2(sK5)),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    k1_xboole_0 != k2_orders_2(sK5,k2_struct_0(sK5)) & l1_orders_2(sK5) & v5_orders_2(sK5) & v4_orders_2(sK5) & v3_orders_2(sK5) & ~v2_struct_0(sK5)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f18,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k2_orders_2(sK5,k2_struct_0(sK5)) & l1_orders_2(sK5) & v5_orders_2(sK5) & v4_orders_2(sK5) & v3_orders_2(sK5) & ~v2_struct_0(sK5))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 0.21/0.52    inference(negated_conjecture,[],[f15])).
% 0.21/0.52  fof(f15,conjecture,(
% 0.21/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_orders_2)).
% 0.21/0.52  fof(f358,plain,(
% 0.21/0.52    ~l1_orders_2(sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f357,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ~v2_struct_0(sK5)),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f357,plain,(
% 0.21/0.52    v2_struct_0(sK5) | ~l1_orders_2(sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f356,f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    v3_orders_2(sK5)),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f356,plain,(
% 0.21/0.52    ~v3_orders_2(sK5) | v2_struct_0(sK5) | ~l1_orders_2(sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f355,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    v4_orders_2(sK5)),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f355,plain,(
% 0.21/0.52    ~v4_orders_2(sK5) | ~v3_orders_2(sK5) | v2_struct_0(sK5) | ~l1_orders_2(sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f354,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    v5_orders_2(sK5)),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f354,plain,(
% 0.21/0.52    ~v5_orders_2(sK5) | ~v4_orders_2(sK5) | ~v3_orders_2(sK5) | v2_struct_0(sK5) | ~l1_orders_2(sK5)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f349])).
% 0.21/0.52  fof(f349,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | ~v5_orders_2(sK5) | ~v4_orders_2(sK5) | ~v3_orders_2(sK5) | v2_struct_0(sK5) | ~l1_orders_2(sK5)),
% 0.21/0.52    inference(superposition,[],[f63,f340])).
% 0.21/0.52  fof(f340,plain,(
% 0.21/0.52    ( ! [X2] : (k1_xboole_0 = k2_orders_2(X2,k2_struct_0(X2)) | ~v5_orders_2(X2) | ~v4_orders_2(X2) | ~v3_orders_2(X2) | v2_struct_0(X2) | ~l1_orders_2(X2)) )),
% 0.21/0.52    inference(resolution,[],[f320,f78])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f27,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.52  fof(f320,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X1,k2_orders_2(X0,k2_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f288,f319])).
% 0.21/0.52  fof(f319,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~sP3(k2_struct_0(X0),X0,X1) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f318,f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.21/0.52  fof(f318,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~sP3(k2_struct_0(X0),X0,X1) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~l1_struct_0(X0)) )),
% 0.21/0.52    inference(superposition,[],[f314,f68])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.52  fof(f314,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~sP3(u1_struct_0(X0),X0,X1) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f310])).
% 0.21/0.52  fof(f310,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | ~sP3(u1_struct_0(X0),X0,X1) | ~sP3(u1_struct_0(X0),X0,X1) | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(resolution,[],[f225,f154])).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    ( ! [X6,X4,X5] : (~r2_hidden(sK7(X4,X5,X6),X4) | ~sP3(X4,X5,X6) | ~l1_orders_2(X5)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f152,f85])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) | ~sP3(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ! [X3] : (~sP2(X3,X1,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((sP2(sK7(X0,X1,X2),X1,X0) & sK7(X0,X1,X2) = X2 & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))) | ~sP3(X0,X1,X2)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f51,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X4] : (sP2(X4,X1,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (sP2(sK7(X0,X1,X2),X1,X0) & sK7(X0,X1,X2) = X2 & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ! [X3] : (~sP2(X3,X1,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (sP2(X4,X1,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~sP3(X0,X1,X2)))),
% 0.21/0.52    inference(rectify,[],[f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ! [X2,X1,X0] : ((sP3(X2,X1,X0) | ! [X3] : (~sP2(X3,X1,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (sP2(X3,X1,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP3(X2,X1,X0)))),
% 0.21/0.52    inference(nnf_transformation,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (sP3(X2,X1,X0) <=> ? [X3] : (sP2(X3,X1,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    ( ! [X6,X4,X5] : (~m1_subset_1(sK7(X4,X5,X6),u1_struct_0(X5)) | ~r2_hidden(sK7(X4,X5,X6),X4) | ~sP3(X4,X5,X6) | ~l1_orders_2(X5)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f149])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    ( ! [X6,X4,X5] : (~m1_subset_1(sK7(X4,X5,X6),u1_struct_0(X5)) | ~r2_hidden(sK7(X4,X5,X6),X4) | ~sP3(X4,X5,X6) | ~l1_orders_2(X5) | ~m1_subset_1(sK7(X4,X5,X6),u1_struct_0(X5))) )),
% 0.21/0.52    inference(resolution,[],[f136,f147])).
% 0.21/0.52  % (12580)Refutation not found, incomplete strategy% (12580)------------------------------
% 0.21/0.52  % (12580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_orders_2(X1,X0,X0) | ~l1_orders_2(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f143])).
% 0.21/0.52  % (12580)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  fof(f143,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~r2_orders_2(X1,X0,X0) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.21/0.52    inference(resolution,[],[f131,f95])).
% 0.21/0.52  % (12580)Memory used [KB]: 10490
% 0.21/0.52  % (12580)Time elapsed: 0.104 s
% 0.21/0.52  % (12580)------------------------------
% 0.21/0.52  % (12580)------------------------------
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    ( ! [X2,X1] : (~sP0(X1,X1,X2)) )),
% 0.21/0.52    inference(equality_resolution,[],[f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (X0 != X1 | ~sP0(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | X0 = X1 | ~r1_orders_2(X2,X1,X0)) & ((X0 != X1 & r1_orders_2(X2,X1,X0)) | ~sP0(X0,X1,X2)))),
% 0.21/0.52    inference(rectify,[],[f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ! [X2,X1,X0] : ((sP0(X2,X1,X0) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~sP0(X2,X1,X0)))),
% 0.21/0.52    inference(flattening,[],[f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ! [X2,X1,X0] : ((sP0(X2,X1,X0) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~sP0(X2,X1,X0)))),
% 0.21/0.52    inference(nnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (sP0(X2,X1,X0) <=> (X1 != X2 & r1_orders_2(X0,X1,X2)))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    ( ! [X4,X5,X3] : (sP0(X3,X5,X4) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~l1_orders_2(X4) | ~r2_orders_2(X4,X5,X3) | ~m1_subset_1(X3,u1_struct_0(X4))) )),
% 0.21/0.52    inference(resolution,[],[f75,f70])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_orders_2(X0,X1,X2) | sP0(X2,X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((r2_orders_2(X0,X1,X2) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_orders_2(X0,X1,X2))) | ~sP1(X0,X1,X2))),
% 0.21/0.52    inference(nnf_transformation,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_orders_2(X0,X1,X2) <=> sP0(X2,X1,X0)) | ~sP1(X0,X1,X2))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (sP1(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(definition_folding,[],[f22,f33,f32])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).
% 0.21/0.52  fof(f136,plain,(
% 0.21/0.52    ( ! [X6,X4,X5,X3] : (r2_orders_2(X5,sK7(X4,X5,X6),X3) | ~m1_subset_1(X3,u1_struct_0(X5)) | ~r2_hidden(X3,X4) | ~sP3(X4,X5,X6)) )),
% 0.21/0.52    inference(resolution,[],[f89,f87])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (sP2(sK7(X0,X1,X2),X1,X0) | ~sP3(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f53])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X1] : (~sP2(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r2_orders_2(X1,X0,X4)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | (~r2_orders_2(X1,X0,sK8(X0,X1,X2)) & r2_hidden(sK8(X0,X1,X2),X2) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r2_orders_2(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP2(X0,X1,X2)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f55,f56])).
% 0.21/0.52  % (12581)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X3] : (~r2_orders_2(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r2_orders_2(X1,X0,sK8(X0,X1,X2)) & r2_hidden(sK8(X0,X1,X2),X2) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : (~r2_orders_2(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r2_orders_2(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP2(X0,X1,X2)))),
% 0.21/0.52    inference(rectify,[],[f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ! [X3,X1,X2] : ((sP2(X3,X1,X2) | ? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1)))) & (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP2(X3,X1,X2)))),
% 0.21/0.52    inference(nnf_transformation,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X3,X1,X2] : (sP2(X3,X1,X2) <=> ! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.52  fof(f225,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK7(X1,X0,X2),u1_struct_0(X0)) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | ~sP3(X1,X0,X2)) )),
% 0.21/0.52    inference(resolution,[],[f224,f85])).
% 0.21/0.52  fof(f224,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1) | r2_hidden(X0,u1_struct_0(X1))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f223,f104])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sP2(X0,X1,k1_xboole_0)) )),
% 0.21/0.52    inference(resolution,[],[f91,f101])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(superposition,[],[f79,f96])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f82])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.52    inference(flattening,[],[f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK8(X0,X1,X2),X2) | sP2(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f57])).
% 0.21/0.52  fof(f223,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1) | ~sP2(X0,X1,k1_xboole_0) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.21/0.52    inference(resolution,[],[f222,f98])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (sP3(X0,X1,X3) | ~sP2(X3,X1,X0) | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 0.21/0.52    inference(equality_resolution,[],[f88])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (sP3(X0,X1,X2) | ~sP2(X3,X1,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f53])).
% 0.21/0.52  fof(f222,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~sP3(k1_xboole_0,X0,X1) | r2_hidden(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f221])).
% 0.21/0.52  fof(f221,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(X1,u1_struct_0(X0)) | ~sP3(k1_xboole_0,X0,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(superposition,[],[f210,f140])).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    ( ! [X0] : (u1_struct_0(X0) = k2_orders_2(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f139,f69])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    ( ! [X0] : (u1_struct_0(X0) = k2_orders_2(X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.21/0.52    inference(superposition,[],[f76,f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0] : (k1_xboole_0 = k1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0] : (l1_struct_0(X0) => k1_xboole_0 = k1_struct_0(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_struct_0)).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ( ! [X0] : (u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0] : (u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0] : (u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,axiom,(
% 0.21/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k2_orders_2(X0,k1_struct_0(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_orders_2)).
% 0.21/0.52  fof(f210,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(X1,k2_orders_2(X0,k1_xboole_0)) | ~sP3(k1_xboole_0,X0,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(resolution,[],[f172,f65])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.52  fof(f172,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~sP3(X1,X0,X2) | r2_hidden(X2,k2_orders_2(X0,X1)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f170,f93])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | sP4(X0,X1,X2) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (sP4(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.21/0.52    inference(definition_folding,[],[f29,f37,f36,f35])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> sP3(X2,X1,X0)) | ~sP4(X0,X1,X2))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.21/0.52    inference(flattening,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).
% 0.21/0.52  fof(f170,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(X2,k2_orders_2(X0,X1)) | ~sP3(X1,X0,X2) | ~sP4(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(superposition,[],[f84,f77])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~sP3(X2,X1,X0) | ~sP4(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~sP3(X2,X1,X0)) & (sP3(X2,X1,X0) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~sP4(X0,X1,X2))),
% 0.21/0.52    inference(nnf_transformation,[],[f37])).
% 0.21/0.52  fof(f288,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X1,k2_orders_2(X0,k2_struct_0(X0))) | sP3(k2_struct_0(X0),X0,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f286,f69])).
% 0.21/0.52  fof(f286,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X1,k2_orders_2(X0,k2_struct_0(X0))) | sP3(k2_struct_0(X0),X0,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.21/0.52    inference(superposition,[],[f254,f68])).
% 0.21/0.52  fof(f254,plain,(
% 0.21/0.52    ( ! [X2,X3] : (~r2_hidden(X3,k2_orders_2(X2,u1_struct_0(X2))) | sP3(u1_struct_0(X2),X2,X3) | ~l1_orders_2(X2) | ~v5_orders_2(X2) | ~v4_orders_2(X2) | ~v3_orders_2(X2) | v2_struct_0(X2)) )),
% 0.21/0.52    inference(resolution,[],[f173,f100])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f66,f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.52  fof(f173,plain,(
% 0.21/0.52    ( ! [X4,X5,X3] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3))) | sP3(X4,X3,X5) | ~r2_hidden(X5,k2_orders_2(X3,X4)) | ~l1_orders_2(X3) | ~v5_orders_2(X3) | ~v4_orders_2(X3) | ~v3_orders_2(X3) | v2_struct_0(X3)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f171,f93])).
% 0.21/0.52  fof(f171,plain,(
% 0.21/0.52    ( ! [X4,X5,X3] : (~r2_hidden(X5,k2_orders_2(X3,X4)) | sP3(X4,X3,X5) | ~sP4(X5,X3,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3))) | ~l1_orders_2(X3) | ~v5_orders_2(X3) | ~v4_orders_2(X3) | ~v3_orders_2(X3) | v2_struct_0(X3)) )),
% 0.21/0.52    inference(superposition,[],[f83,f77])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | sP3(X2,X1,X0) | ~sP4(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f49])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    k1_xboole_0 != k2_orders_2(sK5,k2_struct_0(sK5))),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (12573)------------------------------
% 0.21/0.52  % (12573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12573)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (12573)Memory used [KB]: 6268
% 0.21/0.52  % (12573)Time elapsed: 0.094 s
% 0.21/0.52  % (12573)------------------------------
% 0.21/0.52  % (12573)------------------------------
% 0.21/0.52  % (12568)Success in time 0.158 s
%------------------------------------------------------------------------------
