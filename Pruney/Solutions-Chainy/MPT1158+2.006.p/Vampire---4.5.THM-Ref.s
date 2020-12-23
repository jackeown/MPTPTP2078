%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 507 expanded)
%              Number of leaves         :   25 ( 171 expanded)
%              Depth                    :   16
%              Number of atoms          :  664 (3846 expanded)
%              Number of equality atoms :   96 ( 203 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f411,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f104,f125,f129,f308,f360,f368,f374,f410])).

fof(f410,plain,
    ( spl9_1
    | ~ spl9_17 ),
    inference(avatar_contradiction_clause,[],[f409])).

fof(f409,plain,
    ( $false
    | spl9_1
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f408,f59])).

fof(f59,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ( ~ r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
      | ~ r2_orders_2(sK3,sK4,sK5) )
    & ( r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
      | r2_orders_2(sK3,sK4,sK5) )
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f35,f38,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
                  | ~ r2_orders_2(X0,X1,X2) )
                & ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
                  | r2_orders_2(X0,X1,X2) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_hidden(X1,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2)))
                | ~ r2_orders_2(sK3,X1,X2) )
              & ( r2_hidden(X1,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2)))
                | r2_orders_2(sK3,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(sK3)) )
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l1_orders_2(sK3)
      & v5_orders_2(sK3)
      & v4_orders_2(sK3)
      & v3_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r2_hidden(X1,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2)))
              | ~ r2_orders_2(sK3,X1,X2) )
            & ( r2_hidden(X1,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2)))
              | r2_orders_2(sK3,X1,X2) )
            & m1_subset_1(X2,u1_struct_0(sK3)) )
        & m1_subset_1(X1,u1_struct_0(sK3)) )
   => ( ? [X2] :
          ( ( ~ r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2)))
            | ~ r2_orders_2(sK3,sK4,X2) )
          & ( r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2)))
            | r2_orders_2(sK3,sK4,X2) )
          & m1_subset_1(X2,u1_struct_0(sK3)) )
      & m1_subset_1(sK4,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X2] :
        ( ( ~ r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2)))
          | ~ r2_orders_2(sK3,sK4,X2) )
        & ( r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2)))
          | r2_orders_2(sK3,sK4,X2) )
        & m1_subset_1(X2,u1_struct_0(sK3)) )
   => ( ( ~ r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
        | ~ r2_orders_2(sK3,sK4,sK5) )
      & ( r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
        | r2_orders_2(sK3,sK4,sK5) )
      & m1_subset_1(sK5,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

% (20390)Refutation not found, incomplete strategy% (20390)------------------------------
% (20390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20390)Termination reason: Refutation not found, incomplete strategy

% (20390)Memory used [KB]: 1918
% (20390)Time elapsed: 0.115 s
% (20390)------------------------------
% (20390)------------------------------
% (20402)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% (20404)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% (20414)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% (20402)Refutation not found, incomplete strategy% (20402)------------------------------
% (20402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20402)Termination reason: Refutation not found, incomplete strategy

% (20402)Memory used [KB]: 10746
% (20402)Time elapsed: 0.140 s
% (20402)------------------------------
% (20402)------------------------------
% (20403)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% (20406)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% (20397)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% (20414)Refutation not found, incomplete strategy% (20414)------------------------------
% (20414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20414)Termination reason: Refutation not found, incomplete strategy

% (20414)Memory used [KB]: 10746
% (20414)Time elapsed: 0.136 s
% (20414)------------------------------
% (20414)------------------------------
% (20395)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% (20401)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% (20405)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% (20396)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% (20396)Refutation not found, incomplete strategy% (20396)------------------------------
% (20396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20396)Termination reason: Refutation not found, incomplete strategy

% (20396)Memory used [KB]: 10746
% (20396)Time elapsed: 0.141 s
% (20396)------------------------------
% (20396)------------------------------
% (20409)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
                | ~ r2_orders_2(X0,X1,X2) )
              & ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
                | r2_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

% (20407)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
                | ~ r2_orders_2(X0,X1,X2) )
              & ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
                | r2_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <~> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <~> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_orders_2(X0,X1,X2)
                <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_orders_2)).

fof(f408,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | spl9_1
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f402,f98])).

fof(f98,plain,
    ( ~ r2_orders_2(sK3,sK4,sK5)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl9_1
  <=> r2_orders_2(sK3,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f402,plain,
    ( r2_orders_2(sK3,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl9_17 ),
    inference(resolution,[],[f398,f109])).

fof(f109,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(resolution,[],[f93,f94])).

fof(f94,plain,(
    ! [X0,X1] : sP2(X1,X0,k2_tarski(X0,X1)) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( sP2(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP2(X1,X0,X2) )
      & ( sP2(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP2(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f32])).

fof(f32,plain,(
    ! [X1,X0,X2] :
      ( sP2(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f93,plain,(
    ! [X4,X2,X0] :
      ( ~ sP2(X0,X4,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ( ( sK8(X0,X1,X2) != X0
              & sK8(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( sK8(X0,X1,X2) = X0
            | sK8(X0,X1,X2) = X1
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f49,f50])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK8(X0,X1,X2) != X0
            & sK8(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( sK8(X0,X1,X2) = X0
          | sK8(X0,X1,X2) = X1
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ( X0 != X3
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X0 = X3
              | X1 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X1,X0,X2] :
      ( ( sP2(X1,X0,X2)
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
        | ~ sP2(X1,X0,X2) ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X1,X0,X2] :
      ( ( sP2(X1,X0,X2)
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
        | ~ sP2(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f398,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_tarski(sK5,sK5))
        | r2_orders_2(sK3,sK4,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3)) )
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f394,f306])).

fof(f306,plain,
    ( sP0(sK3,k2_tarski(sK5,sK5),sK4)
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f305])).

fof(f305,plain,
    ( spl9_17
  <=> sP0(sK3,k2_tarski(sK5,sK5),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f394,plain,
    ( ! [X1] :
        ( r2_orders_2(sK3,sK4,X1)
        | ~ r2_hidden(X1,k2_tarski(sK5,sK5))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ sP0(sK3,k2_tarski(sK5,sK5),sK4) )
    | ~ spl9_17 ),
    inference(superposition,[],[f73,f377])).

fof(f377,plain,
    ( sK4 = sK7(sK3,k2_tarski(sK5,sK5),sK4)
    | ~ spl9_17 ),
    inference(resolution,[],[f306,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | sK7(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ( ~ r2_orders_2(X0,X3,sK6(X0,X1,X3))
              & r2_hidden(sK6(X0,X1,X3),X1)
              & m1_subset_1(sK6(X0,X1,X3),u1_struct_0(X0)) )
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ( ! [X6] :
              ( r2_orders_2(X0,sK7(X0,X1,X2),X6)
              | ~ r2_hidden(X6,X1)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & sK7(X0,X1,X2) = X2
          & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f43,f45,f44])).

fof(f44,plain,(
    ! [X3,X1,X0] :
      ( ? [X4] :
          ( ~ r2_orders_2(X0,X3,X4)
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r2_orders_2(X0,X3,sK6(X0,X1,X3))
        & r2_hidden(sK6(X0,X1,X3),X1)
        & m1_subset_1(sK6(X0,X1,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X0,X5,X6)
              | ~ r2_hidden(X6,X1)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & X2 = X5
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ! [X6] :
            ( r2_orders_2(X0,sK7(X0,X1,X2),X6)
            | ~ r2_hidden(X6,X1)
            | ~ m1_subset_1(X6,u1_struct_0(X0)) )
        & sK7(X0,X1,X2) = X2
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ? [X4] :
                ( ~ r2_orders_2(X0,X3,X4)
                & r2_hidden(X4,X1)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ? [X5] :
            ( ! [X6] :
                ( r2_orders_2(X0,X5,X6)
                | ~ r2_hidden(X6,X1)
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            & X2 = X5
            & m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ! [X3] :
            ( ? [X4] :
                ( ~ r2_orders_2(X1,X3,X4)
                & r2_hidden(X4,X2)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ? [X3] :
          ( ! [X4] :
              ( r2_orders_2(X1,X3,X4)
              | ~ r2_hidden(X4,X2)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f73,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_orders_2(X0,sK7(X0,X1,X2),X6)
      | ~ r2_hidden(X6,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f374,plain,
    ( ~ spl9_16
    | spl9_17
    | ~ spl9_2
    | spl9_4
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f371,f122,f117,f100,f305,f301])).

fof(f301,plain,
    ( spl9_16
  <=> sP1(sK4,k2_tarski(sK5,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f100,plain,
    ( spl9_2
  <=> r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f117,plain,
    ( spl9_4
  <=> v1_xboole_0(u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f122,plain,
    ( spl9_5
  <=> r2_hidden(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f371,plain,
    ( sP0(sK3,k2_tarski(sK5,sK5),sK4)
    | ~ sP1(sK4,k2_tarski(sK5,sK5),sK3)
    | ~ spl9_2
    | spl9_4
    | ~ spl9_5 ),
    inference(resolution,[],[f151,f273])).

fof(f273,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k2_orders_2(sK3,k2_tarski(sK5,sK5)))
        | sP0(sK3,k2_tarski(sK5,sK5),X2)
        | ~ sP1(X2,k2_tarski(sK5,sK5),sK3) )
    | ~ spl9_5 ),
    inference(superposition,[],[f69,f267])).

fof(f267,plain,
    ( k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5))
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f266,f53])).

fof(f53,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f266,plain,
    ( v2_struct_0(sK3)
    | k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5))
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f265,f54])).

fof(f54,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f265,plain,
    ( ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5))
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f264,f55])).

fof(f55,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f264,plain,
    ( ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5))
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f263,f56])).

fof(f56,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f263,plain,
    ( ~ v5_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5))
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f253,f57])).

fof(f57,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f253,plain,
    ( ~ l1_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5))
    | ~ spl9_5 ),
    inference(resolution,[],[f190,f124])).

fof(f124,plain,
    ( r2_hidden(sK5,u1_struct_0(sK3))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f122])).

fof(f190,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | k2_orders_2(X0,k2_tarski(X1,X1)) = a_2_1_orders_2(X0,k2_tarski(X1,X1)) ) ),
    inference(resolution,[],[f65,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f66,f62])).

fof(f62,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(X2,X1))
      | sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X2,X1))
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_1_orders_2(X2,X1)) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X2,X1] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X2,X1] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f151,plain,
    ( r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5)))
    | ~ spl9_2
    | spl9_4 ),
    inference(backward_demodulation,[],[f101,f146])).

fof(f146,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5)
    | spl9_4 ),
    inference(subsumption_resolution,[],[f142,f118])).

fof(f118,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3))
    | spl9_4 ),
    inference(avatar_component_clause,[],[f117])).

fof(f142,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5)
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(resolution,[],[f88,f59])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f68,f62])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f101,plain,
    ( r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f100])).

fof(f368,plain,
    ( ~ spl9_5
    | spl9_16 ),
    inference(avatar_contradiction_clause,[],[f367])).

fof(f367,plain,
    ( $false
    | ~ spl9_5
    | spl9_16 ),
    inference(subsumption_resolution,[],[f366,f124])).

fof(f366,plain,
    ( ~ r2_hidden(sK5,u1_struct_0(sK3))
    | spl9_16 ),
    inference(subsumption_resolution,[],[f365,f53])).

fof(f365,plain,
    ( v2_struct_0(sK3)
    | ~ r2_hidden(sK5,u1_struct_0(sK3))
    | spl9_16 ),
    inference(subsumption_resolution,[],[f364,f54])).

fof(f364,plain,
    ( ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ r2_hidden(sK5,u1_struct_0(sK3))
    | spl9_16 ),
    inference(subsumption_resolution,[],[f363,f55])).

fof(f363,plain,
    ( ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ r2_hidden(sK5,u1_struct_0(sK3))
    | spl9_16 ),
    inference(subsumption_resolution,[],[f362,f56])).

fof(f362,plain,
    ( ~ v5_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ r2_hidden(sK5,u1_struct_0(sK3))
    | spl9_16 ),
    inference(subsumption_resolution,[],[f361,f57])).

% (20398)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
fof(f361,plain,
    ( ~ l1_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ r2_hidden(sK5,u1_struct_0(sK3))
    | spl9_16 ),
    inference(resolution,[],[f303,f188])).

fof(f188,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,k2_tarski(X1,X1),X2)
      | ~ l1_orders_2(X2)
      | ~ v5_orders_2(X2)
      | ~ v4_orders_2(X2)
      | ~ v3_orders_2(X2)
      | v2_struct_0(X2)
      | ~ r2_hidden(X1,u1_struct_0(X2)) ) ),
    inference(resolution,[],[f77,f87])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | sP1(X0,X2,X1)
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f26,f30,f29])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f303,plain,
    ( ~ sP1(sK4,k2_tarski(sK5,sK5),sK3)
    | spl9_16 ),
    inference(avatar_component_clause,[],[f301])).

fof(f360,plain,
    ( ~ spl9_1
    | spl9_17 ),
    inference(avatar_contradiction_clause,[],[f359])).

fof(f359,plain,
    ( $false
    | ~ spl9_1
    | spl9_17 ),
    inference(subsumption_resolution,[],[f358,f58])).

fof(f58,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f39])).

fof(f358,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ spl9_1
    | spl9_17 ),
    inference(subsumption_resolution,[],[f357,f307])).

fof(f307,plain,
    ( ~ sP0(sK3,k2_tarski(sK5,sK5),sK4)
    | spl9_17 ),
    inference(avatar_component_clause,[],[f305])).

fof(f357,plain,
    ( sP0(sK3,k2_tarski(sK5,sK5),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ spl9_1
    | spl9_17 ),
    inference(subsumption_resolution,[],[f354,f97])).

fof(f97,plain,
    ( r2_orders_2(sK3,sK4,sK5)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f354,plain,
    ( ~ r2_orders_2(sK3,sK4,sK5)
    | sP0(sK3,k2_tarski(sK5,sK5),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | spl9_17 ),
    inference(superposition,[],[f89,f350])).

fof(f350,plain,
    ( sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4)
    | spl9_17 ),
    inference(subsumption_resolution,[],[f349,f58])).

fof(f349,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4)
    | spl9_17 ),
    inference(duplicate_literal_removal,[],[f348])).

fof(f348,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4)
    | sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4)
    | spl9_17 ),
    inference(resolution,[],[f175,f307])).

fof(f175,plain,(
    ! [X6,X4,X7,X5] :
      ( sP0(X4,k2_tarski(X5,X6),X7)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | sK6(X4,k2_tarski(X5,X6),X7) = X5
      | sK6(X4,k2_tarski(X5,X6),X7) = X6 ) ),
    inference(resolution,[],[f90,f168])).

fof(f168,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k2_tarski(X0,X2))
      | X0 = X1
      | X1 = X2 ) ),
    inference(resolution,[],[f79,f94])).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | X1 = X4
      | ~ r2_hidden(X4,X2)
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK6(X0,X1,X3),X1)
      | sP0(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(sK6(X0,X1,X3),X1)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_orders_2(X0,X3,sK6(X0,X1,X3))
      | sP0(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | ~ r2_orders_2(X0,X3,sK6(X0,X1,X3))
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f308,plain,
    ( ~ spl9_16
    | ~ spl9_17
    | spl9_2
    | spl9_4
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f294,f122,f117,f100,f305,f301])).

fof(f294,plain,
    ( ~ sP0(sK3,k2_tarski(sK5,sK5),sK4)
    | ~ sP1(sK4,k2_tarski(sK5,sK5),sK3)
    | spl9_2
    | spl9_4
    | ~ spl9_5 ),
    inference(resolution,[],[f272,f226])).

fof(f226,plain,
    ( ~ r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5)))
    | spl9_2
    | spl9_4 ),
    inference(forward_demodulation,[],[f102,f146])).

fof(f102,plain,
    ( ~ r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
    | spl9_2 ),
    inference(avatar_component_clause,[],[f100])).

fof(f272,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k2_orders_2(sK3,k2_tarski(sK5,sK5)))
        | ~ sP0(sK3,k2_tarski(sK5,sK5),X1)
        | ~ sP1(X1,k2_tarski(sK5,sK5),sK3) )
    | ~ spl9_5 ),
    inference(superposition,[],[f70,f267])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_1_orders_2(X2,X1))
      | ~ sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f129,plain,(
    ~ spl9_4 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f127,f53])).

fof(f127,plain,
    ( v2_struct_0(sK3)
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f126,f107])).

fof(f107,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f63,f57])).

fof(f63,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f126,plain,
    ( ~ l1_struct_0(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_4 ),
    inference(resolution,[],[f119,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f119,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f117])).

fof(f125,plain,
    ( spl9_5
    | spl9_4 ),
    inference(avatar_split_clause,[],[f111,f117,f122])).

fof(f111,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | r2_hidden(sK5,u1_struct_0(sK3)) ),
    inference(resolution,[],[f67,f59])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f104,plain,
    ( spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f60,f100,f96])).

fof(f60,plain,
    ( r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
    | r2_orders_2(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f39])).

fof(f103,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f61,f100,f96])).

fof(f61,plain,
    ( ~ r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
    | ~ r2_orders_2(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:50:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (20408)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (20386)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (20393)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (20400)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (20392)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (20400)Refutation not found, incomplete strategy% (20400)------------------------------
% 0.21/0.51  % (20400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (20400)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (20400)Memory used [KB]: 1791
% 0.21/0.51  % (20400)Time elapsed: 0.055 s
% 0.21/0.51  % (20400)------------------------------
% 0.21/0.51  % (20400)------------------------------
% 0.21/0.52  % (20390)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (20391)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (20399)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (20412)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (20411)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (20410)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (20387)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (20388)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (20389)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (20394)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (20413)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (20392)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f411,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f103,f104,f125,f129,f308,f360,f368,f374,f410])).
% 0.21/0.54  fof(f410,plain,(
% 0.21/0.54    spl9_1 | ~spl9_17),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f409])).
% 0.21/0.54  fof(f409,plain,(
% 0.21/0.54    $false | (spl9_1 | ~spl9_17)),
% 0.21/0.54    inference(subsumption_resolution,[],[f408,f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    (((~r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | ~r2_orders_2(sK3,sK4,sK5)) & (r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | r2_orders_2(sK3,sK4,sK5)) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f35,f38,f37,f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | ~r2_orders_2(sK3,X1,X2)) & (r2_hidden(X1,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | r2_orders_2(sK3,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | ~r2_orders_2(sK3,X1,X2)) & (r2_hidden(X1,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | r2_orders_2(sK3,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(X1,u1_struct_0(sK3))) => (? [X2] : ((~r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | ~r2_orders_2(sK3,sK4,X2)) & (r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | r2_orders_2(sK3,sK4,X2)) & m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK3)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ? [X2] : ((~r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | ~r2_orders_2(sK3,sK4,X2)) & (r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | r2_orders_2(sK3,sK4,X2)) & m1_subset_1(X2,u1_struct_0(sK3))) => ((~r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | ~r2_orders_2(sK3,sK4,sK5)) & (r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | r2_orders_2(sK3,sK4,sK5)) & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  % (20390)Refutation not found, incomplete strategy% (20390)------------------------------
% 0.21/0.54  % (20390)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (20390)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (20390)Memory used [KB]: 1918
% 0.21/0.54  % (20390)Time elapsed: 0.115 s
% 0.21/0.54  % (20390)------------------------------
% 0.21/0.54  % (20390)------------------------------
% 0.21/0.54  % (20402)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (20404)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (20414)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (20402)Refutation not found, incomplete strategy% (20402)------------------------------
% 0.21/0.55  % (20402)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (20402)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (20402)Memory used [KB]: 10746
% 0.21/0.55  % (20402)Time elapsed: 0.140 s
% 0.21/0.55  % (20402)------------------------------
% 0.21/0.55  % (20402)------------------------------
% 0.21/0.55  % (20403)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (20406)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (20397)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (20414)Refutation not found, incomplete strategy% (20414)------------------------------
% 0.21/0.55  % (20414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (20414)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (20414)Memory used [KB]: 10746
% 0.21/0.55  % (20414)Time elapsed: 0.136 s
% 0.21/0.55  % (20414)------------------------------
% 0.21/0.55  % (20414)------------------------------
% 0.21/0.55  % (20395)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (20401)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (20405)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (20396)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (20396)Refutation not found, incomplete strategy% (20396)------------------------------
% 0.21/0.55  % (20396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (20396)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (20396)Memory used [KB]: 10746
% 0.21/0.55  % (20396)Time elapsed: 0.141 s
% 0.21/0.55  % (20396)------------------------------
% 0.21/0.55  % (20396)------------------------------
% 0.21/0.55  % (20409)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f34])).
% 0.21/0.56  % (20407)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (? [X2] : (((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.56    inference(nnf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f13])).
% 0.21/0.56  fof(f13,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,negated_conjecture,(
% 0.21/0.56    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 0.21/0.56    inference(negated_conjecture,[],[f11])).
% 0.21/0.56  fof(f11,conjecture,(
% 0.21/0.56    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_orders_2)).
% 0.21/0.56  fof(f408,plain,(
% 0.21/0.56    ~m1_subset_1(sK5,u1_struct_0(sK3)) | (spl9_1 | ~spl9_17)),
% 0.21/0.56    inference(subsumption_resolution,[],[f402,f98])).
% 0.21/0.56  fof(f98,plain,(
% 0.21/0.56    ~r2_orders_2(sK3,sK4,sK5) | spl9_1),
% 0.21/0.56    inference(avatar_component_clause,[],[f96])).
% 0.21/0.56  fof(f96,plain,(
% 0.21/0.56    spl9_1 <=> r2_orders_2(sK3,sK4,sK5)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.56  fof(f402,plain,(
% 0.21/0.56    r2_orders_2(sK3,sK4,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~spl9_17),
% 0.21/0.56    inference(resolution,[],[f398,f109])).
% 0.21/0.56  fof(f109,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 0.21/0.56    inference(resolution,[],[f93,f94])).
% 0.21/0.56  fof(f94,plain,(
% 0.21/0.56    ( ! [X0,X1] : (sP2(X1,X0,k2_tarski(X0,X1))) )),
% 0.21/0.56    inference(equality_resolution,[],[f85])).
% 0.21/0.56  fof(f85,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (sP2(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 0.21/0.56    inference(cnf_transformation,[],[f52])).
% 0.21/0.56  fof(f52,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP2(X1,X0,X2)) & (sP2(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 0.21/0.56    inference(nnf_transformation,[],[f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP2(X1,X0,X2))),
% 0.21/0.56    inference(definition_folding,[],[f1,f32])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ! [X1,X0,X2] : (sP2(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.21/0.56  fof(f93,plain,(
% 0.21/0.56    ( ! [X4,X2,X0] : (~sP2(X0,X4,X2) | r2_hidden(X4,X2)) )),
% 0.21/0.56    inference(equality_resolution,[],[f80])).
% 0.21/0.56  fof(f80,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | ~sP2(X0,X1,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f51])).
% 0.21/0.56  fof(f51,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | (((sK8(X0,X1,X2) != X0 & sK8(X0,X1,X2) != X1) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sK8(X0,X1,X2) = X0 | sK8(X0,X1,X2) = X1 | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f49,f50])).
% 0.21/0.56  fof(f50,plain,(
% 0.21/0.56    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK8(X0,X1,X2) != X0 & sK8(X0,X1,X2) != X1) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sK8(X0,X1,X2) = X0 | sK8(X0,X1,X2) = X1 | r2_hidden(sK8(X0,X1,X2),X2))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f49,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 0.21/0.56    inference(rectify,[],[f48])).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    ! [X1,X0,X2] : ((sP2(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP2(X1,X0,X2)))),
% 0.21/0.56    inference(flattening,[],[f47])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    ! [X1,X0,X2] : ((sP2(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP2(X1,X0,X2)))),
% 0.21/0.56    inference(nnf_transformation,[],[f32])).
% 0.21/0.56  fof(f398,plain,(
% 0.21/0.56    ( ! [X1] : (~r2_hidden(X1,k2_tarski(sK5,sK5)) | r2_orders_2(sK3,sK4,X1) | ~m1_subset_1(X1,u1_struct_0(sK3))) ) | ~spl9_17),
% 0.21/0.56    inference(subsumption_resolution,[],[f394,f306])).
% 0.21/0.56  fof(f306,plain,(
% 0.21/0.56    sP0(sK3,k2_tarski(sK5,sK5),sK4) | ~spl9_17),
% 0.21/0.56    inference(avatar_component_clause,[],[f305])).
% 0.21/0.56  fof(f305,plain,(
% 0.21/0.56    spl9_17 <=> sP0(sK3,k2_tarski(sK5,sK5),sK4)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 0.21/0.56  fof(f394,plain,(
% 0.21/0.56    ( ! [X1] : (r2_orders_2(sK3,sK4,X1) | ~r2_hidden(X1,k2_tarski(sK5,sK5)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~sP0(sK3,k2_tarski(sK5,sK5),sK4)) ) | ~spl9_17),
% 0.21/0.56    inference(superposition,[],[f73,f377])).
% 0.21/0.56  fof(f377,plain,(
% 0.21/0.56    sK4 = sK7(sK3,k2_tarski(sK5,sK5),sK4) | ~spl9_17),
% 0.21/0.56    inference(resolution,[],[f306,f72])).
% 0.21/0.56  fof(f72,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | sK7(X0,X1,X2) = X2) )),
% 0.21/0.56    inference(cnf_transformation,[],[f46])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : ((~r2_orders_2(X0,X3,sK6(X0,X1,X3)) & r2_hidden(sK6(X0,X1,X3),X1) & m1_subset_1(sK6(X0,X1,X3),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & ((! [X6] : (r2_orders_2(X0,sK7(X0,X1,X2),X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK7(X0,X1,X2) = X2 & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))) | ~sP0(X0,X1,X2)))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f43,f45,f44])).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    ! [X3,X1,X0] : (? [X4] : (~r2_orders_2(X0,X3,X4) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r2_orders_2(X0,X3,sK6(X0,X1,X3)) & r2_hidden(sK6(X0,X1,X3),X1) & m1_subset_1(sK6(X0,X1,X3),u1_struct_0(X0))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X0,X5,X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) => (! [X6] : (r2_orders_2(X0,sK7(X0,X1,X2),X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK7(X0,X1,X2) = X2 & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_orders_2(X0,X3,X4) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X5] : (! [X6] : (r2_orders_2(X0,X5,X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) | ~sP0(X0,X1,X2)))),
% 0.21/0.56    inference(rectify,[],[f42])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP0(X1,X2,X0)))),
% 0.21/0.56    inference(nnf_transformation,[],[f29])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 0.21/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.56  fof(f73,plain,(
% 0.21/0.56    ( ! [X6,X2,X0,X1] : (r2_orders_2(X0,sK7(X0,X1,X2),X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~sP0(X0,X1,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f46])).
% 0.21/0.56  fof(f374,plain,(
% 0.21/0.56    ~spl9_16 | spl9_17 | ~spl9_2 | spl9_4 | ~spl9_5),
% 0.21/0.56    inference(avatar_split_clause,[],[f371,f122,f117,f100,f305,f301])).
% 0.21/0.56  fof(f301,plain,(
% 0.21/0.56    spl9_16 <=> sP1(sK4,k2_tarski(sK5,sK5),sK3)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.21/0.56  fof(f100,plain,(
% 0.21/0.56    spl9_2 <=> r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.56  fof(f117,plain,(
% 0.21/0.56    spl9_4 <=> v1_xboole_0(u1_struct_0(sK3))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.21/0.56  fof(f122,plain,(
% 0.21/0.56    spl9_5 <=> r2_hidden(sK5,u1_struct_0(sK3))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.21/0.56  fof(f371,plain,(
% 0.21/0.56    sP0(sK3,k2_tarski(sK5,sK5),sK4) | ~sP1(sK4,k2_tarski(sK5,sK5),sK3) | (~spl9_2 | spl9_4 | ~spl9_5)),
% 0.21/0.56    inference(resolution,[],[f151,f273])).
% 0.21/0.56  fof(f273,plain,(
% 0.21/0.56    ( ! [X2] : (~r2_hidden(X2,k2_orders_2(sK3,k2_tarski(sK5,sK5))) | sP0(sK3,k2_tarski(sK5,sK5),X2) | ~sP1(X2,k2_tarski(sK5,sK5),sK3)) ) | ~spl9_5),
% 0.21/0.56    inference(superposition,[],[f69,f267])).
% 0.21/0.56  fof(f267,plain,(
% 0.21/0.56    k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5)) | ~spl9_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f266,f53])).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    ~v2_struct_0(sK3)),
% 0.21/0.56    inference(cnf_transformation,[],[f39])).
% 0.21/0.56  fof(f266,plain,(
% 0.21/0.56    v2_struct_0(sK3) | k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5)) | ~spl9_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f265,f54])).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    v3_orders_2(sK3)),
% 0.21/0.56    inference(cnf_transformation,[],[f39])).
% 0.21/0.56  fof(f265,plain,(
% 0.21/0.56    ~v3_orders_2(sK3) | v2_struct_0(sK3) | k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5)) | ~spl9_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f264,f55])).
% 0.21/0.56  fof(f55,plain,(
% 0.21/0.56    v4_orders_2(sK3)),
% 0.21/0.56    inference(cnf_transformation,[],[f39])).
% 0.21/0.56  fof(f264,plain,(
% 0.21/0.56    ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5)) | ~spl9_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f263,f56])).
% 0.21/0.56  fof(f56,plain,(
% 0.21/0.56    v5_orders_2(sK3)),
% 0.21/0.56    inference(cnf_transformation,[],[f39])).
% 0.21/0.56  fof(f263,plain,(
% 0.21/0.56    ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5)) | ~spl9_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f253,f57])).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    l1_orders_2(sK3)),
% 0.21/0.56    inference(cnf_transformation,[],[f39])).
% 0.21/0.56  fof(f253,plain,(
% 0.21/0.56    ~l1_orders_2(sK3) | ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5)) | ~spl9_5),
% 0.21/0.56    inference(resolution,[],[f190,f124])).
% 0.21/0.56  fof(f124,plain,(
% 0.21/0.56    r2_hidden(sK5,u1_struct_0(sK3)) | ~spl9_5),
% 0.21/0.56    inference(avatar_component_clause,[],[f122])).
% 0.21/0.56  fof(f190,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r2_hidden(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | k2_orders_2(X0,k2_tarski(X1,X1)) = a_2_1_orders_2(X0,k2_tarski(X1,X1))) )),
% 0.21/0.56    inference(resolution,[],[f65,f87])).
% 0.21/0.56  fof(f87,plain,(
% 0.21/0.56    ( ! [X0,X1] : (m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f66,f62])).
% 0.21/0.56  fof(f62,plain,(
% 0.21/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.56  fof(f66,plain,(
% 0.21/0.56    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f20])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 0.21/0.56  fof(f65,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f19])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f18])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).
% 0.21/0.56  fof(f69,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(X2,X1)) | sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f41])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X2,X1)) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_hidden(X0,a_2_1_orders_2(X2,X1)))) | ~sP1(X0,X1,X2))),
% 0.21/0.56    inference(rectify,[],[f40])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ! [X0,X2,X1] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~sP1(X0,X2,X1))),
% 0.21/0.56    inference(nnf_transformation,[],[f30])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ! [X0,X2,X1] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 0.21/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.56  fof(f151,plain,(
% 0.21/0.56    r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5))) | (~spl9_2 | spl9_4)),
% 0.21/0.56    inference(backward_demodulation,[],[f101,f146])).
% 0.21/0.56  fof(f146,plain,(
% 0.21/0.56    k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5) | spl9_4),
% 0.21/0.56    inference(subsumption_resolution,[],[f142,f118])).
% 0.21/0.56  fof(f118,plain,(
% 0.21/0.56    ~v1_xboole_0(u1_struct_0(sK3)) | spl9_4),
% 0.21/0.56    inference(avatar_component_clause,[],[f117])).
% 0.21/0.56  fof(f142,plain,(
% 0.21/0.56    k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5) | v1_xboole_0(u1_struct_0(sK3))),
% 0.21/0.56    inference(resolution,[],[f88,f59])).
% 0.21/0.56  fof(f88,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f68,f62])).
% 0.21/0.56  fof(f68,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.56    inference(flattening,[],[f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,axiom,(
% 0.21/0.56    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.56  fof(f101,plain,(
% 0.21/0.56    r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | ~spl9_2),
% 0.21/0.56    inference(avatar_component_clause,[],[f100])).
% 0.21/0.56  fof(f368,plain,(
% 0.21/0.56    ~spl9_5 | spl9_16),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f367])).
% 0.21/0.56  fof(f367,plain,(
% 0.21/0.56    $false | (~spl9_5 | spl9_16)),
% 0.21/0.56    inference(subsumption_resolution,[],[f366,f124])).
% 0.21/0.56  fof(f366,plain,(
% 0.21/0.56    ~r2_hidden(sK5,u1_struct_0(sK3)) | spl9_16),
% 0.21/0.56    inference(subsumption_resolution,[],[f365,f53])).
% 0.21/0.56  fof(f365,plain,(
% 0.21/0.56    v2_struct_0(sK3) | ~r2_hidden(sK5,u1_struct_0(sK3)) | spl9_16),
% 0.21/0.56    inference(subsumption_resolution,[],[f364,f54])).
% 0.21/0.56  fof(f364,plain,(
% 0.21/0.56    ~v3_orders_2(sK3) | v2_struct_0(sK3) | ~r2_hidden(sK5,u1_struct_0(sK3)) | spl9_16),
% 0.21/0.56    inference(subsumption_resolution,[],[f363,f55])).
% 0.21/0.56  fof(f363,plain,(
% 0.21/0.56    ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | ~r2_hidden(sK5,u1_struct_0(sK3)) | spl9_16),
% 0.21/0.56    inference(subsumption_resolution,[],[f362,f56])).
% 0.21/0.56  fof(f362,plain,(
% 0.21/0.56    ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | ~r2_hidden(sK5,u1_struct_0(sK3)) | spl9_16),
% 0.21/0.56    inference(subsumption_resolution,[],[f361,f57])).
% 0.21/0.56  % (20398)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.56  fof(f361,plain,(
% 0.21/0.56    ~l1_orders_2(sK3) | ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | ~r2_hidden(sK5,u1_struct_0(sK3)) | spl9_16),
% 0.21/0.56    inference(resolution,[],[f303,f188])).
% 0.21/0.56  fof(f188,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (sP1(X0,k2_tarski(X1,X1),X2) | ~l1_orders_2(X2) | ~v5_orders_2(X2) | ~v4_orders_2(X2) | ~v3_orders_2(X2) | v2_struct_0(X2) | ~r2_hidden(X1,u1_struct_0(X2))) )),
% 0.21/0.56    inference(resolution,[],[f77,f87])).
% 0.21/0.56  fof(f77,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | sP1(X0,X2,X1) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.21/0.56    inference(definition_folding,[],[f26,f30,f29])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.21/0.56    inference(flattening,[],[f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 0.21/0.56    inference(ennf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).
% 0.21/0.56  fof(f303,plain,(
% 0.21/0.56    ~sP1(sK4,k2_tarski(sK5,sK5),sK3) | spl9_16),
% 0.21/0.56    inference(avatar_component_clause,[],[f301])).
% 0.21/0.56  fof(f360,plain,(
% 0.21/0.56    ~spl9_1 | spl9_17),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f359])).
% 0.21/0.56  fof(f359,plain,(
% 0.21/0.56    $false | (~spl9_1 | spl9_17)),
% 0.21/0.56    inference(subsumption_resolution,[],[f358,f58])).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.21/0.56    inference(cnf_transformation,[],[f39])).
% 0.21/0.56  fof(f358,plain,(
% 0.21/0.56    ~m1_subset_1(sK4,u1_struct_0(sK3)) | (~spl9_1 | spl9_17)),
% 0.21/0.56    inference(subsumption_resolution,[],[f357,f307])).
% 0.21/0.56  fof(f307,plain,(
% 0.21/0.56    ~sP0(sK3,k2_tarski(sK5,sK5),sK4) | spl9_17),
% 0.21/0.56    inference(avatar_component_clause,[],[f305])).
% 0.21/0.56  fof(f357,plain,(
% 0.21/0.56    sP0(sK3,k2_tarski(sK5,sK5),sK4) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | (~spl9_1 | spl9_17)),
% 0.21/0.56    inference(subsumption_resolution,[],[f354,f97])).
% 0.21/0.56  fof(f97,plain,(
% 0.21/0.56    r2_orders_2(sK3,sK4,sK5) | ~spl9_1),
% 0.21/0.56    inference(avatar_component_clause,[],[f96])).
% 0.21/0.56  fof(f354,plain,(
% 0.21/0.56    ~r2_orders_2(sK3,sK4,sK5) | sP0(sK3,k2_tarski(sK5,sK5),sK4) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | spl9_17),
% 0.21/0.56    inference(superposition,[],[f89,f350])).
% 0.21/0.56  fof(f350,plain,(
% 0.21/0.56    sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4) | spl9_17),
% 0.21/0.56    inference(subsumption_resolution,[],[f349,f58])).
% 0.21/0.56  fof(f349,plain,(
% 0.21/0.56    ~m1_subset_1(sK4,u1_struct_0(sK3)) | sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4) | spl9_17),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f348])).
% 0.21/0.56  fof(f348,plain,(
% 0.21/0.56    ~m1_subset_1(sK4,u1_struct_0(sK3)) | sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4) | sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4) | spl9_17),
% 0.21/0.56    inference(resolution,[],[f175,f307])).
% 0.21/0.56  fof(f175,plain,(
% 0.21/0.56    ( ! [X6,X4,X7,X5] : (sP0(X4,k2_tarski(X5,X6),X7) | ~m1_subset_1(X7,u1_struct_0(X4)) | sK6(X4,k2_tarski(X5,X6),X7) = X5 | sK6(X4,k2_tarski(X5,X6),X7) = X6) )),
% 0.21/0.56    inference(resolution,[],[f90,f168])).
% 0.21/0.56  fof(f168,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X1,k2_tarski(X0,X2)) | X0 = X1 | X1 = X2) )),
% 0.21/0.56    inference(resolution,[],[f79,f94])).
% 0.21/0.56  fof(f79,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X1] : (~sP2(X0,X1,X2) | X1 = X4 | ~r2_hidden(X4,X2) | X0 = X4) )),
% 0.21/0.56    inference(cnf_transformation,[],[f51])).
% 0.21/0.56  fof(f90,plain,(
% 0.21/0.56    ( ! [X0,X3,X1] : (r2_hidden(sK6(X0,X1,X3),X1) | sP0(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 0.21/0.56    inference(equality_resolution,[],[f75])).
% 0.21/0.56  fof(f75,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2) | r2_hidden(sK6(X0,X1,X3),X1) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f46])).
% 0.21/0.56  fof(f89,plain,(
% 0.21/0.56    ( ! [X0,X3,X1] : (~r2_orders_2(X0,X3,sK6(X0,X1,X3)) | sP0(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 0.21/0.56    inference(equality_resolution,[],[f76])).
% 0.21/0.56  fof(f76,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2) | ~r2_orders_2(X0,X3,sK6(X0,X1,X3)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f46])).
% 0.21/0.56  fof(f308,plain,(
% 0.21/0.56    ~spl9_16 | ~spl9_17 | spl9_2 | spl9_4 | ~spl9_5),
% 0.21/0.56    inference(avatar_split_clause,[],[f294,f122,f117,f100,f305,f301])).
% 0.21/0.56  fof(f294,plain,(
% 0.21/0.56    ~sP0(sK3,k2_tarski(sK5,sK5),sK4) | ~sP1(sK4,k2_tarski(sK5,sK5),sK3) | (spl9_2 | spl9_4 | ~spl9_5)),
% 0.21/0.56    inference(resolution,[],[f272,f226])).
% 0.21/0.56  fof(f226,plain,(
% 0.21/0.56    ~r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5))) | (spl9_2 | spl9_4)),
% 0.21/0.56    inference(forward_demodulation,[],[f102,f146])).
% 0.21/0.56  fof(f102,plain,(
% 0.21/0.56    ~r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | spl9_2),
% 0.21/0.56    inference(avatar_component_clause,[],[f100])).
% 0.21/0.56  fof(f272,plain,(
% 0.21/0.56    ( ! [X1] : (r2_hidden(X1,k2_orders_2(sK3,k2_tarski(sK5,sK5))) | ~sP0(sK3,k2_tarski(sK5,sK5),X1) | ~sP1(X1,k2_tarski(sK5,sK5),sK3)) ) | ~spl9_5),
% 0.21/0.56    inference(superposition,[],[f70,f267])).
% 0.21/0.56  fof(f70,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r2_hidden(X0,a_2_1_orders_2(X2,X1)) | ~sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f41])).
% 0.21/0.56  fof(f129,plain,(
% 0.21/0.56    ~spl9_4),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f128])).
% 0.21/0.56  fof(f128,plain,(
% 0.21/0.56    $false | ~spl9_4),
% 0.21/0.56    inference(subsumption_resolution,[],[f127,f53])).
% 0.21/0.56  fof(f127,plain,(
% 0.21/0.56    v2_struct_0(sK3) | ~spl9_4),
% 0.21/0.56    inference(subsumption_resolution,[],[f126,f107])).
% 0.21/0.56  fof(f107,plain,(
% 0.21/0.56    l1_struct_0(sK3)),
% 0.21/0.56    inference(resolution,[],[f63,f57])).
% 0.21/0.56  fof(f63,plain,(
% 0.21/0.56    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f15])).
% 0.21/0.56  fof(f15,plain,(
% 0.21/0.56    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.21/0.56  fof(f126,plain,(
% 0.21/0.56    ~l1_struct_0(sK3) | v2_struct_0(sK3) | ~spl9_4),
% 0.21/0.56    inference(resolution,[],[f119,f64])).
% 0.21/0.56  fof(f64,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f16])).
% 0.21/0.56  fof(f16,plain,(
% 0.21/0.56    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.56  fof(f119,plain,(
% 0.21/0.56    v1_xboole_0(u1_struct_0(sK3)) | ~spl9_4),
% 0.21/0.56    inference(avatar_component_clause,[],[f117])).
% 0.21/0.56  fof(f125,plain,(
% 0.21/0.56    spl9_5 | spl9_4),
% 0.21/0.56    inference(avatar_split_clause,[],[f111,f117,f122])).
% 0.21/0.56  fof(f111,plain,(
% 0.21/0.56    v1_xboole_0(u1_struct_0(sK3)) | r2_hidden(sK5,u1_struct_0(sK3))),
% 0.21/0.56    inference(resolution,[],[f67,f59])).
% 0.21/0.56  fof(f67,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f22])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.56    inference(flattening,[],[f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.56  fof(f104,plain,(
% 0.21/0.56    spl9_1 | spl9_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f60,f100,f96])).
% 0.21/0.56  fof(f60,plain,(
% 0.21/0.56    r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | r2_orders_2(sK3,sK4,sK5)),
% 0.21/0.56    inference(cnf_transformation,[],[f39])).
% 0.21/0.56  fof(f103,plain,(
% 0.21/0.56    ~spl9_1 | ~spl9_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f61,f100,f96])).
% 0.21/0.56  fof(f61,plain,(
% 0.21/0.56    ~r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | ~r2_orders_2(sK3,sK4,sK5)),
% 0.21/0.56    inference(cnf_transformation,[],[f39])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (20392)------------------------------
% 0.21/0.56  % (20392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (20392)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (20392)Memory used [KB]: 11001
% 0.21/0.56  % (20392)Time elapsed: 0.086 s
% 0.21/0.56  % (20392)------------------------------
% 0.21/0.56  % (20392)------------------------------
% 0.21/0.56  % (20385)Success in time 0.196 s
%------------------------------------------------------------------------------
