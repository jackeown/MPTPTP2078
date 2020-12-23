%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  122 (1690 expanded)
%              Number of leaves         :   17 ( 538 expanded)
%              Depth                    :   29
%              Number of atoms          :  606 (14611 expanded)
%              Number of equality atoms :   74 ( 255 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f222,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f155,f221])).

fof(f221,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_contradiction_clause,[],[f220])).

fof(f220,plain,
    ( $false
    | ~ spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f219,f158])).

fof(f158,plain,
    ( ~ r2_hidden(sK1,k2_orders_2(sK0,k2_tarski(sK2,sK2)))
    | spl6_2 ),
    inference(forward_demodulation,[],[f95,f105])).

fof(f105,plain,(
    k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2) ),
    inference(resolution,[],[f98,f46])).

fof(f46,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ~ r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      | ~ r2_orders_2(sK0,sK1,sK2) )
    & ( r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      | r2_orders_2(sK0,sK1,sK2) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).

fof(f27,plain,
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
              ( ( ~ r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
                | ~ r2_orders_2(sK0,X1,X2) )
              & ( r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
                | r2_orders_2(sK0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
              | ~ r2_orders_2(sK0,X1,X2) )
            & ( r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
              | r2_orders_2(sK0,X1,X2) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ~ r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
            | ~ r2_orders_2(sK0,sK1,X2) )
          & ( r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
            | r2_orders_2(sK0,sK1,X2) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( ( ~ r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
          | ~ r2_orders_2(sK0,sK1,X2) )
        & ( r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
          | r2_orders_2(sK0,sK1,X2) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ~ r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
        | ~ r2_orders_2(sK0,sK1,sK2) )
      & ( r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
        | r2_orders_2(sK0,sK1,sK2) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f13])).

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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_orders_2)).

fof(f98,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(sK0),X0) ) ),
    inference(resolution,[],[f88,f69])).

% (15722)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% (15714)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% (15727)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% (15722)Refutation not found, incomplete strategy% (15722)------------------------------
% (15722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15719)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% (15710)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% (15732)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% (15722)Termination reason: Refutation not found, incomplete strategy

% (15722)Memory used [KB]: 1791
% (15722)Time elapsed: 0.098 s
% (15722)------------------------------
% (15722)------------------------------
% (15733)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% (15731)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% (15733)Refutation not found, incomplete strategy% (15733)------------------------------
% (15733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15733)Termination reason: Refutation not found, incomplete strategy

% (15733)Memory used [KB]: 1663
% (15733)Time elapsed: 0.002 s
% (15733)------------------------------
% (15733)------------------------------
% (15708)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% (15707)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% (15705)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% (15714)Refutation not found, incomplete strategy% (15714)------------------------------
% (15714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15714)Termination reason: Refutation not found, incomplete strategy

% (15714)Memory used [KB]: 10746
% (15714)Time elapsed: 0.098 s
% (15714)------------------------------
% (15714)------------------------------
% (15708)Refutation not found, incomplete strategy% (15708)------------------------------
% (15708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15708)Termination reason: Refutation not found, incomplete strategy

% (15708)Memory used [KB]: 1918
% (15708)Time elapsed: 0.132 s
% (15708)------------------------------
% (15708)------------------------------
fof(f69,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1) ) ),
    inference(definition_unfolding,[],[f60,f64])).

fof(f64,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f88,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f76,f87])).

fof(f87,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f44,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f44,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f76,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f40,f62])).

fof(f62,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f40,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f95,plain,
    ( ~ r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl6_2
  <=> r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f219,plain,
    ( r2_hidden(sK1,k2_orders_2(sK0,k2_tarski(sK2,sK2)))
    | ~ spl6_1
    | spl6_2 ),
    inference(forward_demodulation,[],[f218,f137])).

fof(f137,plain,(
    k2_orders_2(sK0,k2_tarski(sK2,sK2)) = a_2_1_orders_2(sK0,k2_tarski(sK2,sK2)) ),
    inference(resolution,[],[f134,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) ) ),
    inference(global_subsumption,[],[f44,f43,f42,f41,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0) ) ),
    inference(resolution,[],[f40,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).

fof(f41,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f42,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f43,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f134,plain,(
    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f133,f40])).

fof(f133,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f132,f41])).

fof(f132,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f131,f44])).

fof(f131,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f130,f46])).

fof(f130,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f61,f105])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).

fof(f218,plain,
    ( r2_hidden(sK1,a_2_1_orders_2(sK0,k2_tarski(sK2,sK2)))
    | ~ spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f217,f45])).

fof(f45,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f217,plain,
    ( r2_hidden(sK1,a_2_1_orders_2(sK0,k2_tarski(sK2,sK2)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f216,f134])).

fof(f216,plain,
    ( r2_hidden(sK1,a_2_1_orders_2(sK0,k2_tarski(sK2,sK2)))
    | ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f213,f92])).

fof(f92,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl6_1
  <=> r2_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f213,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK1,a_2_1_orders_2(sK0,k2_tarski(sK2,sK2)))
    | ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl6_2 ),
    inference(superposition,[],[f86,f208])).

fof(f208,plain,
    ( sK2 = sK3(sK0,k2_tarski(sK2,sK2),sK1)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f206,f45])).

fof(f206,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | sK2 = sK3(sK0,k2_tarski(sK2,sK2),sK1)
    | spl6_2 ),
    inference(resolution,[],[f200,f158])).

fof(f200,plain,(
    ! [X1] :
      ( r2_hidden(X1,k2_orders_2(sK0,k2_tarski(sK2,sK2)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | sK2 = sK3(sK0,k2_tarski(sK2,sK2),X1) ) ),
    inference(subsumption_resolution,[],[f197,f134])).

fof(f197,plain,(
    ! [X1] :
      ( r2_hidden(X1,k2_orders_2(sK0,k2_tarski(sK2,sK2)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | sK2 = sK3(sK0,k2_tarski(sK2,sK2),X1) ) ),
    inference(superposition,[],[f135,f137])).

fof(f135,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,a_2_1_orders_2(sK0,k2_tarski(X0,X0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | sK3(sK0,k2_tarski(X0,X0),X1) = X0 ) ),
    inference(resolution,[],[f85,f75])).

fof(f75,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f55,f64])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f85,plain,(
    ! [X6,X7] :
      ( r2_hidden(sK3(sK0,X6,X7),X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | r2_hidden(X7,a_2_1_orders_2(sK0,X6)) ) ),
    inference(global_subsumption,[],[f44,f43,f42,f41,f80])).

fof(f80,plain,(
    ! [X6,X7] :
      ( r2_hidden(sK3(sK0,X6,X7),X6)
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | r2_hidden(X7,a_2_1_orders_2(sK0,X6)) ) ),
    inference(resolution,[],[f40,f71])).

fof(f71,plain,(
    ! [X2,X3,X1] :
      ( v2_struct_0(X1)
      | r2_hidden(sK3(X1,X2,X3),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | r2_hidden(X3,a_2_1_orders_2(X1,X2)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | r2_hidden(sK3(X1,X2,X3),X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ( ~ r2_orders_2(X1,X3,sK3(X1,X2,X3))
                & r2_hidden(sK3(X1,X2,X3),X2)
                & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r2_orders_2(X1,sK4(X0,X1,X2),X6)
                | ~ r2_hidden(X6,X2)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & sK4(X0,X1,X2) = X0
            & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f32,f34,f33])).

fof(f33,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X3,X4)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X3,sK3(X1,X2,X3))
        & r2_hidden(sK3(X1,X2,X3),X2)
        & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X1,X5,X6)
              | ~ r2_hidden(X6,X2)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_orders_2(X1,sK4(X0,X1,X2),X6)
            | ~ r2_hidden(X6,X2)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & sK4(X0,X1,X2) = X0
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X3,X4)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ! [X6] :
                  ( r2_orders_2(X1,X5,X6)
                  | ~ r2_hidden(X6,X2)
                  | ~ m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
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
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

fof(f86,plain,(
    ! [X8,X9] :
      ( ~ r2_orders_2(sK0,X8,sK3(sK0,X9,X8))
      | r2_hidden(X8,a_2_1_orders_2(sK0,X9))
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X8,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f44,f43,f42,f41,f81])).

fof(f81,plain,(
    ! [X8,X9] :
      ( ~ r2_orders_2(sK0,X8,sK3(sK0,X9,X8))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | r2_hidden(X8,a_2_1_orders_2(sK0,X9)) ) ),
    inference(resolution,[],[f40,f70])).

fof(f70,plain,(
    ! [X2,X3,X1] :
      ( v2_struct_0(X1)
      | ~ r2_orders_2(X1,X3,sK3(X1,X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | r2_hidden(X3,a_2_1_orders_2(X1,X2)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ r2_orders_2(X1,X3,sK3(X1,X2,X3))
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f155,plain,(
    ~ spl6_2 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f153,f74])).

fof(f74,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f56,f64])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f153,plain,
    ( ~ r2_hidden(sK2,k2_tarski(sK2,sK2))
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f151,f46])).

fof(f151,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_hidden(sK2,k2_tarski(sK2,sK2))
    | ~ spl6_2 ),
    inference(resolution,[],[f150,f99])).

fof(f99,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f48,f96])).

fof(f96,plain,
    ( r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f48,plain,
    ( ~ r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | ~ r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f150,plain,
    ( ! [X0] :
        ( r2_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k2_tarski(sK2,sK2)) )
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f149,f129])).

fof(f129,plain,
    ( r2_hidden(sK1,k2_orders_2(sK0,k2_tarski(sK2,sK2)))
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f96,f105])).

fof(f149,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,k2_orders_2(sK0,k2_tarski(sK2,sK2)))
        | r2_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k2_tarski(sK2,sK2)) )
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f148,f137])).

fof(f148,plain,
    ( ! [X0] :
        ( r2_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k2_tarski(sK2,sK2))
        | ~ r2_hidden(sK1,a_2_1_orders_2(sK0,k2_tarski(sK2,sK2))) )
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f146,f134])).

fof(f146,plain,
    ( ! [X0] :
        ( r2_orders_2(sK0,sK1,X0)
        | ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k2_tarski(sK2,sK2))
        | ~ r2_hidden(sK1,a_2_1_orders_2(sK0,k2_tarski(sK2,sK2))) )
    | ~ spl6_2 ),
    inference(superposition,[],[f84,f143])).

fof(f143,plain,
    ( sK1 = sK4(sK1,sK0,k2_tarski(sK2,sK2))
    | ~ spl6_2 ),
    inference(resolution,[],[f139,f129])).

fof(f139,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_orders_2(sK0,k2_tarski(sK2,sK2)))
      | sK4(X0,sK0,k2_tarski(sK2,sK2)) = X0 ) ),
    inference(forward_demodulation,[],[f136,f137])).

fof(f136,plain,(
    ! [X0] :
      ( sK4(X0,sK0,k2_tarski(sK2,sK2)) = X0
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,k2_tarski(sK2,sK2))) ) ),
    inference(resolution,[],[f134,f83])).

fof(f83,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK4(X1,sK0,X2) = X1
      | ~ r2_hidden(X1,a_2_1_orders_2(sK0,X2)) ) ),
    inference(global_subsumption,[],[f44,f43,f42,f41,f78])).

fof(f78,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,a_2_1_orders_2(sK0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | sK4(X1,sK0,X2) = X1 ) ),
    inference(resolution,[],[f40,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X1)
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | sK4(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f84,plain,(
    ! [X4,X5,X3] :
      ( r2_orders_2(sK0,sK4(X5,sK0,X4),X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(X3,X4)
      | ~ r2_hidden(X5,a_2_1_orders_2(sK0,X4)) ) ),
    inference(global_subsumption,[],[f44,f43,f42,f41,f79])).

fof(f79,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,X4)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(X5,a_2_1_orders_2(sK0,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | r2_orders_2(sK0,sK4(X5,sK0,X4),X3) ) ),
    inference(resolution,[],[f40,f51])).

fof(f51,plain,(
    ! [X6,X2,X0,X1] :
      ( v2_struct_0(X1)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | r2_orders_2(X1,sK4(X0,X1,X2),X6) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f97,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f47,f94,f90])).

fof(f47,plain,
    ( r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:03:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (15704)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.51  % (15712)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.52  % (15709)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (15713)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (15728)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.53  % (15728)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f222,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f97,f155,f221])).
% 0.22/0.53  fof(f221,plain,(
% 0.22/0.53    ~spl6_1 | spl6_2),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f220])).
% 0.22/0.53  fof(f220,plain,(
% 0.22/0.53    $false | (~spl6_1 | spl6_2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f219,f158])).
% 0.22/0.53  fof(f158,plain,(
% 0.22/0.53    ~r2_hidden(sK1,k2_orders_2(sK0,k2_tarski(sK2,sK2))) | spl6_2),
% 0.22/0.53    inference(forward_demodulation,[],[f95,f105])).
% 0.22/0.53  fof(f105,plain,(
% 0.22/0.53    k6_domain_1(u1_struct_0(sK0),sK2) = k2_tarski(sK2,sK2)),
% 0.22/0.53    inference(resolution,[],[f98,f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.53    inference(cnf_transformation,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    (((~r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | ~r2_orders_2(sK0,sK1,sK2)) & (r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | r2_orders_2(sK0,sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | ~r2_orders_2(sK0,X1,X2)) & (r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | r2_orders_2(sK0,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | ~r2_orders_2(sK0,X1,X2)) & (r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | r2_orders_2(sK0,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : ((~r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | ~r2_orders_2(sK0,sK1,X2)) & (r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | r2_orders_2(sK0,sK1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ? [X2] : ((~r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | ~r2_orders_2(sK0,sK1,X2)) & (r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | r2_orders_2(sK0,sK1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) => ((~r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | ~r2_orders_2(sK0,sK1,sK2)) & (r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | r2_orders_2(sK0,sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 0.22/0.53    inference(negated_conjecture,[],[f9])).
% 0.22/0.53  fof(f9,conjecture,(
% 0.22/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_orders_2)).
% 0.22/0.53  fof(f98,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(sK0),X0)) )),
% 0.22/0.53    inference(resolution,[],[f88,f69])).
% 0.22/0.53  % (15722)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.54  % (15714)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.54  % (15727)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (15722)Refutation not found, incomplete strategy% (15722)------------------------------
% 0.22/0.54  % (15722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (15719)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (15710)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (15732)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (15722)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (15722)Memory used [KB]: 1791
% 0.22/0.54  % (15722)Time elapsed: 0.098 s
% 0.22/0.54  % (15722)------------------------------
% 0.22/0.54  % (15722)------------------------------
% 0.22/0.54  % (15733)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (15731)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (15733)Refutation not found, incomplete strategy% (15733)------------------------------
% 0.22/0.54  % (15733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (15733)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (15733)Memory used [KB]: 1663
% 0.22/0.54  % (15733)Time elapsed: 0.002 s
% 0.22/0.54  % (15733)------------------------------
% 0.22/0.54  % (15733)------------------------------
% 0.22/0.54  % (15708)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (15707)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (15705)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (15714)Refutation not found, incomplete strategy% (15714)------------------------------
% 0.22/0.54  % (15714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (15714)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (15714)Memory used [KB]: 10746
% 0.22/0.54  % (15714)Time elapsed: 0.098 s
% 0.22/0.54  % (15714)------------------------------
% 0.22/0.54  % (15714)------------------------------
% 0.22/0.55  % (15708)Refutation not found, incomplete strategy% (15708)------------------------------
% 0.22/0.55  % (15708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (15708)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (15708)Memory used [KB]: 1918
% 0.22/0.55  % (15708)Time elapsed: 0.132 s
% 0.22/0.55  % (15708)------------------------------
% 0.22/0.55  % (15708)------------------------------
% 0.22/0.55  fof(f69,plain,(
% 0.22/0.55    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1)) )),
% 0.22/0.55    inference(definition_unfolding,[],[f60,f64])).
% 0.22/0.55  fof(f64,plain,(
% 0.22/0.55    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.55  fof(f60,plain,(
% 0.22/0.55    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.55    inference(flattening,[],[f18])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.55  fof(f88,plain,(
% 0.22/0.55    ~v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.55    inference(subsumption_resolution,[],[f76,f87])).
% 0.22/0.55  fof(f87,plain,(
% 0.22/0.55    l1_struct_0(sK0)),
% 0.22/0.55    inference(resolution,[],[f44,f63])).
% 0.22/0.55  fof(f63,plain,(
% 0.22/0.55    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f24])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    l1_orders_2(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  fof(f76,plain,(
% 0.22/0.55    ~l1_struct_0(sK0) | ~v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.55    inference(resolution,[],[f40,f62])).
% 0.22/0.55  fof(f62,plain,(
% 0.22/0.55    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.55    inference(flattening,[],[f22])).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    ~v2_struct_0(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  fof(f95,plain,(
% 0.22/0.55    ~r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | spl6_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f94])).
% 0.22/0.55  fof(f94,plain,(
% 0.22/0.55    spl6_2 <=> r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.55  fof(f219,plain,(
% 0.22/0.55    r2_hidden(sK1,k2_orders_2(sK0,k2_tarski(sK2,sK2))) | (~spl6_1 | spl6_2)),
% 0.22/0.55    inference(forward_demodulation,[],[f218,f137])).
% 0.22/0.55  fof(f137,plain,(
% 0.22/0.55    k2_orders_2(sK0,k2_tarski(sK2,sK2)) = a_2_1_orders_2(sK0,k2_tarski(sK2,sK2))),
% 0.22/0.55    inference(resolution,[],[f134,f82])).
% 0.22/0.55  fof(f82,plain,(
% 0.22/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)) )),
% 0.22/0.55    inference(global_subsumption,[],[f44,f43,f42,f41,f77])).
% 0.22/0.55  fof(f77,plain,(
% 0.22/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | k2_orders_2(sK0,X0) = a_2_1_orders_2(sK0,X0)) )),
% 0.22/0.55    inference(resolution,[],[f40,f59])).
% 0.22/0.55  fof(f59,plain,(
% 0.22/0.55    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.55    inference(flattening,[],[f16])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    v3_orders_2(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    v4_orders_2(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  fof(f43,plain,(
% 0.22/0.55    v5_orders_2(sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  fof(f134,plain,(
% 0.22/0.55    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.55    inference(subsumption_resolution,[],[f133,f40])).
% 0.22/0.55  fof(f133,plain,(
% 0.22/0.55    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.22/0.55    inference(subsumption_resolution,[],[f132,f41])).
% 0.22/0.55  fof(f132,plain,(
% 0.22/0.55    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.55    inference(subsumption_resolution,[],[f131,f44])).
% 0.22/0.55  fof(f131,plain,(
% 0.22/0.55    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.55    inference(subsumption_resolution,[],[f130,f46])).
% 0.22/0.55  fof(f130,plain,(
% 0.22/0.55    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.55    inference(superposition,[],[f61,f105])).
% 0.22/0.55  fof(f61,plain,(
% 0.22/0.55    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f21])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.55    inference(flattening,[],[f20])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,plain,(
% 0.22/0.55    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.55    inference(pure_predicate_removal,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).
% 0.22/0.55  fof(f218,plain,(
% 0.22/0.55    r2_hidden(sK1,a_2_1_orders_2(sK0,k2_tarski(sK2,sK2))) | (~spl6_1 | spl6_2)),
% 0.22/0.55    inference(subsumption_resolution,[],[f217,f45])).
% 0.22/0.55  fof(f45,plain,(
% 0.22/0.55    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  fof(f217,plain,(
% 0.22/0.55    r2_hidden(sK1,a_2_1_orders_2(sK0,k2_tarski(sK2,sK2))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl6_1 | spl6_2)),
% 0.22/0.55    inference(subsumption_resolution,[],[f216,f134])).
% 0.22/0.55  fof(f216,plain,(
% 0.22/0.55    r2_hidden(sK1,a_2_1_orders_2(sK0,k2_tarski(sK2,sK2))) | ~m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl6_1 | spl6_2)),
% 0.22/0.55    inference(subsumption_resolution,[],[f213,f92])).
% 0.22/0.55  fof(f92,plain,(
% 0.22/0.55    r2_orders_2(sK0,sK1,sK2) | ~spl6_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f90])).
% 0.22/0.55  fof(f90,plain,(
% 0.22/0.55    spl6_1 <=> r2_orders_2(sK0,sK1,sK2)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.55  fof(f213,plain,(
% 0.22/0.55    ~r2_orders_2(sK0,sK1,sK2) | r2_hidden(sK1,a_2_1_orders_2(sK0,k2_tarski(sK2,sK2))) | ~m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | spl6_2),
% 0.22/0.55    inference(superposition,[],[f86,f208])).
% 0.22/0.55  fof(f208,plain,(
% 0.22/0.55    sK2 = sK3(sK0,k2_tarski(sK2,sK2),sK1) | spl6_2),
% 0.22/0.55    inference(subsumption_resolution,[],[f206,f45])).
% 0.22/0.55  fof(f206,plain,(
% 0.22/0.55    ~m1_subset_1(sK1,u1_struct_0(sK0)) | sK2 = sK3(sK0,k2_tarski(sK2,sK2),sK1) | spl6_2),
% 0.22/0.55    inference(resolution,[],[f200,f158])).
% 0.22/0.55  fof(f200,plain,(
% 0.22/0.55    ( ! [X1] : (r2_hidden(X1,k2_orders_2(sK0,k2_tarski(sK2,sK2))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | sK2 = sK3(sK0,k2_tarski(sK2,sK2),X1)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f197,f134])).
% 0.22/0.55  fof(f197,plain,(
% 0.22/0.55    ( ! [X1] : (r2_hidden(X1,k2_orders_2(sK0,k2_tarski(sK2,sK2))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | sK2 = sK3(sK0,k2_tarski(sK2,sK2),X1)) )),
% 0.22/0.55    inference(superposition,[],[f135,f137])).
% 0.22/0.55  fof(f135,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r2_hidden(X1,a_2_1_orders_2(sK0,k2_tarski(X0,X0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(k2_tarski(X0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | sK3(sK0,k2_tarski(X0,X0),X1) = X0) )),
% 0.22/0.55    inference(resolution,[],[f85,f75])).
% 0.22/0.55  fof(f75,plain,(
% 0.22/0.55    ( ! [X0,X3] : (~r2_hidden(X3,k2_tarski(X0,X0)) | X0 = X3) )),
% 0.22/0.55    inference(equality_resolution,[],[f68])).
% 0.22/0.55  fof(f68,plain,(
% 0.22/0.55    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 0.22/0.55    inference(definition_unfolding,[],[f55,f64])).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f39])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.55    inference(rectify,[],[f36])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.55    inference(nnf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.55  fof(f85,plain,(
% 0.22/0.55    ( ! [X6,X7] : (r2_hidden(sK3(sK0,X6,X7),X6) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X7,u1_struct_0(sK0)) | r2_hidden(X7,a_2_1_orders_2(sK0,X6))) )),
% 0.22/0.55    inference(global_subsumption,[],[f44,f43,f42,f41,f80])).
% 0.22/0.55  fof(f80,plain,(
% 0.22/0.55    ( ! [X6,X7] : (r2_hidden(sK3(sK0,X6,X7),X6) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | r2_hidden(X7,a_2_1_orders_2(sK0,X6))) )),
% 0.22/0.55    inference(resolution,[],[f40,f71])).
% 0.22/0.55  fof(f71,plain,(
% 0.22/0.55    ( ! [X2,X3,X1] : (v2_struct_0(X1) | r2_hidden(sK3(X1,X2,X3),X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | r2_hidden(X3,a_2_1_orders_2(X1,X2))) )),
% 0.22/0.55    inference(equality_resolution,[],[f53])).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_1_orders_2(X1,X2)) | r2_hidden(sK3(X1,X2,X3),X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f35])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,X3,sK3(X1,X2,X3)) & r2_hidden(sK3(X1,X2,X3),X2) & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,sK4(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK4(X0,X1,X2) = X0 & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f32,f34,f33])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,X3,sK3(X1,X2,X3)) & r2_hidden(sK3(X1,X2,X3),X2) & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1))))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,sK4(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK4(X0,X1,X2) = X0 & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.22/0.55    inference(rectify,[],[f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.22/0.55    inference(nnf_transformation,[],[f15])).
% 0.22/0.55  fof(f15,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.22/0.55    inference(flattening,[],[f14])).
% 0.22/0.55  fof(f14,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).
% 0.22/0.55  fof(f86,plain,(
% 0.22/0.55    ( ! [X8,X9] : (~r2_orders_2(sK0,X8,sK3(sK0,X9,X8)) | r2_hidden(X8,a_2_1_orders_2(sK0,X9)) | ~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X8,u1_struct_0(sK0))) )),
% 0.22/0.55    inference(global_subsumption,[],[f44,f43,f42,f41,f81])).
% 0.22/0.55  fof(f81,plain,(
% 0.22/0.55    ( ! [X8,X9] : (~r2_orders_2(sK0,X8,sK3(sK0,X9,X8)) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | r2_hidden(X8,a_2_1_orders_2(sK0,X9))) )),
% 0.22/0.55    inference(resolution,[],[f40,f70])).
% 0.22/0.55  fof(f70,plain,(
% 0.22/0.55    ( ! [X2,X3,X1] : (v2_struct_0(X1) | ~r2_orders_2(X1,X3,sK3(X1,X2,X3)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | r2_hidden(X3,a_2_1_orders_2(X1,X2))) )),
% 0.22/0.55    inference(equality_resolution,[],[f54])).
% 0.22/0.55  fof(f54,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~r2_orders_2(X1,X3,sK3(X1,X2,X3)) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f35])).
% 0.22/0.55  fof(f155,plain,(
% 0.22/0.55    ~spl6_2),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f154])).
% 0.22/0.55  fof(f154,plain,(
% 0.22/0.55    $false | ~spl6_2),
% 0.22/0.55    inference(subsumption_resolution,[],[f153,f74])).
% 0.22/0.55  fof(f74,plain,(
% 0.22/0.55    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 0.22/0.55    inference(equality_resolution,[],[f73])).
% 0.22/0.55  fof(f73,plain,(
% 0.22/0.55    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 0.22/0.55    inference(equality_resolution,[],[f67])).
% 0.22/0.55  fof(f67,plain,(
% 0.22/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 0.22/0.55    inference(definition_unfolding,[],[f56,f64])).
% 0.22/0.55  fof(f56,plain,(
% 0.22/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.22/0.55    inference(cnf_transformation,[],[f39])).
% 0.22/0.55  fof(f153,plain,(
% 0.22/0.55    ~r2_hidden(sK2,k2_tarski(sK2,sK2)) | ~spl6_2),
% 0.22/0.55    inference(subsumption_resolution,[],[f151,f46])).
% 0.22/0.55  fof(f151,plain,(
% 0.22/0.55    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~r2_hidden(sK2,k2_tarski(sK2,sK2)) | ~spl6_2),
% 0.22/0.55    inference(resolution,[],[f150,f99])).
% 0.22/0.55  fof(f99,plain,(
% 0.22/0.55    ~r2_orders_2(sK0,sK1,sK2) | ~spl6_2),
% 0.22/0.55    inference(subsumption_resolution,[],[f48,f96])).
% 0.22/0.55  fof(f96,plain,(
% 0.22/0.55    r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | ~spl6_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f94])).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    ~r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | ~r2_orders_2(sK0,sK1,sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  fof(f150,plain,(
% 0.22/0.55    ( ! [X0] : (r2_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k2_tarski(sK2,sK2))) ) | ~spl6_2),
% 0.22/0.55    inference(subsumption_resolution,[],[f149,f129])).
% 0.22/0.55  fof(f129,plain,(
% 0.22/0.55    r2_hidden(sK1,k2_orders_2(sK0,k2_tarski(sK2,sK2))) | ~spl6_2),
% 0.22/0.55    inference(backward_demodulation,[],[f96,f105])).
% 0.22/0.55  fof(f149,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(sK1,k2_orders_2(sK0,k2_tarski(sK2,sK2))) | r2_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k2_tarski(sK2,sK2))) ) | ~spl6_2),
% 0.22/0.55    inference(forward_demodulation,[],[f148,f137])).
% 0.22/0.55  fof(f148,plain,(
% 0.22/0.55    ( ! [X0] : (r2_orders_2(sK0,sK1,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k2_tarski(sK2,sK2)) | ~r2_hidden(sK1,a_2_1_orders_2(sK0,k2_tarski(sK2,sK2)))) ) | ~spl6_2),
% 0.22/0.55    inference(subsumption_resolution,[],[f146,f134])).
% 0.22/0.55  fof(f146,plain,(
% 0.22/0.55    ( ! [X0] : (r2_orders_2(sK0,sK1,X0) | ~m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k2_tarski(sK2,sK2)) | ~r2_hidden(sK1,a_2_1_orders_2(sK0,k2_tarski(sK2,sK2)))) ) | ~spl6_2),
% 0.22/0.55    inference(superposition,[],[f84,f143])).
% 0.22/0.55  fof(f143,plain,(
% 0.22/0.55    sK1 = sK4(sK1,sK0,k2_tarski(sK2,sK2)) | ~spl6_2),
% 0.22/0.55    inference(resolution,[],[f139,f129])).
% 0.22/0.55  fof(f139,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,k2_orders_2(sK0,k2_tarski(sK2,sK2))) | sK4(X0,sK0,k2_tarski(sK2,sK2)) = X0) )),
% 0.22/0.55    inference(forward_demodulation,[],[f136,f137])).
% 0.22/0.55  fof(f136,plain,(
% 0.22/0.55    ( ! [X0] : (sK4(X0,sK0,k2_tarski(sK2,sK2)) = X0 | ~r2_hidden(X0,a_2_1_orders_2(sK0,k2_tarski(sK2,sK2)))) )),
% 0.22/0.55    inference(resolution,[],[f134,f83])).
% 0.22/0.55  fof(f83,plain,(
% 0.22/0.55    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | sK4(X1,sK0,X2) = X1 | ~r2_hidden(X1,a_2_1_orders_2(sK0,X2))) )),
% 0.22/0.55    inference(global_subsumption,[],[f44,f43,f42,f41,f78])).
% 0.22/0.55  fof(f78,plain,(
% 0.22/0.55    ( ! [X2,X1] : (~r2_hidden(X1,a_2_1_orders_2(sK0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | sK4(X1,sK0,X2) = X1) )),
% 0.22/0.55    inference(resolution,[],[f40,f50])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (v2_struct_0(X1) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | sK4(X0,X1,X2) = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f35])).
% 0.22/0.55  fof(f84,plain,(
% 0.22/0.55    ( ! [X4,X5,X3] : (r2_orders_2(sK0,sK4(X5,sK0,X4),X3) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X3,X4) | ~r2_hidden(X5,a_2_1_orders_2(sK0,X4))) )),
% 0.22/0.55    inference(global_subsumption,[],[f44,f43,f42,f41,f79])).
% 0.22/0.55  fof(f79,plain,(
% 0.22/0.55    ( ! [X4,X5,X3] : (~r2_hidden(X3,X4) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X5,a_2_1_orders_2(sK0,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | r2_orders_2(sK0,sK4(X5,sK0,X4),X3)) )),
% 0.22/0.55    inference(resolution,[],[f40,f51])).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    ( ! [X6,X2,X0,X1] : (v2_struct_0(X1) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | r2_orders_2(X1,sK4(X0,X1,X2),X6)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f35])).
% 0.22/0.55  fof(f97,plain,(
% 0.22/0.55    spl6_1 | spl6_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f47,f94,f90])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | r2_orders_2(sK0,sK1,sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (15728)------------------------------
% 0.22/0.55  % (15728)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (15728)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (15728)Memory used [KB]: 10874
% 0.22/0.55  % (15728)Time elapsed: 0.122 s
% 0.22/0.55  % (15728)------------------------------
% 0.22/0.55  % (15728)------------------------------
% 0.22/0.55  % (15706)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.55  % (15703)Success in time 0.183 s
%------------------------------------------------------------------------------
