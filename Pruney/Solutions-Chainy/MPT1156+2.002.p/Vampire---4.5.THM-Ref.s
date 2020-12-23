%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:58 EST 2020

% Result     : Theorem 1.23s
% Output     : Refutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 134 expanded)
%              Number of leaves         :   11 (  39 expanded)
%              Depth                    :   19
%              Number of atoms          :  250 ( 742 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f111,plain,(
    $false ),
    inference(subsumption_resolution,[],[f110,f32])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
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
          ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
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
           => ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
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
         => ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_orders_2)).

fof(f110,plain,(
    v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f109,f54])).

fof(f54,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f40,f36])).

fof(f36,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f40,plain,(
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

fof(f109,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f104,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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

fof(f104,plain,(
    v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f103,f37])).

fof(f37,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f103,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f102,f55])).

fof(f55,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(resolution,[],[f49,f52])).

fof(f52,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f102,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(superposition,[],[f100,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f100,plain,
    ( ~ r2_hidden(sK1,k6_domain_1(u1_struct_0(sK0),sK1))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f99,f37])).

fof(f99,plain,
    ( ~ r2_hidden(sK1,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f98,f32])).

fof(f98,plain,
    ( ~ r2_hidden(sK1,k6_domain_1(u1_struct_0(sK0),sK1))
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f97,f33])).

% (1511)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f33,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f97,plain,
    ( ~ r2_hidden(sK1,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f96,f34])).

fof(f34,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f96,plain,
    ( ~ r2_hidden(sK1,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f95,f35])).

fof(f35,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f95,plain,
    ( ~ r2_hidden(sK1,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f92,f36])).

fof(f92,plain,
    ( ~ r2_hidden(sK1,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f65,f38])).

fof(f38,plain,(
    r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2)))
      | ~ r2_hidden(X0,k6_domain_1(u1_struct_0(X1),X2))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v1_xboole_0(u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f64,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k6_domain_1(X1,X0))
      | v1_xboole_0(X1)
      | m1_subset_1(X2,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f45,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k6_domain_1(u1_struct_0(X1),X2))
      | ~ r2_hidden(X0,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2)))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v1_xboole_0(u1_struct_0(X1)) ) ),
    inference(resolution,[],[f41,f45])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X1,k2_orders_2(X0,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k2_orders_2(X0,X2))
              | ~ r2_hidden(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k2_orders_2(X0,X2))
              | ~ r2_hidden(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( r2_hidden(X1,k2_orders_2(X0,X2))
                  & r2_hidden(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_orders_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:55:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.52  % (1512)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.53  % (1514)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.23/0.53  % (1506)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.23/0.53  % (1514)Refutation found. Thanks to Tanya!
% 1.23/0.53  % SZS status Theorem for theBenchmark
% 1.23/0.53  % (1506)Refutation not found, incomplete strategy% (1506)------------------------------
% 1.23/0.53  % (1506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.53  % (1506)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.53  
% 1.23/0.53  % (1506)Memory used [KB]: 1663
% 1.23/0.53  % (1506)Time elapsed: 0.079 s
% 1.23/0.53  % (1506)------------------------------
% 1.23/0.53  % (1506)------------------------------
% 1.23/0.53  % SZS output start Proof for theBenchmark
% 1.23/0.53  fof(f111,plain,(
% 1.23/0.53    $false),
% 1.23/0.53    inference(subsumption_resolution,[],[f110,f32])).
% 1.23/0.53  fof(f32,plain,(
% 1.23/0.53    ~v2_struct_0(sK0)),
% 1.23/0.53    inference(cnf_transformation,[],[f28])).
% 1.23/0.53  fof(f28,plain,(
% 1.23/0.53    (r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 1.23/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f27,f26])).
% 1.23/0.53  fof(f26,plain,(
% 1.23/0.53    ? [X0] : (? [X1] : (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 1.23/0.53    introduced(choice_axiom,[])).
% 1.23/0.53  fof(f27,plain,(
% 1.23/0.53    ? [X1] : (r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1))) & m1_subset_1(X1,u1_struct_0(sK0))) => (r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 1.23/0.53    introduced(choice_axiom,[])).
% 1.23/0.53  fof(f14,plain,(
% 1.23/0.53    ? [X0] : (? [X1] : (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.23/0.53    inference(flattening,[],[f13])).
% 1.23/0.53  fof(f13,plain,(
% 1.23/0.53    ? [X0] : (? [X1] : (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.23/0.53    inference(ennf_transformation,[],[f12])).
% 1.23/0.53  fof(f12,negated_conjecture,(
% 1.23/0.53    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 1.23/0.53    inference(negated_conjecture,[],[f11])).
% 1.23/0.53  fof(f11,conjecture,(
% 1.23/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 1.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_orders_2)).
% 1.23/0.53  fof(f110,plain,(
% 1.23/0.53    v2_struct_0(sK0)),
% 1.23/0.53    inference(subsumption_resolution,[],[f109,f54])).
% 1.23/0.53  fof(f54,plain,(
% 1.23/0.53    l1_struct_0(sK0)),
% 1.23/0.53    inference(resolution,[],[f40,f36])).
% 1.23/0.53  fof(f36,plain,(
% 1.23/0.53    l1_orders_2(sK0)),
% 1.23/0.53    inference(cnf_transformation,[],[f28])).
% 1.23/0.53  fof(f40,plain,(
% 1.23/0.53    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 1.23/0.53    inference(cnf_transformation,[],[f15])).
% 1.23/0.53  fof(f15,plain,(
% 1.23/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 1.23/0.53    inference(ennf_transformation,[],[f8])).
% 1.23/0.53  fof(f8,axiom,(
% 1.23/0.53    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 1.23/0.53  fof(f109,plain,(
% 1.23/0.53    ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 1.23/0.53    inference(resolution,[],[f104,f42])).
% 1.23/0.53  fof(f42,plain,(
% 1.23/0.53    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.23/0.53    inference(cnf_transformation,[],[f19])).
% 1.23/0.54  fof(f19,plain,(
% 1.23/0.54    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.23/0.54    inference(flattening,[],[f18])).
% 1.23/0.54  fof(f18,plain,(
% 1.23/0.54    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.23/0.54    inference(ennf_transformation,[],[f6])).
% 1.23/0.54  fof(f6,axiom,(
% 1.23/0.54    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.23/0.54  fof(f104,plain,(
% 1.23/0.54    v1_xboole_0(u1_struct_0(sK0))),
% 1.23/0.54    inference(subsumption_resolution,[],[f103,f37])).
% 1.23/0.54  fof(f37,plain,(
% 1.23/0.54    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.23/0.54    inference(cnf_transformation,[],[f28])).
% 1.23/0.54  fof(f103,plain,(
% 1.23/0.54    v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.23/0.54    inference(subsumption_resolution,[],[f102,f55])).
% 1.23/0.54  fof(f55,plain,(
% 1.23/0.54    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 1.23/0.54    inference(resolution,[],[f49,f52])).
% 1.23/0.54  fof(f52,plain,(
% 1.23/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.23/0.54    inference(equality_resolution,[],[f47])).
% 1.23/0.54  fof(f47,plain,(
% 1.23/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.23/0.54    inference(cnf_transformation,[],[f30])).
% 1.23/0.54  fof(f30,plain,(
% 1.23/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.23/0.54    inference(flattening,[],[f29])).
% 1.23/0.54  fof(f29,plain,(
% 1.23/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.23/0.54    inference(nnf_transformation,[],[f1])).
% 1.23/0.54  fof(f1,axiom,(
% 1.23/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.23/0.54  fof(f49,plain,(
% 1.23/0.54    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f31])).
% 1.23/0.54  fof(f31,plain,(
% 1.23/0.54    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.23/0.54    inference(nnf_transformation,[],[f4])).
% 1.23/0.54  fof(f4,axiom,(
% 1.23/0.54    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.23/0.54  fof(f102,plain,(
% 1.23/0.54    ~r2_hidden(sK1,k1_tarski(sK1)) | v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.23/0.54    inference(duplicate_literal_removal,[],[f101])).
% 1.23/0.54  fof(f101,plain,(
% 1.23/0.54    ~r2_hidden(sK1,k1_tarski(sK1)) | v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 1.23/0.54    inference(superposition,[],[f100,f44])).
% 1.23/0.54  fof(f44,plain,(
% 1.23/0.54    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f21])).
% 1.23/0.54  fof(f21,plain,(
% 1.23/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.23/0.54    inference(flattening,[],[f20])).
% 1.23/0.54  fof(f20,plain,(
% 1.23/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.23/0.54    inference(ennf_transformation,[],[f9])).
% 1.23/0.54  fof(f9,axiom,(
% 1.23/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.23/0.54  fof(f100,plain,(
% 1.23/0.54    ~r2_hidden(sK1,k6_domain_1(u1_struct_0(sK0),sK1)) | v1_xboole_0(u1_struct_0(sK0))),
% 1.23/0.54    inference(subsumption_resolution,[],[f99,f37])).
% 1.23/0.54  fof(f99,plain,(
% 1.23/0.54    ~r2_hidden(sK1,k6_domain_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 1.23/0.54    inference(subsumption_resolution,[],[f98,f32])).
% 1.23/0.54  fof(f98,plain,(
% 1.23/0.54    ~r2_hidden(sK1,k6_domain_1(u1_struct_0(sK0),sK1)) | v2_struct_0(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 1.23/0.54    inference(subsumption_resolution,[],[f97,f33])).
% 1.23/0.54  % (1511)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.23/0.54  fof(f33,plain,(
% 1.23/0.54    v3_orders_2(sK0)),
% 1.23/0.54    inference(cnf_transformation,[],[f28])).
% 1.23/0.54  fof(f97,plain,(
% 1.23/0.54    ~r2_hidden(sK1,k6_domain_1(u1_struct_0(sK0),sK1)) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 1.23/0.54    inference(subsumption_resolution,[],[f96,f34])).
% 1.23/0.54  fof(f34,plain,(
% 1.23/0.54    v4_orders_2(sK0)),
% 1.23/0.54    inference(cnf_transformation,[],[f28])).
% 1.23/0.54  fof(f96,plain,(
% 1.23/0.54    ~r2_hidden(sK1,k6_domain_1(u1_struct_0(sK0),sK1)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 1.23/0.54    inference(subsumption_resolution,[],[f95,f35])).
% 1.23/0.54  fof(f35,plain,(
% 1.23/0.54    v5_orders_2(sK0)),
% 1.23/0.54    inference(cnf_transformation,[],[f28])).
% 1.23/0.54  fof(f95,plain,(
% 1.23/0.54    ~r2_hidden(sK1,k6_domain_1(u1_struct_0(sK0),sK1)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 1.23/0.54    inference(subsumption_resolution,[],[f92,f36])).
% 1.23/0.54  fof(f92,plain,(
% 1.23/0.54    ~r2_hidden(sK1,k6_domain_1(u1_struct_0(sK0),sK1)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0))),
% 1.23/0.54    inference(resolution,[],[f65,f38])).
% 1.23/0.54  fof(f38,plain,(
% 1.23/0.54    r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))),
% 1.23/0.54    inference(cnf_transformation,[],[f28])).
% 1.23/0.54  fof(f65,plain,(
% 1.23/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2))) | ~r2_hidden(X0,k6_domain_1(u1_struct_0(X1),X2)) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | v1_xboole_0(u1_struct_0(X1))) )),
% 1.23/0.54    inference(subsumption_resolution,[],[f64,f61])).
% 1.23/0.54  fof(f61,plain,(
% 1.23/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,k6_domain_1(X1,X0)) | v1_xboole_0(X1) | m1_subset_1(X2,X1) | ~m1_subset_1(X0,X1)) )),
% 1.23/0.54    inference(resolution,[],[f45,f51])).
% 1.23/0.54  fof(f51,plain,(
% 1.23/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f25])).
% 1.23/0.54  fof(f25,plain,(
% 1.23/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.23/0.54    inference(flattening,[],[f24])).
% 1.23/0.54  fof(f24,plain,(
% 1.23/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.23/0.54    inference(ennf_transformation,[],[f5])).
% 1.23/0.54  fof(f5,axiom,(
% 1.23/0.54    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 1.23/0.54  fof(f45,plain,(
% 1.23/0.54    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f23])).
% 1.23/0.54  fof(f23,plain,(
% 1.23/0.54    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.23/0.54    inference(flattening,[],[f22])).
% 1.23/0.54  fof(f22,plain,(
% 1.23/0.54    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.23/0.54    inference(ennf_transformation,[],[f7])).
% 1.23/0.54  fof(f7,axiom,(
% 1.23/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 1.23/0.54  fof(f64,plain,(
% 1.23/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,k6_domain_1(u1_struct_0(X1),X2)) | ~r2_hidden(X0,k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2))) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | v1_xboole_0(u1_struct_0(X1))) )),
% 1.23/0.54    inference(resolution,[],[f41,f45])).
% 1.23/0.54  fof(f41,plain,(
% 1.23/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~r2_hidden(X1,k2_orders_2(X0,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f17])).
% 1.23/0.54  fof(f17,plain,(
% 1.23/0.54    ! [X0] : (! [X1] : (! [X2] : (~r2_hidden(X1,k2_orders_2(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.23/0.54    inference(flattening,[],[f16])).
% 1.23/0.54  fof(f16,plain,(
% 1.23/0.54    ! [X0] : (! [X1] : (! [X2] : ((~r2_hidden(X1,k2_orders_2(X0,X2)) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.23/0.54    inference(ennf_transformation,[],[f10])).
% 1.23/0.54  fof(f10,axiom,(
% 1.23/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r2_hidden(X1,k2_orders_2(X0,X2)) & r2_hidden(X1,X2)))))),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_orders_2)).
% 1.23/0.54  % SZS output end Proof for theBenchmark
% 1.23/0.54  % (1514)------------------------------
% 1.23/0.54  % (1514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.54  % (1514)Termination reason: Refutation
% 1.23/0.54  
% 1.23/0.54  % (1514)Memory used [KB]: 1791
% 1.23/0.54  % (1514)Time elapsed: 0.078 s
% 1.23/0.54  % (1514)------------------------------
% 1.23/0.54  % (1514)------------------------------
% 1.23/0.54  % (1504)Success in time 0.166 s
%------------------------------------------------------------------------------
