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
% DateTime   : Thu Dec  3 13:16:35 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 288 expanded)
%              Number of leaves         :   17 (  72 expanded)
%              Depth                    :   44
%              Number of atoms          :  487 ( 990 expanded)
%              Number of equality atoms :   30 ( 126 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f220,plain,(
    $false ),
    inference(subsumption_resolution,[],[f219,f48])).

% (432)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
fof(f48,plain,(
    r2_hidden(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0))
    & r2_hidden(k1_xboole_0,sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
        & r2_hidden(k1_xboole_0,X0)
        & ~ v1_xboole_0(X0) )
   => ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0))
      & r2_hidden(k1_xboole_0,sK0)
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k1_xboole_0,X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k1_xboole_0,X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( r2_hidden(k1_xboole_0,X0)
         => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).

fof(f219,plain,(
    ~ r2_hidden(k1_xboole_0,sK0) ),
    inference(resolution,[],[f218,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f218,plain,(
    ~ m1_subset_1(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f217,f47])).

fof(f47,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f217,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f216,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ~ v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).

fof(f216,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | ~ m1_subset_1(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f211,f49])).

fof(f49,plain,(
    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f211,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | ~ m1_subset_1(k1_xboole_0,sK0)
    | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK0)) ),
    inference(resolution,[],[f210,f50])).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f210,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k3_yellow_0(k2_yellow_1(sK0)))
      | v2_struct_0(k2_yellow_1(sK0))
      | ~ m1_subset_1(X0,sK0)
      | k3_yellow_0(k2_yellow_1(sK0)) = X0 ) ),
    inference(subsumption_resolution,[],[f209,f47])).

fof(f209,plain,(
    ! [X0] :
      ( k3_yellow_0(k2_yellow_1(sK0)) = X0
      | v2_struct_0(k2_yellow_1(sK0))
      | ~ m1_subset_1(X0,sK0)
      | ~ r1_tarski(X0,k3_yellow_0(k2_yellow_1(sK0)))
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f208,f77])).

fof(f77,plain,(
    ! [X0] : m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),X0) ),
    inference(subsumption_resolution,[],[f76,f53])).

fof(f53,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f76,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),X0)
      | ~ l1_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f59,f54])).

fof(f54,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f59,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(f208,plain,(
    ! [X0] :
      ( k3_yellow_0(k2_yellow_1(sK0)) = X0
      | v2_struct_0(k2_yellow_1(sK0))
      | ~ m1_subset_1(X0,sK0)
      | ~ m1_subset_1(k3_yellow_0(k2_yellow_1(sK0)),sK0)
      | ~ r1_tarski(X0,k3_yellow_0(k2_yellow_1(sK0)))
      | v1_xboole_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f203])).

fof(f203,plain,(
    ! [X0] :
      ( k3_yellow_0(k2_yellow_1(sK0)) = X0
      | v2_struct_0(k2_yellow_1(sK0))
      | ~ m1_subset_1(X0,sK0)
      | ~ m1_subset_1(k3_yellow_0(k2_yellow_1(sK0)),sK0)
      | ~ m1_subset_1(X0,sK0)
      | ~ r1_tarski(X0,k3_yellow_0(k2_yellow_1(sK0)))
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f201,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f72,f54])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f58,f54])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f201,plain,(
    ! [X0] :
      ( ~ r3_orders_2(k2_yellow_1(sK0),X0,k3_yellow_0(k2_yellow_1(sK0)))
      | k3_yellow_0(k2_yellow_1(sK0)) = X0
      | v2_struct_0(k2_yellow_1(sK0))
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f200,f77])).

fof(f200,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | k3_yellow_0(k2_yellow_1(sK0)) = X0
      | v2_struct_0(k2_yellow_1(sK0))
      | ~ m1_subset_1(k3_yellow_0(k2_yellow_1(sK0)),sK0)
      | ~ r3_orders_2(k2_yellow_1(sK0),X0,k3_yellow_0(k2_yellow_1(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f196])).

fof(f196,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | k3_yellow_0(k2_yellow_1(sK0)) = X0
      | v2_struct_0(k2_yellow_1(sK0))
      | ~ m1_subset_1(k3_yellow_0(k2_yellow_1(sK0)),sK0)
      | ~ r3_orders_2(k2_yellow_1(sK0),X0,k3_yellow_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X0,sK0)
      | v2_struct_0(k2_yellow_1(sK0)) ) ),
    inference(resolution,[],[f189,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,X0)
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(forward_demodulation,[],[f87,f54])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(forward_demodulation,[],[f86,f54])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f85,f51])).

fof(f51,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(resolution,[],[f70,f53])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f189,plain,(
    ! [X3] :
      ( ~ r1_orders_2(k2_yellow_1(sK0),X3,k3_yellow_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X3,sK0)
      | k3_yellow_0(k2_yellow_1(sK0)) = X3
      | v2_struct_0(k2_yellow_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f186,f77])).

fof(f186,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | ~ r1_orders_2(k2_yellow_1(sK0),X3,k3_yellow_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(k3_yellow_0(k2_yellow_1(sK0)),sK0)
      | k3_yellow_0(k2_yellow_1(sK0)) = X3
      | v2_struct_0(k2_yellow_1(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f184])).

fof(f184,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | ~ r1_orders_2(k2_yellow_1(sK0),X3,k3_yellow_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(k3_yellow_0(k2_yellow_1(sK0)),sK0)
      | k3_yellow_0(k2_yellow_1(sK0)) = X3
      | ~ m1_subset_1(X3,sK0)
      | v2_struct_0(k2_yellow_1(sK0)) ) ),
    inference(resolution,[],[f181,f114])).

fof(f114,plain,(
    ! [X0] :
      ( r1_orders_2(k2_yellow_1(sK0),k3_yellow_0(k2_yellow_1(sK0)),X0)
      | ~ m1_subset_1(X0,sK0)
      | v2_struct_0(k2_yellow_1(sK0)) ) ),
    inference(forward_demodulation,[],[f113,f54])).

fof(f113,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
      | r1_orders_2(k2_yellow_1(sK0),k3_yellow_0(k2_yellow_1(sK0)),X0)
      | v2_struct_0(k2_yellow_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f112,f52])).

fof(f52,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f112,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
      | r1_orders_2(k2_yellow_1(sK0),k3_yellow_0(k2_yellow_1(sK0)),X0)
      | ~ v5_orders_2(k2_yellow_1(sK0))
      | v2_struct_0(k2_yellow_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f109,f53])).

fof(f109,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0)))
      | ~ l1_orders_2(k2_yellow_1(sK0))
      | r1_orders_2(k2_yellow_1(sK0),k3_yellow_0(k2_yellow_1(sK0)),X0)
      | ~ v5_orders_2(k2_yellow_1(sK0))
      | v2_struct_0(k2_yellow_1(sK0)) ) ),
    inference(resolution,[],[f108,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_yellow_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,k3_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).

fof(f108,plain,(
    v1_yellow_0(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f107,f48])).

fof(f107,plain,
    ( v1_yellow_0(k2_yellow_1(sK0))
    | ~ r2_hidden(k1_xboole_0,sK0) ),
    inference(resolution,[],[f102,f69])).

fof(f102,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK0)
    | v1_yellow_0(k2_yellow_1(sK0)) ),
    inference(resolution,[],[f101,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(k2_yellow_1(X0),X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_yellow_0(k2_yellow_1(X0)) ) ),
    inference(forward_demodulation,[],[f79,f54])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(k2_yellow_1(X0),X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_yellow_0(k2_yellow_1(X0)) ) ),
    inference(forward_demodulation,[],[f78,f54])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(k2_yellow_1(X0),u1_struct_0(k2_yellow_1(X0)),X1)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_yellow_0(k2_yellow_1(X0)) ) ),
    inference(resolution,[],[f62,f53])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_lattice3(X0,u1_struct_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v1_yellow_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( v1_yellow_0(X0)
          | ! [X1] :
              ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( r1_lattice3(X0,u1_struct_0(X0),sK1(X0))
            & m1_subset_1(sK1(X0),u1_struct_0(X0)) )
          | ~ v1_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X2] :
          ( r1_lattice3(X0,u1_struct_0(X0),X2)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( r1_lattice3(X0,u1_struct_0(X0),sK1(X0))
        & m1_subset_1(sK1(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( ( v1_yellow_0(X0)
          | ! [X1] :
              ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X2] :
              ( r1_lattice3(X0,u1_struct_0(X0),X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v1_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( ( v1_yellow_0(X0)
          | ! [X1] :
              ( ~ r1_lattice3(X0,u1_struct_0(X0),X1)
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X1] :
              ( r1_lattice3(X0,u1_struct_0(X0),X1)
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v1_yellow_0(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_yellow_0(X0)
      <=> ? [X1] :
            ( r1_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_yellow_0(X0)
      <=> ? [X1] :
            ( r1_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_yellow_0)).

fof(f101,plain,(
    ! [X0] : r1_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f100,f47])).

fof(f100,plain,(
    ! [X0] :
      ( v1_xboole_0(sK0)
      | r1_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0) ) ),
    inference(resolution,[],[f99,f48])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0)
      | r1_lattice3(k2_yellow_1(X0),X1,k1_xboole_0) ) ),
    inference(resolution,[],[f98,f69])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_xboole_0,X0)
      | r1_lattice3(k2_yellow_1(X0),X1,k1_xboole_0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f97,f50])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,sK2(k2_yellow_1(X1),X2,X0))
      | r1_lattice3(k2_yellow_1(X1),X2,X0)
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f96,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(k2_yellow_1(X0),X1,X2),X0)
      | r1_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0) ) ),
    inference(subsumption_resolution,[],[f83,f53])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(k2_yellow_1(X0),X1,X2),X0)
      | r1_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ l1_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f64,f54])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
                & r2_hidden(sK2(X0,X1,X2),X1)
                & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
        & r2_hidden(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

% (448)Termination reason: Refutation not found, incomplete strategy
fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | r1_lattice3(k2_yellow_1(X1),X2,X0)
      | ~ m1_subset_1(sK2(k2_yellow_1(X1),X2,X0),X1)
      | ~ r1_tarski(X0,sK2(k2_yellow_1(X1),X2,X0))
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f95,f56])).

% (448)Memory used [KB]: 1663
fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v2_struct_0(k2_yellow_1(X1))
      | r1_lattice3(k2_yellow_1(X1),X2,X0)
      | ~ m1_subset_1(sK2(k2_yellow_1(X1),X2,X0),X1)
      | ~ r1_tarski(X0,sK2(k2_yellow_1(X1),X2,X0))
      | v1_xboole_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f94])).

% (448)Time elapsed: 0.106 s
% (448)------------------------------
% (448)------------------------------
fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v2_struct_0(k2_yellow_1(X1))
      | r1_lattice3(k2_yellow_1(X1),X2,X0)
      | ~ m1_subset_1(sK2(k2_yellow_1(X1),X2,X0),X1)
      | ~ m1_subset_1(X0,X1)
      | ~ r1_tarski(X0,sK2(k2_yellow_1(X1),X2,X0))
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f93,f73])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X1,X2))
      | ~ m1_subset_1(X2,X0)
      | v2_struct_0(k2_yellow_1(X0))
      | r1_lattice3(k2_yellow_1(X0),X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | ~ r3_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X1,X2))
      | ~ m1_subset_1(X2,X0)
      | v2_struct_0(k2_yellow_1(X0))
      | r1_lattice3(k2_yellow_1(X0),X1,X2) ) ),
    inference(forward_demodulation,[],[f91,f54])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X1,X2))
      | ~ m1_subset_1(X2,X0)
      | v2_struct_0(k2_yellow_1(X0))
      | r1_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) ) ),
    inference(subsumption_resolution,[],[f90,f84])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2(k2_yellow_1(X0),X1,X2),X0)
      | ~ r3_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X1,X2))
      | ~ m1_subset_1(X2,X0)
      | v2_struct_0(k2_yellow_1(X0))
      | r1_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) ) ),
    inference(subsumption_resolution,[],[f89,f53])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2(k2_yellow_1(X0),X1,X2),X0)
      | ~ r3_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X1,X2))
      | ~ m1_subset_1(X2,X0)
      | v2_struct_0(k2_yellow_1(X0))
      | r1_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ l1_orders_2(k2_yellow_1(X0)) ) ),
    inference(resolution,[],[f88,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f181,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | X1 = X2 ) ),
    inference(forward_demodulation,[],[f180,f54])).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_orders_2(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | X1 = X2 ) ),
    inference(forward_demodulation,[],[f179,f54])).

fof(f179,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_orders_2(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | X1 = X2 ) ),
    inference(subsumption_resolution,[],[f178,f53])).

fof(f178,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_orders_2(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | X1 = X2 ) ),
    inference(resolution,[],[f68,f52])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_orders_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:28:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.23/0.49  % (428)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.23/0.51  % (436)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.23/0.51  % (434)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.23/0.52  % (453)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.23/0.52  % (434)Refutation found. Thanks to Tanya!
% 0.23/0.52  % SZS status Theorem for theBenchmark
% 0.23/0.52  % (436)Refutation not found, incomplete strategy% (436)------------------------------
% 0.23/0.52  % (436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (453)Refutation not found, incomplete strategy% (453)------------------------------
% 0.23/0.52  % (453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (436)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.52  
% 0.23/0.52  % (436)Memory used [KB]: 10618
% 0.23/0.52  % (436)Time elapsed: 0.102 s
% 0.23/0.52  % (436)------------------------------
% 0.23/0.52  % (436)------------------------------
% 0.23/0.52  % (453)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.52  
% 0.23/0.52  % (453)Memory used [KB]: 10746
% 0.23/0.52  % (453)Time elapsed: 0.100 s
% 0.23/0.52  % (453)------------------------------
% 0.23/0.52  % (453)------------------------------
% 0.23/0.52  % (445)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.23/0.52  % (448)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.23/0.53  % (448)Refutation not found, incomplete strategy% (448)------------------------------
% 0.23/0.53  % (448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % SZS output start Proof for theBenchmark
% 0.23/0.53  fof(f220,plain,(
% 0.23/0.53    $false),
% 0.23/0.53    inference(subsumption_resolution,[],[f219,f48])).
% 1.28/0.53  % (432)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.28/0.53  fof(f48,plain,(
% 1.28/0.53    r2_hidden(k1_xboole_0,sK0)),
% 1.28/0.53    inference(cnf_transformation,[],[f36])).
% 1.28/0.53  fof(f36,plain,(
% 1.28/0.53    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0)) & r2_hidden(k1_xboole_0,sK0) & ~v1_xboole_0(sK0)),
% 1.28/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f35])).
% 1.28/0.53  fof(f35,plain,(
% 1.28/0.53    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0) & ~v1_xboole_0(X0)) => (k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0)) & r2_hidden(k1_xboole_0,sK0) & ~v1_xboole_0(sK0))),
% 1.28/0.53    introduced(choice_axiom,[])).
% 1.28/0.53  fof(f21,plain,(
% 1.28/0.53    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0) & ~v1_xboole_0(X0))),
% 1.28/0.53    inference(flattening,[],[f20])).
% 1.28/0.53  fof(f20,plain,(
% 1.28/0.53    ? [X0] : ((k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0)) & ~v1_xboole_0(X0))),
% 1.28/0.53    inference(ennf_transformation,[],[f15])).
% 1.28/0.53  fof(f15,negated_conjecture,(
% 1.28/0.53    ~! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 1.28/0.53    inference(negated_conjecture,[],[f14])).
% 1.28/0.53  fof(f14,conjecture,(
% 1.28/0.53    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).
% 1.28/0.53  fof(f219,plain,(
% 1.28/0.53    ~r2_hidden(k1_xboole_0,sK0)),
% 1.28/0.53    inference(resolution,[],[f218,f69])).
% 1.28/0.53  fof(f69,plain,(
% 1.28/0.53    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f32])).
% 1.28/0.53  fof(f32,plain,(
% 1.28/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.28/0.53    inference(ennf_transformation,[],[f2])).
% 1.28/0.53  fof(f2,axiom,(
% 1.28/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.28/0.53  fof(f218,plain,(
% 1.28/0.53    ~m1_subset_1(k1_xboole_0,sK0)),
% 1.28/0.53    inference(subsumption_resolution,[],[f217,f47])).
% 1.28/0.53  fof(f47,plain,(
% 1.28/0.53    ~v1_xboole_0(sK0)),
% 1.28/0.53    inference(cnf_transformation,[],[f36])).
% 1.28/0.53  fof(f217,plain,(
% 1.28/0.53    ~m1_subset_1(k1_xboole_0,sK0) | v1_xboole_0(sK0)),
% 1.28/0.53    inference(resolution,[],[f216,f56])).
% 1.28/0.53  fof(f56,plain,(
% 1.28/0.53    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f22])).
% 1.28/0.53  fof(f22,plain,(
% 1.28/0.53    ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0))),
% 1.28/0.53    inference(ennf_transformation,[],[f17])).
% 1.28/0.53  fof(f17,plain,(
% 1.28/0.53    ! [X0] : (~v1_xboole_0(X0) => ~v2_struct_0(k2_yellow_1(X0)))),
% 1.28/0.53    inference(pure_predicate_removal,[],[f11])).
% 1.28/0.53  fof(f11,axiom,(
% 1.28/0.53    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).
% 1.28/0.53  fof(f216,plain,(
% 1.28/0.53    v2_struct_0(k2_yellow_1(sK0)) | ~m1_subset_1(k1_xboole_0,sK0)),
% 1.28/0.53    inference(subsumption_resolution,[],[f211,f49])).
% 1.28/0.53  fof(f49,plain,(
% 1.28/0.53    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0))),
% 1.28/0.53    inference(cnf_transformation,[],[f36])).
% 1.28/0.53  fof(f211,plain,(
% 1.28/0.53    v2_struct_0(k2_yellow_1(sK0)) | ~m1_subset_1(k1_xboole_0,sK0) | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK0))),
% 1.28/0.53    inference(resolution,[],[f210,f50])).
% 1.28/0.53  fof(f50,plain,(
% 1.28/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f1])).
% 1.28/0.53  fof(f1,axiom,(
% 1.28/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.28/0.53  fof(f210,plain,(
% 1.28/0.53    ( ! [X0] : (~r1_tarski(X0,k3_yellow_0(k2_yellow_1(sK0))) | v2_struct_0(k2_yellow_1(sK0)) | ~m1_subset_1(X0,sK0) | k3_yellow_0(k2_yellow_1(sK0)) = X0) )),
% 1.28/0.53    inference(subsumption_resolution,[],[f209,f47])).
% 1.28/0.53  fof(f209,plain,(
% 1.28/0.53    ( ! [X0] : (k3_yellow_0(k2_yellow_1(sK0)) = X0 | v2_struct_0(k2_yellow_1(sK0)) | ~m1_subset_1(X0,sK0) | ~r1_tarski(X0,k3_yellow_0(k2_yellow_1(sK0))) | v1_xboole_0(sK0)) )),
% 1.28/0.53    inference(subsumption_resolution,[],[f208,f77])).
% 1.28/0.53  fof(f77,plain,(
% 1.28/0.53    ( ! [X0] : (m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),X0)) )),
% 1.28/0.53    inference(subsumption_resolution,[],[f76,f53])).
% 1.28/0.53  fof(f53,plain,(
% 1.28/0.53    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 1.28/0.53    inference(cnf_transformation,[],[f18])).
% 1.28/0.53  fof(f18,plain,(
% 1.28/0.53    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 1.28/0.53    inference(pure_predicate_removal,[],[f9])).
% 1.28/0.53  fof(f9,axiom,(
% 1.28/0.53    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 1.28/0.53  fof(f76,plain,(
% 1.28/0.53    ( ! [X0] : (m1_subset_1(k3_yellow_0(k2_yellow_1(X0)),X0) | ~l1_orders_2(k2_yellow_1(X0))) )),
% 1.28/0.53    inference(superposition,[],[f59,f54])).
% 1.28/0.53  fof(f54,plain,(
% 1.28/0.53    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 1.28/0.53    inference(cnf_transformation,[],[f12])).
% 1.28/0.53  fof(f12,axiom,(
% 1.28/0.53    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).
% 1.28/0.53  fof(f59,plain,(
% 1.28/0.53    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f24])).
% 1.28/0.53  fof(f24,plain,(
% 1.28/0.53    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.28/0.53    inference(ennf_transformation,[],[f7])).
% 1.28/0.53  fof(f7,axiom,(
% 1.28/0.53    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).
% 1.28/0.53  fof(f208,plain,(
% 1.28/0.53    ( ! [X0] : (k3_yellow_0(k2_yellow_1(sK0)) = X0 | v2_struct_0(k2_yellow_1(sK0)) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(k3_yellow_0(k2_yellow_1(sK0)),sK0) | ~r1_tarski(X0,k3_yellow_0(k2_yellow_1(sK0))) | v1_xboole_0(sK0)) )),
% 1.28/0.53    inference(duplicate_literal_removal,[],[f203])).
% 1.28/0.53  fof(f203,plain,(
% 1.28/0.53    ( ! [X0] : (k3_yellow_0(k2_yellow_1(sK0)) = X0 | v2_struct_0(k2_yellow_1(sK0)) | ~m1_subset_1(X0,sK0) | ~m1_subset_1(k3_yellow_0(k2_yellow_1(sK0)),sK0) | ~m1_subset_1(X0,sK0) | ~r1_tarski(X0,k3_yellow_0(k2_yellow_1(sK0))) | v1_xboole_0(sK0)) )),
% 1.28/0.53    inference(resolution,[],[f201,f73])).
% 1.28/0.53  fof(f73,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 1.28/0.53    inference(forward_demodulation,[],[f72,f54])).
% 1.28/0.53  fof(f72,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 1.28/0.53    inference(forward_demodulation,[],[f58,f54])).
% 1.28/0.53  fof(f58,plain,(
% 1.28/0.53    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 1.28/0.53    inference(cnf_transformation,[],[f37])).
% 1.28/0.53  fof(f37,plain,(
% 1.28/0.53    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 1.28/0.53    inference(nnf_transformation,[],[f23])).
% 1.28/0.53  fof(f23,plain,(
% 1.28/0.53    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 1.28/0.53    inference(ennf_transformation,[],[f13])).
% 1.28/0.53  fof(f13,axiom,(
% 1.28/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 1.28/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).
% 1.28/0.53  fof(f201,plain,(
% 1.28/0.53    ( ! [X0] : (~r3_orders_2(k2_yellow_1(sK0),X0,k3_yellow_0(k2_yellow_1(sK0))) | k3_yellow_0(k2_yellow_1(sK0)) = X0 | v2_struct_0(k2_yellow_1(sK0)) | ~m1_subset_1(X0,sK0)) )),
% 1.28/0.53    inference(subsumption_resolution,[],[f200,f77])).
% 1.28/0.53  fof(f200,plain,(
% 1.28/0.53    ( ! [X0] : (~m1_subset_1(X0,sK0) | k3_yellow_0(k2_yellow_1(sK0)) = X0 | v2_struct_0(k2_yellow_1(sK0)) | ~m1_subset_1(k3_yellow_0(k2_yellow_1(sK0)),sK0) | ~r3_orders_2(k2_yellow_1(sK0),X0,k3_yellow_0(k2_yellow_1(sK0)))) )),
% 1.28/0.53    inference(duplicate_literal_removal,[],[f196])).
% 1.28/0.54  fof(f196,plain,(
% 1.28/0.54    ( ! [X0] : (~m1_subset_1(X0,sK0) | k3_yellow_0(k2_yellow_1(sK0)) = X0 | v2_struct_0(k2_yellow_1(sK0)) | ~m1_subset_1(k3_yellow_0(k2_yellow_1(sK0)),sK0) | ~r3_orders_2(k2_yellow_1(sK0),X0,k3_yellow_0(k2_yellow_1(sK0))) | ~m1_subset_1(X0,sK0) | v2_struct_0(k2_yellow_1(sK0))) )),
% 1.28/0.54    inference(resolution,[],[f189,f88])).
% 1.28/0.54  fof(f88,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,X0) | v2_struct_0(k2_yellow_1(X0))) )),
% 1.28/0.54    inference(forward_demodulation,[],[f87,f54])).
% 1.28/0.54  fof(f87,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | r1_orders_2(k2_yellow_1(X0),X1,X2) | v2_struct_0(k2_yellow_1(X0))) )),
% 1.28/0.54    inference(forward_demodulation,[],[f86,f54])).
% 1.28/0.54  fof(f86,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | r1_orders_2(k2_yellow_1(X0),X1,X2) | v2_struct_0(k2_yellow_1(X0))) )),
% 1.28/0.54    inference(subsumption_resolution,[],[f85,f51])).
% 1.28/0.54  fof(f51,plain,(
% 1.28/0.54    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 1.28/0.54    inference(cnf_transformation,[],[f19])).
% 1.28/0.54  fof(f19,plain,(
% 1.28/0.54    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 1.28/0.54    inference(pure_predicate_removal,[],[f16])).
% 1.28/0.54  fof(f16,plain,(
% 1.28/0.54    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 1.28/0.54    inference(pure_predicate_removal,[],[f10])).
% 1.28/0.54  fof(f10,axiom,(
% 1.28/0.54    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 1.28/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).
% 1.28/0.54  fof(f85,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0))) )),
% 1.28/0.54    inference(resolution,[],[f70,f53])).
% 1.28/0.54  fof(f70,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f46])).
% 1.28/0.54  fof(f46,plain,(
% 1.28/0.54    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.28/0.54    inference(nnf_transformation,[],[f34])).
% 1.28/0.54  fof(f34,plain,(
% 1.28/0.54    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.28/0.54    inference(flattening,[],[f33])).
% 1.28/0.54  fof(f33,plain,(
% 1.28/0.54    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.28/0.54    inference(ennf_transformation,[],[f3])).
% 1.28/0.54  fof(f3,axiom,(
% 1.28/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 1.28/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 1.28/0.54  fof(f189,plain,(
% 1.28/0.54    ( ! [X3] : (~r1_orders_2(k2_yellow_1(sK0),X3,k3_yellow_0(k2_yellow_1(sK0))) | ~m1_subset_1(X3,sK0) | k3_yellow_0(k2_yellow_1(sK0)) = X3 | v2_struct_0(k2_yellow_1(sK0))) )),
% 1.28/0.54    inference(subsumption_resolution,[],[f186,f77])).
% 1.28/0.54  fof(f186,plain,(
% 1.28/0.54    ( ! [X3] : (~m1_subset_1(X3,sK0) | ~r1_orders_2(k2_yellow_1(sK0),X3,k3_yellow_0(k2_yellow_1(sK0))) | ~m1_subset_1(k3_yellow_0(k2_yellow_1(sK0)),sK0) | k3_yellow_0(k2_yellow_1(sK0)) = X3 | v2_struct_0(k2_yellow_1(sK0))) )),
% 1.28/0.54    inference(duplicate_literal_removal,[],[f184])).
% 1.28/0.54  fof(f184,plain,(
% 1.28/0.54    ( ! [X3] : (~m1_subset_1(X3,sK0) | ~r1_orders_2(k2_yellow_1(sK0),X3,k3_yellow_0(k2_yellow_1(sK0))) | ~m1_subset_1(k3_yellow_0(k2_yellow_1(sK0)),sK0) | k3_yellow_0(k2_yellow_1(sK0)) = X3 | ~m1_subset_1(X3,sK0) | v2_struct_0(k2_yellow_1(sK0))) )),
% 1.28/0.54    inference(resolution,[],[f181,f114])).
% 1.28/0.54  fof(f114,plain,(
% 1.28/0.54    ( ! [X0] : (r1_orders_2(k2_yellow_1(sK0),k3_yellow_0(k2_yellow_1(sK0)),X0) | ~m1_subset_1(X0,sK0) | v2_struct_0(k2_yellow_1(sK0))) )),
% 1.28/0.54    inference(forward_demodulation,[],[f113,f54])).
% 1.28/0.54  fof(f113,plain,(
% 1.28/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),k3_yellow_0(k2_yellow_1(sK0)),X0) | v2_struct_0(k2_yellow_1(sK0))) )),
% 1.28/0.54    inference(subsumption_resolution,[],[f112,f52])).
% 1.28/0.54  fof(f52,plain,(
% 1.28/0.54    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 1.28/0.54    inference(cnf_transformation,[],[f19])).
% 1.28/0.54  fof(f112,plain,(
% 1.28/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),k3_yellow_0(k2_yellow_1(sK0)),X0) | ~v5_orders_2(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0))) )),
% 1.28/0.54    inference(subsumption_resolution,[],[f109,f53])).
% 1.28/0.54  fof(f109,plain,(
% 1.28/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | r1_orders_2(k2_yellow_1(sK0),k3_yellow_0(k2_yellow_1(sK0)),X0) | ~v5_orders_2(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0))) )),
% 1.28/0.54    inference(resolution,[],[f108,f67])).
% 1.28/0.54  fof(f67,plain,(
% 1.28/0.54    ( ! [X0,X1] : (~v1_yellow_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,k3_yellow_0(X0),X1) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f29])).
% 1.28/0.54  fof(f29,plain,(
% 1.28/0.54    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.28/0.54    inference(flattening,[],[f28])).
% 1.28/0.54  fof(f28,plain,(
% 1.28/0.54    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 1.28/0.54    inference(ennf_transformation,[],[f8])).
% 1.28/0.54  fof(f8,axiom,(
% 1.28/0.54    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 1.28/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_yellow_0)).
% 1.28/0.54  fof(f108,plain,(
% 1.28/0.54    v1_yellow_0(k2_yellow_1(sK0))),
% 1.28/0.54    inference(subsumption_resolution,[],[f107,f48])).
% 1.28/0.54  fof(f107,plain,(
% 1.28/0.54    v1_yellow_0(k2_yellow_1(sK0)) | ~r2_hidden(k1_xboole_0,sK0)),
% 1.28/0.54    inference(resolution,[],[f102,f69])).
% 1.28/0.54  fof(f102,plain,(
% 1.28/0.54    ~m1_subset_1(k1_xboole_0,sK0) | v1_yellow_0(k2_yellow_1(sK0))),
% 1.28/0.54    inference(resolution,[],[f101,f80])).
% 1.28/0.54  fof(f80,plain,(
% 1.28/0.54    ( ! [X0,X1] : (~r1_lattice3(k2_yellow_1(X0),X0,X1) | ~m1_subset_1(X1,X0) | v1_yellow_0(k2_yellow_1(X0))) )),
% 1.28/0.54    inference(forward_demodulation,[],[f79,f54])).
% 1.28/0.54  fof(f79,plain,(
% 1.28/0.54    ( ! [X0,X1] : (~r1_lattice3(k2_yellow_1(X0),X0,X1) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_yellow_0(k2_yellow_1(X0))) )),
% 1.28/0.54    inference(forward_demodulation,[],[f78,f54])).
% 1.28/0.54  fof(f78,plain,(
% 1.28/0.54    ( ! [X0,X1] : (~r1_lattice3(k2_yellow_1(X0),u1_struct_0(k2_yellow_1(X0)),X1) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_yellow_0(k2_yellow_1(X0))) )),
% 1.28/0.54    inference(resolution,[],[f62,f53])).
% 1.28/0.54  fof(f62,plain,(
% 1.28/0.54    ( ! [X0,X1] : (~l1_orders_2(X0) | ~r1_lattice3(X0,u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | v1_yellow_0(X0)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f41])).
% 1.28/0.54  fof(f41,plain,(
% 1.28/0.54    ! [X0] : (((v1_yellow_0(X0) | ! [X1] : (~r1_lattice3(X0,u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((r1_lattice3(X0,u1_struct_0(X0),sK1(X0)) & m1_subset_1(sK1(X0),u1_struct_0(X0))) | ~v1_yellow_0(X0))) | ~l1_orders_2(X0))),
% 1.28/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).
% 1.28/0.54  fof(f40,plain,(
% 1.28/0.54    ! [X0] : (? [X2] : (r1_lattice3(X0,u1_struct_0(X0),X2) & m1_subset_1(X2,u1_struct_0(X0))) => (r1_lattice3(X0,u1_struct_0(X0),sK1(X0)) & m1_subset_1(sK1(X0),u1_struct_0(X0))))),
% 1.28/0.54    introduced(choice_axiom,[])).
% 1.28/0.54  fof(f39,plain,(
% 1.28/0.54    ! [X0] : (((v1_yellow_0(X0) | ! [X1] : (~r1_lattice3(X0,u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X2] : (r1_lattice3(X0,u1_struct_0(X0),X2) & m1_subset_1(X2,u1_struct_0(X0))) | ~v1_yellow_0(X0))) | ~l1_orders_2(X0))),
% 1.28/0.54    inference(rectify,[],[f38])).
% 1.28/0.54  fof(f38,plain,(
% 1.28/0.54    ! [X0] : (((v1_yellow_0(X0) | ! [X1] : (~r1_lattice3(X0,u1_struct_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (r1_lattice3(X0,u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) | ~v1_yellow_0(X0))) | ~l1_orders_2(X0))),
% 1.28/0.54    inference(nnf_transformation,[],[f25])).
% 1.28/0.54  fof(f25,plain,(
% 1.28/0.54    ! [X0] : ((v1_yellow_0(X0) <=> ? [X1] : (r1_lattice3(X0,u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.28/0.54    inference(ennf_transformation,[],[f6])).
% 1.28/0.54  fof(f6,axiom,(
% 1.28/0.54    ! [X0] : (l1_orders_2(X0) => (v1_yellow_0(X0) <=> ? [X1] : (r1_lattice3(X0,u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 1.28/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_yellow_0)).
% 1.28/0.54  fof(f101,plain,(
% 1.28/0.54    ( ! [X0] : (r1_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0)) )),
% 1.28/0.54    inference(subsumption_resolution,[],[f100,f47])).
% 1.28/0.54  fof(f100,plain,(
% 1.28/0.54    ( ! [X0] : (v1_xboole_0(sK0) | r1_lattice3(k2_yellow_1(sK0),X0,k1_xboole_0)) )),
% 1.28/0.54    inference(resolution,[],[f99,f48])).
% 1.28/0.54  fof(f99,plain,(
% 1.28/0.54    ( ! [X0,X1] : (~r2_hidden(k1_xboole_0,X0) | v1_xboole_0(X0) | r1_lattice3(k2_yellow_1(X0),X1,k1_xboole_0)) )),
% 1.28/0.54    inference(resolution,[],[f98,f69])).
% 1.28/0.54  fof(f98,plain,(
% 1.28/0.54    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,X0) | r1_lattice3(k2_yellow_1(X0),X1,k1_xboole_0) | v1_xboole_0(X0)) )),
% 1.28/0.54    inference(resolution,[],[f97,f50])).
% 1.28/0.54  fof(f97,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,sK2(k2_yellow_1(X1),X2,X0)) | r1_lattice3(k2_yellow_1(X1),X2,X0) | ~m1_subset_1(X0,X1) | v1_xboole_0(X1)) )),
% 1.28/0.54    inference(subsumption_resolution,[],[f96,f84])).
% 1.28/0.54  fof(f84,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (m1_subset_1(sK2(k2_yellow_1(X0),X1,X2),X0) | r1_lattice3(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0)) )),
% 1.28/0.54    inference(subsumption_resolution,[],[f83,f53])).
% 1.28/0.54  fof(f83,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (m1_subset_1(sK2(k2_yellow_1(X0),X1,X2),X0) | r1_lattice3(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | ~l1_orders_2(k2_yellow_1(X0))) )),
% 1.28/0.54    inference(superposition,[],[f64,f54])).
% 1.28/0.54  fof(f64,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f45])).
% 1.28/0.54  fof(f45,plain,(
% 1.28/0.54    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK2(X0,X1,X2)) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.28/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).
% 1.28/0.54  fof(f44,plain,(
% 1.28/0.54    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK2(X0,X1,X2)) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 1.28/0.54    introduced(choice_axiom,[])).
% 1.28/0.54  fof(f43,plain,(
% 1.28/0.54    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.28/0.54    inference(rectify,[],[f42])).
% 1.28/0.54  fof(f42,plain,(
% 1.28/0.54    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.28/0.54    inference(nnf_transformation,[],[f27])).
% 1.28/0.54  fof(f27,plain,(
% 1.28/0.54    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.28/0.54    inference(flattening,[],[f26])).
% 1.28/0.54  fof(f26,plain,(
% 1.28/0.54    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.28/0.54    inference(ennf_transformation,[],[f5])).
% 1.28/0.54  fof(f5,axiom,(
% 1.28/0.54    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 1.28/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).
% 1.28/0.54  % (448)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  fof(f96,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,X1) | r1_lattice3(k2_yellow_1(X1),X2,X0) | ~m1_subset_1(sK2(k2_yellow_1(X1),X2,X0),X1) | ~r1_tarski(X0,sK2(k2_yellow_1(X1),X2,X0)) | v1_xboole_0(X1)) )),
% 1.28/0.54    inference(subsumption_resolution,[],[f95,f56])).
% 1.28/0.54  
% 1.28/0.54  % (448)Memory used [KB]: 1663
% 1.28/0.54  fof(f95,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,X1) | v2_struct_0(k2_yellow_1(X1)) | r1_lattice3(k2_yellow_1(X1),X2,X0) | ~m1_subset_1(sK2(k2_yellow_1(X1),X2,X0),X1) | ~r1_tarski(X0,sK2(k2_yellow_1(X1),X2,X0)) | v1_xboole_0(X1)) )),
% 1.28/0.54    inference(duplicate_literal_removal,[],[f94])).
% 1.28/0.54  % (448)Time elapsed: 0.106 s
% 1.28/0.54  % (448)------------------------------
% 1.28/0.54  % (448)------------------------------
% 1.28/0.54  fof(f94,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,X1) | v2_struct_0(k2_yellow_1(X1)) | r1_lattice3(k2_yellow_1(X1),X2,X0) | ~m1_subset_1(sK2(k2_yellow_1(X1),X2,X0),X1) | ~m1_subset_1(X0,X1) | ~r1_tarski(X0,sK2(k2_yellow_1(X1),X2,X0)) | v1_xboole_0(X1)) )),
% 1.28/0.54    inference(resolution,[],[f93,f73])).
% 1.28/0.54  fof(f93,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X1,X2)) | ~m1_subset_1(X2,X0) | v2_struct_0(k2_yellow_1(X0)) | r1_lattice3(k2_yellow_1(X0),X1,X2)) )),
% 1.28/0.54    inference(duplicate_literal_removal,[],[f92])).
% 1.28/0.54  fof(f92,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | ~r3_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X1,X2)) | ~m1_subset_1(X2,X0) | v2_struct_0(k2_yellow_1(X0)) | r1_lattice3(k2_yellow_1(X0),X1,X2)) )),
% 1.28/0.54    inference(forward_demodulation,[],[f91,f54])).
% 1.28/0.54  fof(f91,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X1,X2)) | ~m1_subset_1(X2,X0) | v2_struct_0(k2_yellow_1(X0)) | r1_lattice3(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) )),
% 1.28/0.54    inference(subsumption_resolution,[],[f90,f84])).
% 1.28/0.54  fof(f90,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(sK2(k2_yellow_1(X0),X1,X2),X0) | ~r3_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X1,X2)) | ~m1_subset_1(X2,X0) | v2_struct_0(k2_yellow_1(X0)) | r1_lattice3(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) )),
% 1.28/0.54    inference(subsumption_resolution,[],[f89,f53])).
% 1.28/0.54  fof(f89,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(sK2(k2_yellow_1(X0),X1,X2),X0) | ~r3_orders_2(k2_yellow_1(X0),X2,sK2(k2_yellow_1(X0),X1,X2)) | ~m1_subset_1(X2,X0) | v2_struct_0(k2_yellow_1(X0)) | r1_lattice3(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~l1_orders_2(k2_yellow_1(X0))) )),
% 1.28/0.54    inference(resolution,[],[f88,f66])).
% 1.28/0.54  fof(f66,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X2,sK2(X0,X1,X2)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f45])).
% 1.28/0.54  fof(f181,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~r1_orders_2(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X1,X0) | ~r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | X1 = X2) )),
% 1.28/0.54    inference(forward_demodulation,[],[f180,f54])).
% 1.28/0.54  fof(f180,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | ~r1_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_orders_2(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | X1 = X2) )),
% 1.28/0.54    inference(forward_demodulation,[],[f179,f54])).
% 1.28/0.54  fof(f179,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~r1_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_orders_2(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | X1 = X2) )),
% 1.28/0.54    inference(subsumption_resolution,[],[f178,f53])).
% 1.28/0.54  fof(f178,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~r1_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_orders_2(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~l1_orders_2(k2_yellow_1(X0)) | X1 = X2) )),
% 1.28/0.54    inference(resolution,[],[f68,f52])).
% 1.28/0.54  fof(f68,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~r1_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | X1 = X2) )),
% 1.28/0.54    inference(cnf_transformation,[],[f31])).
% 1.28/0.54  fof(f31,plain,(
% 1.28/0.54    ! [X0] : (! [X1] : (! [X2] : (X1 = X2 | ~r1_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 1.28/0.54    inference(flattening,[],[f30])).
% 1.28/0.54  fof(f30,plain,(
% 1.28/0.54    ! [X0] : (! [X1] : (! [X2] : ((X1 = X2 | (~r1_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 1.28/0.54    inference(ennf_transformation,[],[f4])).
% 1.28/0.54  fof(f4,axiom,(
% 1.28/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2)) => X1 = X2))))),
% 1.28/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_orders_2)).
% 1.28/0.54  % SZS output end Proof for theBenchmark
% 1.28/0.54  % (434)------------------------------
% 1.28/0.54  % (434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (434)Termination reason: Refutation
% 1.28/0.54  
% 1.28/0.54  % (434)Memory used [KB]: 6396
% 1.28/0.54  % (434)Time elapsed: 0.099 s
% 1.28/0.54  % (434)------------------------------
% 1.28/0.54  % (434)------------------------------
% 1.28/0.54  % (430)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.28/0.54  % (426)Success in time 0.164 s
%------------------------------------------------------------------------------
