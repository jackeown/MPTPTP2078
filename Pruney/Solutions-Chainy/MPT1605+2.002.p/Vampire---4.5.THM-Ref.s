%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 254 expanded)
%              Number of leaves         :   15 (  60 expanded)
%              Depth                    :   30
%              Number of atoms          :  351 ( 793 expanded)
%              Number of equality atoms :   39 ( 139 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f244,plain,(
    $false ),
    inference(subsumption_resolution,[],[f243,f37])).

fof(f37,plain,(
    r2_hidden(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k1_xboole_0,X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k1_xboole_0,X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( r2_hidden(k1_xboole_0,X0)
         => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

fof(f243,plain,(
    ~ r2_hidden(k1_xboole_0,sK0) ),
    inference(resolution,[],[f242,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f242,plain,(
    ~ m1_subset_1(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f241,f36])).

fof(f36,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f241,plain,
    ( v1_xboole_0(sK0)
    | ~ m1_subset_1(k1_xboole_0,sK0) ),
    inference(forward_demodulation,[],[f240,f43])).

fof(f43,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f240,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK0)
    | v1_xboole_0(u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f239,f73])).

fof(f73,plain,(
    ! [X0] : l1_struct_0(k2_yellow_1(X0)) ),
    inference(resolution,[],[f47,f42])).

fof(f42,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f47,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f239,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK0)
    | ~ l1_struct_0(k2_yellow_1(sK0))
    | v1_xboole_0(u1_struct_0(k2_yellow_1(sK0))) ),
    inference(resolution,[],[f238,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).

fof(f238,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | ~ m1_subset_1(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f237,f38])).

fof(f38,plain,(
    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f237,plain,
    ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK0))
    | ~ m1_subset_1(k1_xboole_0,sK0)
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(forward_demodulation,[],[f236,f76])).

fof(f76,plain,(
    ! [X0] : k3_yellow_0(k2_yellow_1(X0)) = k1_yellow_0(k2_yellow_1(X0),k1_xboole_0) ),
    inference(resolution,[],[f48,f42])).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f236,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK0)
    | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0)
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f235,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r2_lattice3(k2_yellow_1(X1),k1_xboole_0,X0)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(forward_demodulation,[],[f82,f43])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
      | r2_lattice3(k2_yellow_1(X1),k1_xboole_0,X0) ) ),
    inference(resolution,[],[f49,f42])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_lattice3(X0,k1_xboole_0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_lattice3(X0,k1_xboole_0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_lattice3(X0,k1_xboole_0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

fof(f235,plain,
    ( ~ r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,sK0)
    | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0)
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f234,f77])).

fof(f77,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f63,f74])).

fof(f74,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f60,f39])).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f234,plain,
    ( ~ r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,sK0)
    | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0)
    | v2_struct_0(k2_yellow_1(sK0))
    | ~ r1_tarski(k1_xboole_0,sK1(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f232,f37])).

fof(f232,plain,
    ( ~ r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,sK0)
    | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0)
    | ~ r2_hidden(k1_xboole_0,sK0)
    | v2_struct_0(k2_yellow_1(sK0))
    | ~ r1_tarski(k1_xboole_0,sK1(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[],[f231,f166])).

fof(f166,plain,(
    ! [X0] :
      ( r1_orders_2(k2_yellow_1(sK0),X0,sK1(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0))
      | ~ r2_hidden(X0,sK0)
      | v2_struct_0(k2_yellow_1(sK0))
      | ~ r1_tarski(X0,sK1(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0)) ) ),
    inference(subsumption_resolution,[],[f165,f61])).

fof(f165,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0))
      | ~ r2_hidden(X0,sK0)
      | ~ m1_subset_1(X0,sK0)
      | v2_struct_0(k2_yellow_1(sK0))
      | r1_orders_2(k2_yellow_1(sK0),X0,sK1(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0)) ) ),
    inference(subsumption_resolution,[],[f163,f154])).

fof(f154,plain,(
    m1_subset_1(sK1(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0),sK0) ),
    inference(subsumption_resolution,[],[f151,f38])).

fof(f151,plain,
    ( m1_subset_1(sK1(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0),sK0)
    | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK0)) ),
    inference(resolution,[],[f150,f37])).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(sK1(k2_yellow_1(X0),X1,k1_xboole_0),X0)
      | k3_yellow_0(k2_yellow_1(X0)) = X1 ) ),
    inference(forward_demodulation,[],[f149,f76])).

fof(f149,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK1(k2_yellow_1(X0),X1,k1_xboole_0),X0)
      | k1_yellow_0(k2_yellow_1(X0),k1_xboole_0) = X1
      | ~ r2_hidden(X1,X0) ) ),
    inference(subsumption_resolution,[],[f147,f61])).

fof(f147,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK1(k2_yellow_1(X0),X1,k1_xboole_0),X0)
      | k1_yellow_0(k2_yellow_1(X0),k1_xboole_0) = X1
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(resolution,[],[f145,f83])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(k2_yellow_1(X0),X2,X1)
      | m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),X0)
      | k1_yellow_0(k2_yellow_1(X0),X2) = X1
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f144,f61])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),X0)
      | ~ r2_lattice3(k2_yellow_1(X0),X2,X1)
      | k1_yellow_0(k2_yellow_1(X0),X2) = X1 ) ),
    inference(forward_demodulation,[],[f143,f43])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | ~ r2_lattice3(k2_yellow_1(X0),X2,X1)
      | m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
      | k1_yellow_0(k2_yellow_1(X0),X2) = X1 ) ),
    inference(forward_demodulation,[],[f142,f43])).

% (30107)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f142,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ r2_lattice3(k2_yellow_1(X0),X2,X1)
      | m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
      | k1_yellow_0(k2_yellow_1(X0),X2) = X1 ) ),
    inference(subsumption_resolution,[],[f141,f42])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(k2_yellow_1(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ r2_lattice3(k2_yellow_1(X0),X2,X1)
      | m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0)))
      | k1_yellow_0(k2_yellow_1(X0),X2) = X1 ) ),
    inference(resolution,[],[f55,f41])).

fof(f41,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X2,X1)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | k1_yellow_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
                | ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r2_lattice3(X0,X2,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X2,X1) )
              & ( ( ! [X4] :
                      ( r1_orders_2(X0,X1,X4)
                      | ~ r2_lattice3(X0,X2,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_lattice3(X0,X2,X1) )
                | ~ r1_yellow_0(X0,X2)
                | k1_yellow_0(X0,X2) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X4)
                       => r1_orders_2(X0,X1,X4) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    inference(rectify,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) )
               => ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 ) )
              & ( ( r1_yellow_0(X0,X2)
                  & k1_yellow_0(X0,X2) = X1 )
               => ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X2,X3)
                       => r1_orders_2(X0,X1,X3) ) )
                  & r2_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_yellow_0)).

fof(f163,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0))
      | ~ r2_hidden(X0,sK0)
      | ~ m1_subset_1(X0,sK0)
      | v2_struct_0(k2_yellow_1(sK0))
      | r1_orders_2(k2_yellow_1(sK0),X0,sK1(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0))
      | ~ m1_subset_1(sK1(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0),sK0) ) ),
    inference(resolution,[],[f160,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,X0)
      | v2_struct_0(k2_yellow_1(X0))
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0) ) ),
    inference(forward_demodulation,[],[f106,f43])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v2_struct_0(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    inference(forward_demodulation,[],[f105,f43])).

% (30108)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f105,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(k2_yellow_1(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    inference(subsumption_resolution,[],[f104,f42])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(k2_yellow_1(X0))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    inference(resolution,[],[f66,f40])).

fof(f40,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f160,plain,(
    ! [X2] :
      ( r3_orders_2(k2_yellow_1(sK0),X2,sK1(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0))
      | ~ r1_tarski(X2,sK1(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0))
      | ~ r2_hidden(X2,sK0) ) ),
    inference(resolution,[],[f154,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | ~ r1_tarski(X2,X0)
      | r3_orders_2(k2_yellow_1(X1),X2,X0)
      | ~ r2_hidden(X2,X1) ) ),
    inference(subsumption_resolution,[],[f84,f60])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | ~ r1_tarski(X2,X0)
      | r3_orders_2(k2_yellow_1(X1),X2,X0)
      | ~ r2_hidden(X2,X1) ) ),
    inference(resolution,[],[f72,f61])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X1,X2)
      | r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    inference(forward_demodulation,[],[f71,f43])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ r1_tarski(X1,X2)
      | r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    inference(forward_demodulation,[],[f45,f43])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ r1_tarski(X1,X2)
      | r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

% (30118)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f231,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(k2_yellow_1(X0),X1,sK1(k2_yellow_1(X0),X1,X2))
      | ~ r2_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X1,X0)
      | k1_yellow_0(k2_yellow_1(X0),X2) = X1 ) ),
    inference(forward_demodulation,[],[f230,f43])).

fof(f230,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ r2_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ r1_orders_2(k2_yellow_1(X0),X1,sK1(k2_yellow_1(X0),X1,X2))
      | k1_yellow_0(k2_yellow_1(X0),X2) = X1 ) ),
    inference(subsumption_resolution,[],[f229,f42])).

fof(f229,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(k2_yellow_1(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ r2_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ r1_orders_2(k2_yellow_1(X0),X1,sK1(k2_yellow_1(X0),X1,X2))
      | k1_yellow_0(k2_yellow_1(X0),X2) = X1 ) ),
    inference(resolution,[],[f57,f41])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,sK1(X0,X1,X2))
      | k1_yellow_0(X0,X2) = X1 ) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n013.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:12:24 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.52  % (30135)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (30114)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (30113)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (30111)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (30129)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (30113)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f244,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(subsumption_resolution,[],[f243,f37])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    r2_hidden(k1_xboole_0,sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ? [X0] : (k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0) & ~v1_xboole_0(X0))),
% 0.22/0.54    inference(flattening,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ? [X0] : ((k1_xboole_0 != k3_yellow_0(k2_yellow_1(X0)) & r2_hidden(k1_xboole_0,X0)) & ~v1_xboole_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,negated_conjecture,(
% 0.22/0.54    ~! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 0.22/0.54    inference(negated_conjecture,[],[f15])).
% 0.22/0.54  fof(f15,conjecture,(
% 0.22/0.54    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).
% 0.22/0.54  fof(f243,plain,(
% 0.22/0.54    ~r2_hidden(k1_xboole_0,sK0)),
% 0.22/0.54    inference(resolution,[],[f242,f61])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.54  fof(f242,plain,(
% 0.22/0.54    ~m1_subset_1(k1_xboole_0,sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f241,f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ~v1_xboole_0(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f241,plain,(
% 0.22/0.54    v1_xboole_0(sK0) | ~m1_subset_1(k1_xboole_0,sK0)),
% 0.22/0.54    inference(forward_demodulation,[],[f240,f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.22/0.54  fof(f240,plain,(
% 0.22/0.54    ~m1_subset_1(k1_xboole_0,sK0) | v1_xboole_0(u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.54    inference(subsumption_resolution,[],[f239,f73])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    ( ! [X0] : (l1_struct_0(k2_yellow_1(X0))) )),
% 0.22/0.54    inference(resolution,[],[f47,f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 0.22/0.54    inference(pure_predicate_removal,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.22/0.54  fof(f239,plain,(
% 0.22/0.54    ~m1_subset_1(k1_xboole_0,sK0) | ~l1_struct_0(k2_yellow_1(sK0)) | v1_xboole_0(u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.54    inference(resolution,[],[f238,f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X0] : (~v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(u1_struct_0(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0] : ((l1_struct_0(X0) & v2_struct_0(X0)) => v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).
% 0.22/0.54  fof(f238,plain,(
% 0.22/0.54    v2_struct_0(k2_yellow_1(sK0)) | ~m1_subset_1(k1_xboole_0,sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f237,f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    k1_xboole_0 != k3_yellow_0(k2_yellow_1(sK0))),
% 0.22/0.54    inference(cnf_transformation,[],[f23])).
% 0.22/0.54  fof(f237,plain,(
% 0.22/0.54    k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK0)) | ~m1_subset_1(k1_xboole_0,sK0) | v2_struct_0(k2_yellow_1(sK0))),
% 0.22/0.54    inference(forward_demodulation,[],[f236,f76])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    ( ! [X0] : (k3_yellow_0(k2_yellow_1(X0)) = k1_yellow_0(k2_yellow_1(X0),k1_xboole_0)) )),
% 0.22/0.54    inference(resolution,[],[f48,f42])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X0] : (~l1_orders_2(X0) | k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).
% 0.22/0.54  fof(f236,plain,(
% 0.22/0.54    ~m1_subset_1(k1_xboole_0,sK0) | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) | v2_struct_0(k2_yellow_1(sK0))),
% 0.22/0.54    inference(subsumption_resolution,[],[f235,f83])).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_lattice3(k2_yellow_1(X1),k1_xboole_0,X0) | ~m1_subset_1(X0,X1)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f82,f43])).
% 0.22/0.54  fof(f82,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) | r2_lattice3(k2_yellow_1(X1),k1_xboole_0,X0)) )),
% 0.22/0.54    inference(resolution,[],[f49,f42])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r2_lattice3(X0,k1_xboole_0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (r2_lattice3(X0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_lattice3(X0,k1_xboole_0,X1)))),
% 0.22/0.54    inference(pure_predicate_removal,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (r1_lattice3(X0,k1_xboole_0,X1) & r2_lattice3(X0,k1_xboole_0,X1))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).
% 0.22/0.54  fof(f235,plain,(
% 0.22/0.54    ~r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,sK0) | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) | v2_struct_0(k2_yellow_1(sK0))),
% 0.22/0.54    inference(subsumption_resolution,[],[f234,f77])).
% 0.22/0.54  fof(f77,plain,(
% 0.22/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.54    inference(resolution,[],[f63,f74])).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.54    inference(resolution,[],[f60,f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    v1_xboole_0(k1_xboole_0)),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    v1_xboole_0(k1_xboole_0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.54  fof(f234,plain,(
% 0.22/0.54    ~r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,sK0) | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) | v2_struct_0(k2_yellow_1(sK0)) | ~r1_tarski(k1_xboole_0,sK1(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0))),
% 0.22/0.54    inference(subsumption_resolution,[],[f232,f37])).
% 0.22/0.54  fof(f232,plain,(
% 0.22/0.54    ~r2_lattice3(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,sK0) | k1_xboole_0 = k1_yellow_0(k2_yellow_1(sK0),k1_xboole_0) | ~r2_hidden(k1_xboole_0,sK0) | v2_struct_0(k2_yellow_1(sK0)) | ~r1_tarski(k1_xboole_0,sK1(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0))),
% 0.22/0.54    inference(resolution,[],[f231,f166])).
% 0.22/0.54  fof(f166,plain,(
% 0.22/0.54    ( ! [X0] : (r1_orders_2(k2_yellow_1(sK0),X0,sK1(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0)) | ~r2_hidden(X0,sK0) | v2_struct_0(k2_yellow_1(sK0)) | ~r1_tarski(X0,sK1(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f165,f61])).
% 0.22/0.54  fof(f165,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_tarski(X0,sK1(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0)) | ~r2_hidden(X0,sK0) | ~m1_subset_1(X0,sK0) | v2_struct_0(k2_yellow_1(sK0)) | r1_orders_2(k2_yellow_1(sK0),X0,sK1(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f163,f154])).
% 0.22/0.54  fof(f154,plain,(
% 0.22/0.54    m1_subset_1(sK1(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0),sK0)),
% 0.22/0.54    inference(subsumption_resolution,[],[f151,f38])).
% 0.22/0.54  fof(f151,plain,(
% 0.22/0.54    m1_subset_1(sK1(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0),sK0) | k1_xboole_0 = k3_yellow_0(k2_yellow_1(sK0))),
% 0.22/0.54    inference(resolution,[],[f150,f37])).
% 0.22/0.54  fof(f150,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(sK1(k2_yellow_1(X0),X1,k1_xboole_0),X0) | k3_yellow_0(k2_yellow_1(X0)) = X1) )),
% 0.22/0.54    inference(forward_demodulation,[],[f149,f76])).
% 0.22/0.54  fof(f149,plain,(
% 0.22/0.54    ( ! [X0,X1] : (m1_subset_1(sK1(k2_yellow_1(X0),X1,k1_xboole_0),X0) | k1_yellow_0(k2_yellow_1(X0),k1_xboole_0) = X1 | ~r2_hidden(X1,X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f147,f61])).
% 0.22/0.54  fof(f147,plain,(
% 0.22/0.54    ( ! [X0,X1] : (m1_subset_1(sK1(k2_yellow_1(X0),X1,k1_xboole_0),X0) | k1_yellow_0(k2_yellow_1(X0),k1_xboole_0) = X1 | ~r2_hidden(X1,X0) | ~m1_subset_1(X1,X0)) )),
% 0.22/0.54    inference(resolution,[],[f145,f83])).
% 0.22/0.54  fof(f145,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_lattice3(k2_yellow_1(X0),X2,X1) | m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),X0) | k1_yellow_0(k2_yellow_1(X0),X2) = X1 | ~r2_hidden(X1,X0)) )),
% 0.22/0.54    inference(resolution,[],[f144,f61])).
% 0.22/0.54  fof(f144,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),X0) | ~r2_lattice3(k2_yellow_1(X0),X2,X1) | k1_yellow_0(k2_yellow_1(X0),X2) = X1) )),
% 0.22/0.54    inference(forward_demodulation,[],[f143,f43])).
% 0.22/0.54  fof(f143,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | ~r2_lattice3(k2_yellow_1(X0),X2,X1) | m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0))) | k1_yellow_0(k2_yellow_1(X0),X2) = X1) )),
% 0.22/0.54    inference(forward_demodulation,[],[f142,f43])).
% 0.22/0.54  % (30107)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  fof(f142,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~r2_lattice3(k2_yellow_1(X0),X2,X1) | m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0))) | k1_yellow_0(k2_yellow_1(X0),X2) = X1) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f141,f42])).
% 0.22/0.54  fof(f141,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~l1_orders_2(k2_yellow_1(X0)) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~r2_lattice3(k2_yellow_1(X0),X2,X1) | m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),u1_struct_0(k2_yellow_1(X0))) | k1_yellow_0(k2_yellow_1(X0),X2) = X1) )),
% 0.22/0.54    inference(resolution,[],[f55,f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 0.22/0.54    inference(pure_predicate_removal,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.22/0.54    inference(pure_predicate_removal,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r2_lattice3(X0,X2,X1) | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | k1_yellow_0(X0,X2) = X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | ~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.22/0.54    inference(flattening,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X1,X3) & r2_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X1,X4) | ~r2_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_lattice3(X0,X2,X1)) | (~r1_yellow_0(X0,X2) | k1_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X4) => r1_orders_2(X0,X1,X4))) & r2_lattice3(X0,X2,X1))))))),
% 0.22/0.54    inference(rectify,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1)) => (r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1)) & ((r1_yellow_0(X0,X2) & k1_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X2,X3) => r1_orders_2(X0,X1,X3))) & r2_lattice3(X0,X2,X1))))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_yellow_0)).
% 0.22/0.54  fof(f163,plain,(
% 0.22/0.54    ( ! [X0] : (~r1_tarski(X0,sK1(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0)) | ~r2_hidden(X0,sK0) | ~m1_subset_1(X0,sK0) | v2_struct_0(k2_yellow_1(sK0)) | r1_orders_2(k2_yellow_1(sK0),X0,sK1(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0)) | ~m1_subset_1(sK1(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0),sK0)) )),
% 0.22/0.54    inference(resolution,[],[f160,f107])).
% 0.22/0.54  fof(f107,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,X0) | v2_struct_0(k2_yellow_1(X0)) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f106,f43])).
% 0.22/0.54  fof(f106,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f105,f43])).
% 0.22/0.54  % (30108)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  fof(f105,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f104,f42])).
% 0.22/0.54  fof(f104,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (v2_struct_0(k2_yellow_1(X0)) | ~l1_orders_2(k2_yellow_1(X0)) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2)) )),
% 0.22/0.54    inference(resolution,[],[f66,f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f20])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v3_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.22/0.54  fof(f160,plain,(
% 0.22/0.54    ( ! [X2] : (r3_orders_2(k2_yellow_1(sK0),X2,sK1(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0)) | ~r1_tarski(X2,sK1(k2_yellow_1(sK0),k1_xboole_0,k1_xboole_0)) | ~r2_hidden(X2,sK0)) )),
% 0.22/0.54    inference(resolution,[],[f154,f85])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,X1) | ~r1_tarski(X2,X0) | r3_orders_2(k2_yellow_1(X1),X2,X0) | ~r2_hidden(X2,X1)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f84,f60])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | ~r1_tarski(X2,X0) | r3_orders_2(k2_yellow_1(X1),X2,X0) | ~r2_hidden(X2,X1)) )),
% 0.22/0.54    inference(resolution,[],[f72,f61])).
% 0.22/0.54  fof(f72,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | ~m1_subset_1(X2,X0) | v1_xboole_0(X0) | ~r1_tarski(X1,X2) | r3_orders_2(k2_yellow_1(X0),X1,X2)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f71,f43])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~r1_tarski(X1,X2) | r3_orders_2(k2_yellow_1(X0),X1,X2)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f45,f43])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~r1_tarski(X1,X2) | r3_orders_2(k2_yellow_1(X0),X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,axiom,(
% 0.22/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).
% 0.22/0.54  % (30118)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.54  fof(f231,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_orders_2(k2_yellow_1(X0),X1,sK1(k2_yellow_1(X0),X1,X2)) | ~r2_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X1,X0) | k1_yellow_0(k2_yellow_1(X0),X2) = X1) )),
% 0.22/0.54    inference(forward_demodulation,[],[f230,f43])).
% 0.22/0.54  fof(f230,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~r2_lattice3(k2_yellow_1(X0),X2,X1) | ~r1_orders_2(k2_yellow_1(X0),X1,sK1(k2_yellow_1(X0),X1,X2)) | k1_yellow_0(k2_yellow_1(X0),X2) = X1) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f229,f42])).
% 0.22/0.54  fof(f229,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~l1_orders_2(k2_yellow_1(X0)) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~r2_lattice3(k2_yellow_1(X0),X2,X1) | ~r1_orders_2(k2_yellow_1(X0),X1,sK1(k2_yellow_1(X0),X1,X2)) | k1_yellow_0(k2_yellow_1(X0),X2) = X1) )),
% 0.22/0.54    inference(resolution,[],[f57,f41])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r2_lattice3(X0,X2,X1) | ~r1_orders_2(X0,X1,sK1(X0,X1,X2)) | k1_yellow_0(X0,X2) = X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f31])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (30113)------------------------------
% 0.22/0.54  % (30113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (30113)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (30113)Memory used [KB]: 6396
% 0.22/0.54  % (30113)Time elapsed: 0.085 s
% 0.22/0.54  % (30113)------------------------------
% 0.22/0.54  % (30113)------------------------------
% 0.22/0.54  % (30134)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (30132)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (30106)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (30108)Refutation not found, incomplete strategy% (30108)------------------------------
% 0.22/0.54  % (30108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (30108)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (30108)Memory used [KB]: 10746
% 0.22/0.54  % (30108)Time elapsed: 0.124 s
% 0.22/0.54  % (30108)------------------------------
% 0.22/0.54  % (30108)------------------------------
% 0.22/0.54  % (30106)Refutation not found, incomplete strategy% (30106)------------------------------
% 0.22/0.54  % (30106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (30106)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (30106)Memory used [KB]: 1663
% 0.22/0.54  % (30106)Time elapsed: 0.124 s
% 0.22/0.54  % (30106)------------------------------
% 0.22/0.54  % (30106)------------------------------
% 0.22/0.54  % (30121)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.55  % (30104)Success in time 0.18 s
%------------------------------------------------------------------------------
