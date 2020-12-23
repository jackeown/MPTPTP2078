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
% DateTime   : Thu Dec  3 13:16:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 158 expanded)
%              Number of leaves         :   15 (  38 expanded)
%              Depth                    :   29
%              Number of atoms          :  417 ( 712 expanded)
%              Number of equality atoms :   44 ( 103 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f465,plain,(
    $false ),
    inference(subsumption_resolution,[],[f464,f41])).

fof(f41,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( k3_tarski(sK0) != k4_yellow_0(k2_yellow_1(sK0))
    & r2_hidden(k3_tarski(sK0),sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( k3_tarski(X0) != k4_yellow_0(k2_yellow_1(X0))
        & r2_hidden(k3_tarski(X0),X0)
        & ~ v1_xboole_0(X0) )
   => ( k3_tarski(sK0) != k4_yellow_0(k2_yellow_1(sK0))
      & r2_hidden(k3_tarski(sK0),sK0)
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( k3_tarski(X0) != k4_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k3_tarski(X0),X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( k3_tarski(X0) != k4_yellow_0(k2_yellow_1(X0))
      & r2_hidden(k3_tarski(X0),X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( r2_hidden(k3_tarski(X0),X0)
         => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

fof(f464,plain,(
    v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f463,f73])).

% (24909)Refutation not found, incomplete strategy% (24909)------------------------------
% (24909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24909)Termination reason: Refutation not found, incomplete strategy

% (24909)Memory used [KB]: 10618
% (24909)Time elapsed: 0.082 s
% (24909)------------------------------
% (24909)------------------------------
fof(f73,plain,(
    m1_subset_1(k3_tarski(sK0),sK0) ),
    inference(resolution,[],[f62,f42])).

fof(f42,plain,(
    r2_hidden(k3_tarski(sK0),sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f463,plain,
    ( ~ m1_subset_1(k3_tarski(sK0),sK0)
    | v1_xboole_0(sK0) ),
    inference(trivial_inequality_removal,[],[f453])).

fof(f453,plain,
    ( k3_tarski(sK0) != k3_tarski(sK0)
    | ~ m1_subset_1(k3_tarski(sK0),sK0)
    | v1_xboole_0(sK0) ),
    inference(superposition,[],[f43,f373])).

fof(f373,plain,(
    ! [X8] :
      ( k4_yellow_0(k2_yellow_1(X8)) = k3_tarski(X8)
      | ~ m1_subset_1(k3_tarski(X8),X8)
      | v1_xboole_0(X8) ) ),
    inference(subsumption_resolution,[],[f372,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_lattice3(k2_yellow_1(X0),k1_xboole_0,X1)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f75,f46])).

fof(f46,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r1_lattice3(k2_yellow_1(X0),k1_xboole_0,X1)
      | ~ l1_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f53,f47])).

fof(f47,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

% (24925)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f11,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_lattice3(X0,k1_xboole_0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_lattice3(X0,k1_xboole_0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_lattice3(X0,k1_xboole_0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

fof(f372,plain,(
    ! [X8] :
      ( k4_yellow_0(k2_yellow_1(X8)) = k3_tarski(X8)
      | ~ m1_subset_1(k3_tarski(X8),X8)
      | v1_xboole_0(X8)
      | ~ r1_lattice3(k2_yellow_1(X8),k1_xboole_0,k3_tarski(X8)) ) ),
    inference(subsumption_resolution,[],[f346,f46])).

fof(f346,plain,(
    ! [X8] :
      ( k4_yellow_0(k2_yellow_1(X8)) = k3_tarski(X8)
      | ~ m1_subset_1(k3_tarski(X8),X8)
      | v1_xboole_0(X8)
      | ~ r1_lattice3(k2_yellow_1(X8),k1_xboole_0,k3_tarski(X8))
      | ~ l1_orders_2(k2_yellow_1(X8)) ) ),
    inference(superposition,[],[f269,f52])).

fof(f52,plain,(
    ! [X0] :
      ( k4_yellow_0(X0) = k2_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k4_yellow_0(X0) = k2_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k4_yellow_0(X0) = k2_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_yellow_0)).

fof(f269,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = k2_yellow_0(k2_yellow_1(X0),X1)
      | ~ m1_subset_1(k3_tarski(X0),X0)
      | v1_xboole_0(X0)
      | ~ r1_lattice3(k2_yellow_1(X0),X1,k3_tarski(X0)) ) ),
    inference(duplicate_literal_removal,[],[f262])).

fof(f262,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(k2_yellow_1(X0),X1,k3_tarski(X0))
      | ~ m1_subset_1(k3_tarski(X0),X0)
      | v1_xboole_0(X0)
      | k3_tarski(X0) = k2_yellow_0(k2_yellow_1(X0),X1)
      | ~ r1_lattice3(k2_yellow_1(X0),X1,k3_tarski(X0))
      | ~ m1_subset_1(k3_tarski(X0),X0)
      | v1_xboole_0(X0)
      | k3_tarski(X0) = k2_yellow_0(k2_yellow_1(X0),X1) ) ),
    inference(resolution,[],[f184,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(k2_yellow_1(X0),X2,X1),X0)
      | ~ r1_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X0)
      | k2_yellow_0(k2_yellow_1(X0),X1) = X2 ) ),
    inference(resolution,[],[f113,f64])).

% (24907)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),X0)
      | k2_yellow_0(k2_yellow_1(X0),X2) = X1
      | ~ r1_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f112,f45])).

fof(f45,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
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
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),X0)
      | k2_yellow_0(k2_yellow_1(X0),X2) = X1
      | ~ r1_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f110,f46])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),X0)
      | k2_yellow_0(k2_yellow_1(X0),X2) = X1
      | ~ r1_lattice3(k2_yellow_1(X0),X2,X1)
      | ~ m1_subset_1(X1,X0)
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f56,f47])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | k2_yellow_0(X0,X2) = X1
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_yellow_0(X0,X2)
                  & k2_yellow_0(X0,X2) = X1 )
                | ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X1)
                  & r1_lattice3(X0,X2,sK1(X0,X1,X2))
                  & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X1)
          & r1_lattice3(X0,X2,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X1)
        & r1_lattice3(X0,X2,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(rectify,[],[f6])).

fof(f6,axiom,(
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

fof(f184,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK1(k2_yellow_1(X0),k3_tarski(X2),X1),X2)
      | ~ r1_lattice3(k2_yellow_1(X0),X1,k3_tarski(X2))
      | ~ m1_subset_1(k3_tarski(X2),X0)
      | v1_xboole_0(X0)
      | k2_yellow_0(k2_yellow_1(X0),X1) = k3_tarski(X2) ) ),
    inference(resolution,[],[f121,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(sK1(k2_yellow_1(X0),X2,X1),X2)
      | k2_yellow_0(k2_yellow_1(X0),X1) = X2
      | ~ r1_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | k2_yellow_0(k2_yellow_1(X0),X1) = X2
      | ~ r1_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ r1_tarski(sK1(k2_yellow_1(X0),X2,X1),X2)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f119,f47])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(k2_yellow_1(X0),X1) = X2
      | ~ r1_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,X0)
      | ~ r1_tarski(sK1(k2_yellow_1(X0),X2,X1),X2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f118,f113])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(k2_yellow_1(X0),X1) = X2
      | ~ r1_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),X0)
      | ~ r1_tarski(sK1(k2_yellow_1(X0),X2,X1),X2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f117,f45])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(k2_yellow_1(X0),X1) = X2
      | ~ r1_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ v5_orders_2(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),X0)
      | ~ r1_tarski(sK1(k2_yellow_1(X0),X2,X1),X2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f116,f46])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( k2_yellow_0(k2_yellow_1(X0),X1) = X2
      | ~ r1_lattice3(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),X0)
      | ~ r1_tarski(sK1(k2_yellow_1(X0),X2,X1),X2)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f58,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f98,f47])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f96,f47])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f95,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ~ v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v2_struct_0(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f94,f44])).

fof(f44,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f93,f46])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v3_orders_2(k2_yellow_1(X0))
      | v2_struct_0(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f65,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ r1_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f69,f47])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f51,f47])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X1,X2)
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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

% (24907)Refutation not found, incomplete strategy% (24907)------------------------------
% (24907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24907)Termination reason: Refutation not found, incomplete strategy

% (24907)Memory used [KB]: 10618
% (24907)Time elapsed: 0.085 s
% (24907)------------------------------
% (24907)------------------------------
fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X1)
      | k2_yellow_0(X0,X2) = X1
      | ~ r1_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f43,plain,(
    k3_tarski(sK0) != k4_yellow_0(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:19:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.43  % (24914)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.48  % (24920)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (24906)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (24912)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (24906)Refutation not found, incomplete strategy% (24906)------------------------------
% 0.22/0.48  % (24906)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (24906)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (24906)Memory used [KB]: 6140
% 0.22/0.48  % (24906)Time elapsed: 0.055 s
% 0.22/0.48  % (24906)------------------------------
% 0.22/0.48  % (24906)------------------------------
% 0.22/0.49  % (24908)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (24916)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.49  % (24911)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (24916)Refutation not found, incomplete strategy% (24916)------------------------------
% 0.22/0.49  % (24916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (24916)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (24916)Memory used [KB]: 6140
% 0.22/0.49  % (24916)Time elapsed: 0.071 s
% 0.22/0.49  % (24916)------------------------------
% 0.22/0.49  % (24916)------------------------------
% 0.22/0.49  % (24910)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (24909)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (24922)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.50  % (24908)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f465,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(subsumption_resolution,[],[f464,f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ~v1_xboole_0(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    k3_tarski(sK0) != k4_yellow_0(k2_yellow_1(sK0)) & r2_hidden(k3_tarski(sK0),sK0) & ~v1_xboole_0(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ? [X0] : (k3_tarski(X0) != k4_yellow_0(k2_yellow_1(X0)) & r2_hidden(k3_tarski(X0),X0) & ~v1_xboole_0(X0)) => (k3_tarski(sK0) != k4_yellow_0(k2_yellow_1(sK0)) & r2_hidden(k3_tarski(sK0),sK0) & ~v1_xboole_0(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ? [X0] : (k3_tarski(X0) != k4_yellow_0(k2_yellow_1(X0)) & r2_hidden(k3_tarski(X0),X0) & ~v1_xboole_0(X0))),
% 0.22/0.50    inference(flattening,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ? [X0] : ((k3_tarski(X0) != k4_yellow_0(k2_yellow_1(X0)) & r2_hidden(k3_tarski(X0),X0)) & ~v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,negated_conjecture,(
% 0.22/0.50    ~! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 0.22/0.50    inference(negated_conjecture,[],[f13])).
% 0.22/0.50  fof(f13,conjecture,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).
% 0.22/0.50  fof(f464,plain,(
% 0.22/0.50    v1_xboole_0(sK0)),
% 0.22/0.50    inference(subsumption_resolution,[],[f463,f73])).
% 0.22/0.50  % (24909)Refutation not found, incomplete strategy% (24909)------------------------------
% 0.22/0.50  % (24909)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (24909)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (24909)Memory used [KB]: 10618
% 0.22/0.50  % (24909)Time elapsed: 0.082 s
% 0.22/0.50  % (24909)------------------------------
% 0.22/0.50  % (24909)------------------------------
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    m1_subset_1(k3_tarski(sK0),sK0)),
% 0.22/0.50    inference(resolution,[],[f62,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    r2_hidden(k3_tarski(sK0),sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.50  fof(f463,plain,(
% 0.22/0.50    ~m1_subset_1(k3_tarski(sK0),sK0) | v1_xboole_0(sK0)),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f453])).
% 0.22/0.50  fof(f453,plain,(
% 0.22/0.50    k3_tarski(sK0) != k3_tarski(sK0) | ~m1_subset_1(k3_tarski(sK0),sK0) | v1_xboole_0(sK0)),
% 0.22/0.50    inference(superposition,[],[f43,f373])).
% 0.22/0.50  fof(f373,plain,(
% 0.22/0.50    ( ! [X8] : (k4_yellow_0(k2_yellow_1(X8)) = k3_tarski(X8) | ~m1_subset_1(k3_tarski(X8),X8) | v1_xboole_0(X8)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f372,f76])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_lattice3(k2_yellow_1(X0),k1_xboole_0,X1) | ~m1_subset_1(X1,X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f75,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 0.22/0.50    inference(pure_predicate_removal,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r1_lattice3(k2_yellow_1(X0),k1_xboole_0,X1) | ~l1_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.50    inference(superposition,[],[f53,f47])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  % (24925)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | r1_lattice3(X0,k1_xboole_0,X1) | ~l1_orders_2(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (r1_lattice3(X0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_lattice3(X0,k1_xboole_0,X1)))),
% 0.22/0.50    inference(pure_predicate_removal,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (r1_lattice3(X0,k1_xboole_0,X1) & r2_lattice3(X0,k1_xboole_0,X1))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).
% 0.22/0.50  fof(f372,plain,(
% 0.22/0.50    ( ! [X8] : (k4_yellow_0(k2_yellow_1(X8)) = k3_tarski(X8) | ~m1_subset_1(k3_tarski(X8),X8) | v1_xboole_0(X8) | ~r1_lattice3(k2_yellow_1(X8),k1_xboole_0,k3_tarski(X8))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f346,f46])).
% 0.22/0.50  fof(f346,plain,(
% 0.22/0.50    ( ! [X8] : (k4_yellow_0(k2_yellow_1(X8)) = k3_tarski(X8) | ~m1_subset_1(k3_tarski(X8),X8) | v1_xboole_0(X8) | ~r1_lattice3(k2_yellow_1(X8),k1_xboole_0,k3_tarski(X8)) | ~l1_orders_2(k2_yellow_1(X8))) )),
% 0.22/0.50    inference(superposition,[],[f269,f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X0] : (k4_yellow_0(X0) = k2_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0] : (k4_yellow_0(X0) = k2_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : (l1_orders_2(X0) => k4_yellow_0(X0) = k2_yellow_0(X0,k1_xboole_0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_yellow_0)).
% 0.22/0.50  fof(f269,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_tarski(X0) = k2_yellow_0(k2_yellow_1(X0),X1) | ~m1_subset_1(k3_tarski(X0),X0) | v1_xboole_0(X0) | ~r1_lattice3(k2_yellow_1(X0),X1,k3_tarski(X0))) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f262])).
% 0.22/0.50  fof(f262,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_lattice3(k2_yellow_1(X0),X1,k3_tarski(X0)) | ~m1_subset_1(k3_tarski(X0),X0) | v1_xboole_0(X0) | k3_tarski(X0) = k2_yellow_0(k2_yellow_1(X0),X1) | ~r1_lattice3(k2_yellow_1(X0),X1,k3_tarski(X0)) | ~m1_subset_1(k3_tarski(X0),X0) | v1_xboole_0(X0) | k3_tarski(X0) = k2_yellow_0(k2_yellow_1(X0),X1)) )),
% 0.22/0.50    inference(resolution,[],[f184,f114])).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r2_hidden(sK1(k2_yellow_1(X0),X2,X1),X0) | ~r1_lattice3(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | v1_xboole_0(X0) | k2_yellow_0(k2_yellow_1(X0),X1) = X2) )),
% 0.22/0.50    inference(resolution,[],[f113,f64])).
% 0.22/0.50  % (24907)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.50    inference(flattening,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),X0) | k2_yellow_0(k2_yellow_1(X0),X2) = X1 | ~r1_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X1,X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f112,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 0.22/0.50    inference(pure_predicate_removal,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.22/0.50    inference(pure_predicate_removal,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.22/0.50  fof(f112,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),X0) | k2_yellow_0(k2_yellow_1(X0),X2) = X1 | ~r1_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X1,X0) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f110,f46])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (m1_subset_1(sK1(k2_yellow_1(X0),X1,X2),X0) | k2_yellow_0(k2_yellow_1(X0),X2) = X1 | ~r1_lattice3(k2_yellow_1(X0),X2,X1) | ~m1_subset_1(X1,X0) | ~l1_orders_2(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.50    inference(superposition,[],[f56,f47])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | k2_yellow_0(X0,X2) = X1 | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | (~r1_orders_2(X0,sK1(X0,X1,X2),X1) & r1_lattice3(X0,X2,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | ~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK1(X0,X1,X2),X1) & r1_lattice3(X0,X2,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | ? [X3] : (~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | ~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.22/0.50    inference(flattening,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) | (? [X3] : ((~r1_orders_2(X0,X3,X1) & r1_lattice3(X0,X2,X3)) & m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X2,X1))) & ((! [X4] : ((r1_orders_2(X0,X4,X1) | ~r1_lattice3(X0,X2,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_lattice3(X0,X2,X1)) | (~r2_yellow_0(X0,X2) | k2_yellow_0(X0,X2) != X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1)) => (r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1)) & ((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) => (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X4) => r1_orders_2(X0,X4,X1))) & r1_lattice3(X0,X2,X1))))))),
% 0.22/0.50    inference(rectify,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (((! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1)) => (r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1)) & ((r2_yellow_0(X0,X2) & k2_yellow_0(X0,X2) = X1) => (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X2,X3) => r1_orders_2(X0,X3,X1))) & r1_lattice3(X0,X2,X1))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_yellow_0)).
% 0.22/0.50  fof(f184,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r2_hidden(sK1(k2_yellow_1(X0),k3_tarski(X2),X1),X2) | ~r1_lattice3(k2_yellow_1(X0),X1,k3_tarski(X2)) | ~m1_subset_1(k3_tarski(X2),X0) | v1_xboole_0(X0) | k2_yellow_0(k2_yellow_1(X0),X1) = k3_tarski(X2)) )),
% 0.22/0.50    inference(resolution,[],[f121,f63])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_tarski(sK1(k2_yellow_1(X0),X2,X1),X2) | k2_yellow_0(k2_yellow_1(X0),X1) = X2 | ~r1_lattice3(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f120])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | k2_yellow_0(k2_yellow_1(X0),X1) = X2 | ~r1_lattice3(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | ~r1_tarski(sK1(k2_yellow_1(X0),X2,X1),X2) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f119,f47])).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k2_yellow_0(k2_yellow_1(X0),X1) = X2 | ~r1_lattice3(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,X0) | ~r1_tarski(sK1(k2_yellow_1(X0),X2,X1),X2) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f118,f113])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k2_yellow_0(k2_yellow_1(X0),X1) = X2 | ~r1_lattice3(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,X0) | ~m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),X0) | ~r1_tarski(sK1(k2_yellow_1(X0),X2,X1),X2) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f117,f45])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k2_yellow_0(k2_yellow_1(X0),X1) = X2 | ~r1_lattice3(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~v5_orders_2(k2_yellow_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),X0) | ~r1_tarski(sK1(k2_yellow_1(X0),X2,X1),X2) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f116,f46])).
% 0.22/0.50  fof(f116,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k2_yellow_0(k2_yellow_1(X0),X1) = X2 | ~r1_lattice3(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~l1_orders_2(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(sK1(k2_yellow_1(X0),X2,X1),X0) | ~r1_tarski(sK1(k2_yellow_1(X0),X2,X1),X2) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(resolution,[],[f58,f100])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f99])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | ~m1_subset_1(X2,X0) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f98,f47])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f97])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f96,f47])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f95,f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(X0) => ~v2_struct_0(k2_yellow_1(X0)))),
% 0.22/0.50    inference(pure_predicate_removal,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f94,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f93,f46])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~l1_orders_2(k2_yellow_1(X0)) | ~v3_orders_2(k2_yellow_1(X0)) | v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(resolution,[],[f65,f70])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~r1_tarski(X1,X2) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f69,f47])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f51,f47])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,axiom,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r3_orders_2(X0,X1,X2) | r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f33])).
% 0.22/0.50  % (24907)Refutation not found, incomplete strategy% (24907)------------------------------
% 0.22/0.50  % (24907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (24907)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (24907)Memory used [KB]: 10618
% 0.22/0.50  % (24907)Time elapsed: 0.085 s
% 0.22/0.50  % (24907)------------------------------
% 0.22/0.50  % (24907)------------------------------
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_orders_2(X0,sK1(X0,X1,X2),X1) | k2_yellow_0(X0,X2) = X1 | ~r1_lattice3(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f39])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    k3_tarski(sK0) != k4_yellow_0(k2_yellow_1(sK0))),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (24908)------------------------------
% 0.22/0.50  % (24908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (24908)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (24908)Memory used [KB]: 10746
% 0.22/0.50  % (24908)Time elapsed: 0.079 s
% 0.22/0.50  % (24908)------------------------------
% 0.22/0.50  % (24908)------------------------------
% 0.22/0.51  % (24905)Success in time 0.137 s
%------------------------------------------------------------------------------
