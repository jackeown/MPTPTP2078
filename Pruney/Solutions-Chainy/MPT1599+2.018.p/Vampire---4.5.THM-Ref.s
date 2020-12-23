%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:31 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  156 (1813 expanded)
%              Number of leaves         :   18 ( 611 expanded)
%              Depth                    :   42
%              Number of atoms          :  669 (7197 expanded)
%              Number of equality atoms :   38 ( 636 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f381,plain,(
    $false ),
    inference(subsumption_resolution,[],[f380,f51])).

fof(f51,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f41])).

% (31964)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f41,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k3_xboole_0(sK3,sK4))
    & m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    & v2_lattice3(k2_yellow_1(sK2))
    & ~ v1_xboole_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f40,f39,f38])).

% (31962)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
                & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
            & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
        & v2_lattice3(k2_yellow_1(X0))
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2))) )
      & v2_lattice3(k2_yellow_1(sK2))
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),X1,X2),k3_xboole_0(X1,X2))
            & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2))) )
        & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,X2),k3_xboole_0(sK3,X2))
          & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2))) )
      & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,X2),k3_xboole_0(sK3,X2))
        & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2))) )
   => ( ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k3_xboole_0(sK3,sK4))
      & m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v2_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

% (31939)Refutation not found, incomplete strategy% (31939)------------------------------
% (31939)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31939)Termination reason: Refutation not found, incomplete strategy

% (31939)Memory used [KB]: 10746
% (31939)Time elapsed: 0.128 s
% (31939)------------------------------
% (31939)------------------------------
fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( v2_lattice3(k2_yellow_1(X0))
         => ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v2_lattice3(k2_yellow_1(X0))
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_1)).

fof(f380,plain,(
    v1_xboole_0(sK2) ),
    inference(resolution,[],[f379,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ~ v2_struct_0(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).

fof(f379,plain,(
    v2_struct_0(k2_yellow_1(sK2)) ),
    inference(subsumption_resolution,[],[f376,f338])).

fof(f338,plain,
    ( r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | v2_struct_0(k2_yellow_1(sK2)) ),
    inference(subsumption_resolution,[],[f337,f52])).

fof(f52,plain,(
    v2_lattice3(k2_yellow_1(sK2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f337,plain,
    ( r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | v2_struct_0(k2_yellow_1(sK2))
    | ~ v2_lattice3(k2_yellow_1(sK2)) ),
    inference(subsumption_resolution,[],[f336,f82])).

fof(f82,plain,(
    m1_subset_1(sK3,sK2) ),
    inference(backward_demodulation,[],[f53,f59])).

fof(f59,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f53,plain,(
    m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) ),
    inference(cnf_transformation,[],[f41])).

fof(f336,plain,
    ( r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | v2_struct_0(k2_yellow_1(sK2))
    | ~ m1_subset_1(sK3,sK2)
    | ~ v2_lattice3(k2_yellow_1(sK2)) ),
    inference(subsumption_resolution,[],[f335,f83])).

fof(f83,plain,(
    m1_subset_1(sK4,sK2) ),
    inference(backward_demodulation,[],[f54,f59])).

fof(f54,plain,(
    m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) ),
    inference(cnf_transformation,[],[f41])).

fof(f335,plain,
    ( r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | v2_struct_0(k2_yellow_1(sK2))
    | ~ m1_subset_1(sK4,sK2)
    | ~ m1_subset_1(sK3,sK2)
    | ~ v2_lattice3(k2_yellow_1(sK2)) ),
    inference(resolution,[],[f334,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k12_lattice3(k2_yellow_1(X0),X1,X2),X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ v2_lattice3(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f123,f57])).

fof(f57,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k12_lattice3(k2_yellow_1(X0),X1,X2),X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ v2_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f122,f58])).

fof(f58,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k12_lattice3(k2_yellow_1(X0),X1,X2),X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v2_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f78,f59])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

% (31966)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k12_lattice3)).

fof(f334,plain,
    ( ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | v2_struct_0(k2_yellow_1(sK2)) ),
    inference(subsumption_resolution,[],[f333,f51])).

fof(f333,plain,
    ( v2_struct_0(k2_yellow_1(sK2))
    | r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f330,f83])).

% (31962)Refutation not found, incomplete strategy% (31962)------------------------------
% (31962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31961)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (31962)Termination reason: Refutation not found, incomplete strategy

% (31962)Memory used [KB]: 6268
% (31962)Time elapsed: 0.131 s
% (31962)------------------------------
% (31962)------------------------------
fof(f330,plain,
    ( v2_struct_0(k2_yellow_1(sK2))
    | ~ m1_subset_1(sK4,sK2)
    | r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f329,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f86,f59])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f62,f59])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f329,plain,
    ( r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | v2_struct_0(k2_yellow_1(sK2)) ),
    inference(subsumption_resolution,[],[f328,f52])).

fof(f328,plain,
    ( v2_struct_0(k2_yellow_1(sK2))
    | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ v2_lattice3(k2_yellow_1(sK2)) ),
    inference(subsumption_resolution,[],[f327,f82])).

% (31947)Refutation not found, incomplete strategy% (31947)------------------------------
% (31947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31947)Termination reason: Refutation not found, incomplete strategy

% (31947)Memory used [KB]: 10618
% (31947)Time elapsed: 0.126 s
% (31947)------------------------------
% (31947)------------------------------
fof(f327,plain,
    ( v2_struct_0(k2_yellow_1(sK2))
    | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ m1_subset_1(sK3,sK2)
    | ~ v2_lattice3(k2_yellow_1(sK2)) ),
    inference(subsumption_resolution,[],[f326,f83])).

fof(f326,plain,
    ( v2_struct_0(k2_yellow_1(sK2))
    | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ m1_subset_1(sK4,sK2)
    | ~ m1_subset_1(sK3,sK2)
    | ~ v2_lattice3(k2_yellow_1(sK2)) ),
    inference(resolution,[],[f286,f124])).

fof(f286,plain,
    ( ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | v2_struct_0(k2_yellow_1(sK2))
    | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) ),
    inference(forward_demodulation,[],[f285,f59])).

fof(f285,plain,
    ( v2_struct_0(k2_yellow_1(sK2))
    | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) ),
    inference(subsumption_resolution,[],[f284,f83])).

fof(f284,plain,
    ( ~ m1_subset_1(sK4,sK2)
    | v2_struct_0(k2_yellow_1(sK2))
    | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) ),
    inference(forward_demodulation,[],[f283,f59])).

fof(f283,plain,
    ( v2_struct_0(k2_yellow_1(sK2))
    | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) ),
    inference(subsumption_resolution,[],[f282,f56])).

fof(f56,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f282,plain,
    ( v2_struct_0(k2_yellow_1(sK2))
    | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ v3_orders_2(k2_yellow_1(sK2)) ),
    inference(subsumption_resolution,[],[f281,f58])).

fof(f281,plain,
    ( v2_struct_0(k2_yellow_1(sK2))
    | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ l1_orders_2(k2_yellow_1(sK2))
    | ~ v3_orders_2(k2_yellow_1(sK2)) ),
    inference(duplicate_literal_removal,[],[f276])).

fof(f276,plain,
    ( v2_struct_0(k2_yellow_1(sK2))
    | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ l1_orders_2(k2_yellow_1(sK2))
    | ~ v3_orders_2(k2_yellow_1(sK2))
    | v2_struct_0(k2_yellow_1(sK2)) ),
    inference(resolution,[],[f274,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f274,plain,
    ( r1_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | v2_struct_0(k2_yellow_1(sK2)) ),
    inference(resolution,[],[f272,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | r1_orders_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ~ r1_orders_2(X1,sK5(X0,X1,X2,X3),X0)
          & r1_orders_2(X1,sK5(X0,X1,X2,X3),X2)
          & r1_orders_2(X1,sK5(X0,X1,X2,X3),X3)
          & m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X1)) )
        | ~ r1_orders_2(X1,X0,X2)
        | ~ r1_orders_2(X1,X0,X3) )
      & ( ( ! [X5] :
              ( r1_orders_2(X1,X5,X0)
              | ~ r1_orders_2(X1,X5,X2)
              | ~ r1_orders_2(X1,X5,X3)
              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
          & r1_orders_2(X1,X0,X2)
          & r1_orders_2(X1,X0,X3) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f47,f48])).

fof(f48,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X1,X4,X0)
          & r1_orders_2(X1,X4,X2)
          & r1_orders_2(X1,X4,X3)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,sK5(X0,X1,X2,X3),X0)
        & r1_orders_2(X1,sK5(X0,X1,X2,X3),X2)
        & r1_orders_2(X1,sK5(X0,X1,X2,X3),X3)
        & m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ~ r1_orders_2(X1,X4,X0)
            & r1_orders_2(X1,X4,X2)
            & r1_orders_2(X1,X4,X3)
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ r1_orders_2(X1,X0,X2)
        | ~ r1_orders_2(X1,X0,X3) )
      & ( ( ! [X5] :
              ( r1_orders_2(X1,X5,X0)
              | ~ r1_orders_2(X1,X5,X2)
              | ~ r1_orders_2(X1,X5,X3)
              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
          & r1_orders_2(X1,X0,X2)
          & r1_orders_2(X1,X0,X3) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f46])).

% (31963)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f46,plain,(
    ! [X3,X0,X2,X1] :
      ( ( sP0(X3,X0,X2,X1)
        | ? [X4] :
            ( ~ r1_orders_2(X0,X4,X3)
            & r1_orders_2(X0,X4,X2)
            & r1_orders_2(X0,X4,X1)
            & m1_subset_1(X4,u1_struct_0(X0)) )
        | ~ r1_orders_2(X0,X3,X2)
        | ~ r1_orders_2(X0,X3,X1) )
      & ( ( ! [X4] :
              ( r1_orders_2(X0,X4,X3)
              | ~ r1_orders_2(X0,X4,X2)
              | ~ r1_orders_2(X0,X4,X1)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r1_orders_2(X0,X3,X2)
          & r1_orders_2(X0,X3,X1) )
        | ~ sP0(X3,X0,X2,X1) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X3,X0,X2,X1] :
      ( ( sP0(X3,X0,X2,X1)
        | ? [X4] :
            ( ~ r1_orders_2(X0,X4,X3)
            & r1_orders_2(X0,X4,X2)
            & r1_orders_2(X0,X4,X1)
            & m1_subset_1(X4,u1_struct_0(X0)) )
        | ~ r1_orders_2(X0,X3,X2)
        | ~ r1_orders_2(X0,X3,X1) )
      & ( ( ! [X4] :
              ( r1_orders_2(X0,X4,X3)
              | ~ r1_orders_2(X0,X4,X2)
              | ~ r1_orders_2(X0,X4,X1)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r1_orders_2(X0,X3,X2)
          & r1_orders_2(X0,X3,X1) )
        | ~ sP0(X3,X0,X2,X1) ) ) ),
    inference(nnf_transformation,[],[f35])).

% (31959)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f35,plain,(
    ! [X3,X0,X2,X1] :
      ( sP0(X3,X0,X2,X1)
    <=> ( ! [X4] :
            ( r1_orders_2(X0,X4,X3)
            | ~ r1_orders_2(X0,X4,X2)
            | ~ r1_orders_2(X0,X4,X1)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r1_orders_2(X0,X3,X2)
        & r1_orders_2(X0,X3,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f272,plain,
    ( sP0(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),k2_yellow_1(sK2),sK4,sK3)
    | v2_struct_0(k2_yellow_1(sK2)) ),
    inference(subsumption_resolution,[],[f270,f83])).

fof(f270,plain,
    ( ~ m1_subset_1(sK4,sK2)
    | v2_struct_0(k2_yellow_1(sK2))
    | sP0(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),k2_yellow_1(sK2),sK4,sK3) ),
    inference(resolution,[],[f248,f194])).

fof(f194,plain,
    ( ~ sP1(sK3,sK4,k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | sP0(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),k2_yellow_1(sK2),sK4,sK3) ),
    inference(forward_demodulation,[],[f192,f188])).

fof(f188,plain,(
    k12_lattice3(k2_yellow_1(sK2),sK4,sK3) = k12_lattice3(k2_yellow_1(sK2),sK3,sK4) ),
    inference(backward_demodulation,[],[f177,f185])).

fof(f185,plain,(
    k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k12_lattice3(k2_yellow_1(sK2),sK3,sK4) ),
    inference(resolution,[],[f171,f82])).

fof(f171,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,sK2)
      | k11_lattice3(k2_yellow_1(sK2),X1,sK4) = k12_lattice3(k2_yellow_1(sK2),X1,sK4) ) ),
    inference(resolution,[],[f169,f83])).

fof(f169,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,sK2)
      | ~ m1_subset_1(X1,sK2)
      | k11_lattice3(k2_yellow_1(sK2),X1,X0) = k12_lattice3(k2_yellow_1(sK2),X1,X0) ) ),
    inference(forward_demodulation,[],[f168,f59])).

% (31954)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f168,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,sK2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2)))
      | k11_lattice3(k2_yellow_1(sK2),X1,X0) = k12_lattice3(k2_yellow_1(sK2),X1,X0) ) ),
    inference(forward_demodulation,[],[f167,f59])).

fof(f167,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK2)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2)))
      | k11_lattice3(k2_yellow_1(sK2),X1,X0) = k12_lattice3(k2_yellow_1(sK2),X1,X0) ) ),
    inference(subsumption_resolution,[],[f166,f57])).

fof(f166,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK2)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2)))
      | k11_lattice3(k2_yellow_1(sK2),X1,X0) = k12_lattice3(k2_yellow_1(sK2),X1,X0)
      | ~ v5_orders_2(k2_yellow_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f165,f58])).

fof(f165,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK2)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2)))
      | ~ l1_orders_2(k2_yellow_1(sK2))
      | k11_lattice3(k2_yellow_1(sK2),X1,X0) = k12_lattice3(k2_yellow_1(sK2),X1,X0)
      | ~ v5_orders_2(k2_yellow_1(sK2)) ) ),
    inference(resolution,[],[f79,f52])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f177,plain,(
    k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k12_lattice3(k2_yellow_1(sK2),sK4,sK3) ),
    inference(backward_demodulation,[],[f157,f175])).

fof(f175,plain,(
    k11_lattice3(k2_yellow_1(sK2),sK4,sK3) = k12_lattice3(k2_yellow_1(sK2),sK4,sK3) ),
    inference(resolution,[],[f170,f83])).

fof(f170,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK2)
      | k11_lattice3(k2_yellow_1(sK2),X0,sK3) = k12_lattice3(k2_yellow_1(sK2),X0,sK3) ) ),
    inference(resolution,[],[f169,f82])).

fof(f157,plain,(
    k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,sK3) ),
    inference(resolution,[],[f152,f83])).

% (31954)Refutation not found, incomplete strategy% (31954)------------------------------
% (31954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31954)Termination reason: Refutation not found, incomplete strategy

% (31954)Memory used [KB]: 10618
% (31954)Time elapsed: 0.139 s
% (31954)------------------------------
% (31954)------------------------------
fof(f152,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK2)
      | k11_lattice3(k2_yellow_1(sK2),X0,sK3) = k11_lattice3(k2_yellow_1(sK2),sK3,X0) ) ),
    inference(resolution,[],[f151,f82])).

fof(f151,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,sK2)
      | ~ m1_subset_1(X1,sK2)
      | k11_lattice3(k2_yellow_1(sK2),X1,X0) = k11_lattice3(k2_yellow_1(sK2),X0,X1) ) ),
    inference(forward_demodulation,[],[f150,f59])).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,sK2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2)))
      | k11_lattice3(k2_yellow_1(sK2),X1,X0) = k11_lattice3(k2_yellow_1(sK2),X0,X1) ) ),
    inference(forward_demodulation,[],[f149,f59])).

fof(f149,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK2)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2)))
      | k11_lattice3(k2_yellow_1(sK2),X1,X0) = k11_lattice3(k2_yellow_1(sK2),X0,X1) ) ),
    inference(subsumption_resolution,[],[f148,f57])).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK2)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2)))
      | k11_lattice3(k2_yellow_1(sK2),X1,X0) = k11_lattice3(k2_yellow_1(sK2),X0,X1)
      | ~ v5_orders_2(k2_yellow_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f147,f58])).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK2)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2)))
      | ~ l1_orders_2(k2_yellow_1(sK2))
      | k11_lattice3(k2_yellow_1(sK2),X1,X0) = k11_lattice3(k2_yellow_1(sK2),X0,X1)
      | ~ v5_orders_2(k2_yellow_1(sK2)) ) ),
    inference(resolution,[],[f74,f52])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_lattice3(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_lattice3)).

fof(f192,plain,
    ( ~ sP1(sK3,sK4,k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4))
    | sP0(k12_lattice3(k2_yellow_1(sK2),sK4,sK3),k2_yellow_1(sK2),sK4,sK3) ),
    inference(backward_demodulation,[],[f184,f188])).

fof(f184,plain,
    ( ~ sP1(sK3,sK4,k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK4,sK3))
    | sP0(k12_lattice3(k2_yellow_1(sK2),sK4,sK3),k2_yellow_1(sK2),sK4,sK3) ),
    inference(superposition,[],[f81,f177])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2,k11_lattice3(X2,X0,X1))
      | sP0(k11_lattice3(X2,X0,X1),X2,X1,X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X3,X2,X1,X0)
      | k11_lattice3(X2,X0,X1) != X3
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k11_lattice3(X2,X0,X1) = X3
          | ~ sP0(X3,X2,X1,X0) )
        & ( sP0(X3,X2,X1,X0)
          | k11_lattice3(X2,X0,X1) != X3 ) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X1,X2,X0,X3] :
      ( ( ( k11_lattice3(X0,X1,X2) = X3
          | ~ sP0(X3,X0,X2,X1) )
        & ( sP0(X3,X0,X2,X1)
          | k11_lattice3(X0,X1,X2) != X3 ) )
      | ~ sP1(X1,X2,X0,X3) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X1,X2,X0,X3] :
      ( ( k11_lattice3(X0,X1,X2) = X3
      <=> sP0(X3,X0,X2,X1) )
      | ~ sP1(X1,X2,X0,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f248,plain,(
    ! [X1] :
      ( sP1(sK3,sK4,k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,X1))
      | ~ m1_subset_1(X1,sK2)
      | v2_struct_0(k2_yellow_1(sK2)) ) ),
    inference(resolution,[],[f243,f83])).

fof(f243,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,sK2)
      | v2_struct_0(k2_yellow_1(sK2))
      | ~ m1_subset_1(X1,sK2)
      | sP1(sK3,X0,k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,X1)) ) ),
    inference(resolution,[],[f230,f82])).

fof(f230,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X3,sK2)
      | sP1(sK3,X2,k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),X3,X4))
      | v2_struct_0(k2_yellow_1(sK2))
      | ~ m1_subset_1(X4,sK2)
      | ~ m1_subset_1(X2,sK2) ) ),
    inference(subsumption_resolution,[],[f229,f52])).

fof(f229,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X2,sK2)
      | sP1(sK3,X2,k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),X3,X4))
      | v2_struct_0(k2_yellow_1(sK2))
      | ~ m1_subset_1(X4,sK2)
      | ~ m1_subset_1(X3,sK2)
      | ~ v2_lattice3(k2_yellow_1(sK2)) ) ),
    inference(resolution,[],[f223,f124])).

fof(f223,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,sK2)
      | ~ m1_subset_1(X0,sK2)
      | sP1(sK3,X0,k2_yellow_1(sK2),X1)
      | v2_struct_0(k2_yellow_1(sK2)) ) ),
    inference(resolution,[],[f222,f82])).

fof(f222,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,sK2)
      | ~ m1_subset_1(X1,sK2)
      | ~ m1_subset_1(X0,sK2)
      | sP1(X2,X1,k2_yellow_1(sK2),X0)
      | v2_struct_0(k2_yellow_1(sK2)) ) ),
    inference(forward_demodulation,[],[f221,f59])).

% (31959)Refutation not found, incomplete strategy% (31959)------------------------------
% (31959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31959)Termination reason: Refutation not found, incomplete strategy

% (31959)Memory used [KB]: 10746
% (31959)Time elapsed: 0.140 s
% (31959)------------------------------
% (31959)------------------------------
fof(f221,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,sK2)
      | ~ m1_subset_1(X0,sK2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2)))
      | sP1(X2,X1,k2_yellow_1(sK2),X0)
      | v2_struct_0(k2_yellow_1(sK2)) ) ),
    inference(forward_demodulation,[],[f220,f59])).

fof(f220,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,sK2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2)))
      | sP1(X2,X1,k2_yellow_1(sK2),X0)
      | v2_struct_0(k2_yellow_1(sK2)) ) ),
    inference(forward_demodulation,[],[f219,f59])).

% (31957)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (31963)Refutation not found, incomplete strategy% (31963)------------------------------
% (31963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31963)Termination reason: Refutation not found, incomplete strategy

% (31963)Memory used [KB]: 10746
% (31963)Time elapsed: 0.142 s
% (31963)------------------------------
% (31963)------------------------------
fof(f219,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK2)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2)))
      | sP1(X2,X1,k2_yellow_1(sK2),X0)
      | v2_struct_0(k2_yellow_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f218,f57])).

% (31946)Refutation not found, incomplete strategy% (31946)------------------------------
% (31946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31946)Termination reason: Refutation not found, incomplete strategy

% (31946)Memory used [KB]: 10618
% (31946)Time elapsed: 0.142 s
% (31946)------------------------------
% (31946)------------------------------
fof(f218,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK2)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2)))
      | sP1(X2,X1,k2_yellow_1(sK2),X0)
      | ~ v5_orders_2(k2_yellow_1(sK2))
      | v2_struct_0(k2_yellow_1(sK2)) ) ),
    inference(subsumption_resolution,[],[f217,f58])).

fof(f217,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK2)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2)))
      | ~ l1_orders_2(k2_yellow_1(sK2))
      | sP1(X2,X1,k2_yellow_1(sK2),X0)
      | ~ v5_orders_2(k2_yellow_1(sK2))
      | v2_struct_0(k2_yellow_1(sK2)) ) ),
    inference(resolution,[],[f73,f52])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_lattice3(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | sP1(X1,X2,X0,X3)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( sP1(X1,X2,X0,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f24,f36,f35])).

% (31945)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l28_lattice3)).

fof(f376,plain,
    ( ~ r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)
    | v2_struct_0(k2_yellow_1(sK2)) ),
    inference(resolution,[],[f355,f190])).

fof(f190,plain,(
    ~ r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),k3_xboole_0(sK3,sK4)) ),
    inference(backward_demodulation,[],[f179,f188])).

fof(f179,plain,(
    ~ r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK4,sK3),k3_xboole_0(sK3,sK4)) ),
    inference(backward_demodulation,[],[f55,f177])).

fof(f55,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k3_xboole_0(sK3,sK4)) ),
    inference(cnf_transformation,[],[f41])).

fof(f355,plain,(
    ! [X1] :
      ( r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),k3_xboole_0(sK3,X1))
      | ~ r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),X1)
      | v2_struct_0(k2_yellow_1(sK2)) ) ),
    inference(resolution,[],[f353,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f353,plain,
    ( r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | v2_struct_0(k2_yellow_1(sK2)) ),
    inference(subsumption_resolution,[],[f352,f52])).

fof(f352,plain,
    ( r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | v2_struct_0(k2_yellow_1(sK2))
    | ~ v2_lattice3(k2_yellow_1(sK2)) ),
    inference(subsumption_resolution,[],[f351,f82])).

fof(f351,plain,
    ( r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | v2_struct_0(k2_yellow_1(sK2))
    | ~ m1_subset_1(sK3,sK2)
    | ~ v2_lattice3(k2_yellow_1(sK2)) ),
    inference(subsumption_resolution,[],[f350,f83])).

fof(f350,plain,
    ( r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | v2_struct_0(k2_yellow_1(sK2))
    | ~ m1_subset_1(sK4,sK2)
    | ~ m1_subset_1(sK3,sK2)
    | ~ v2_lattice3(k2_yellow_1(sK2)) ),
    inference(resolution,[],[f349,f124])).

fof(f349,plain,
    ( ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | v2_struct_0(k2_yellow_1(sK2)) ),
    inference(subsumption_resolution,[],[f348,f51])).

fof(f348,plain,
    ( v2_struct_0(k2_yellow_1(sK2))
    | r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f345,f82])).

fof(f345,plain,
    ( v2_struct_0(k2_yellow_1(sK2))
    | ~ m1_subset_1(sK3,sK2)
    | r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f344,f87])).

fof(f344,plain,
    ( r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | v2_struct_0(k2_yellow_1(sK2)) ),
    inference(subsumption_resolution,[],[f343,f52])).

fof(f343,plain,
    ( v2_struct_0(k2_yellow_1(sK2))
    | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ v2_lattice3(k2_yellow_1(sK2)) ),
    inference(subsumption_resolution,[],[f342,f82])).

fof(f342,plain,
    ( v2_struct_0(k2_yellow_1(sK2))
    | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(sK3,sK2)
    | ~ v2_lattice3(k2_yellow_1(sK2)) ),
    inference(subsumption_resolution,[],[f341,f83])).

fof(f341,plain,
    ( v2_struct_0(k2_yellow_1(sK2))
    | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(sK4,sK2)
    | ~ m1_subset_1(sK3,sK2)
    | ~ v2_lattice3(k2_yellow_1(sK2)) ),
    inference(resolution,[],[f299,f124])).

% (31945)Refutation not found, incomplete strategy% (31945)------------------------------
% (31945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31945)Termination reason: Refutation not found, incomplete strategy

% (31945)Memory used [KB]: 10746
% (31945)Time elapsed: 0.141 s
% (31945)------------------------------
% (31945)------------------------------
fof(f299,plain,
    ( ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2)
    | v2_struct_0(k2_yellow_1(sK2))
    | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) ),
    inference(forward_demodulation,[],[f298,f59])).

fof(f298,plain,
    ( v2_struct_0(k2_yellow_1(sK2))
    | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) ),
    inference(subsumption_resolution,[],[f297,f82])).

fof(f297,plain,
    ( ~ m1_subset_1(sK3,sK2)
    | v2_struct_0(k2_yellow_1(sK2))
    | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) ),
    inference(forward_demodulation,[],[f296,f59])).

fof(f296,plain,
    ( v2_struct_0(k2_yellow_1(sK2))
    | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) ),
    inference(subsumption_resolution,[],[f295,f56])).

fof(f295,plain,
    ( v2_struct_0(k2_yellow_1(sK2))
    | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ v3_orders_2(k2_yellow_1(sK2)) ),
    inference(subsumption_resolution,[],[f294,f58])).

fof(f294,plain,
    ( v2_struct_0(k2_yellow_1(sK2))
    | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ l1_orders_2(k2_yellow_1(sK2))
    | ~ v3_orders_2(k2_yellow_1(sK2)) ),
    inference(duplicate_literal_removal,[],[f289])).

fof(f289,plain,
    ( v2_struct_0(k2_yellow_1(sK2))
    | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))
    | ~ m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))
    | ~ l1_orders_2(k2_yellow_1(sK2))
    | ~ v3_orders_2(k2_yellow_1(sK2))
    | v2_struct_0(k2_yellow_1(sK2)) ),
    inference(resolution,[],[f275,f77])).

fof(f275,plain,
    ( r1_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)
    | v2_struct_0(k2_yellow_1(sK2)) ),
    inference(resolution,[],[f272,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | r1_orders_2(X1,X0,X3) ) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:23:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (31952)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.50  % (31952)Refutation not found, incomplete strategy% (31952)------------------------------
% 0.22/0.50  % (31952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (31952)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (31952)Memory used [KB]: 6140
% 0.22/0.50  % (31952)Time elapsed: 0.008 s
% 0.22/0.50  % (31952)------------------------------
% 0.22/0.50  % (31952)------------------------------
% 0.22/0.51  % (31944)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.51  % (31941)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (31960)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (31942)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (31943)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (31948)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (31947)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (31948)Refutation not found, incomplete strategy% (31948)------------------------------
% 0.22/0.52  % (31948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (31948)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (31948)Memory used [KB]: 10618
% 0.22/0.52  % (31948)Time elapsed: 0.108 s
% 0.22/0.52  % (31948)------------------------------
% 0.22/0.52  % (31948)------------------------------
% 0.22/0.52  % (31950)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (31946)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.53  % (31958)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (31965)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (31949)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (31938)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (31951)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (31953)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (31955)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (31956)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (31937)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (31937)Refutation not found, incomplete strategy% (31937)------------------------------
% 0.22/0.54  % (31937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (31937)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (31937)Memory used [KB]: 1663
% 0.22/0.54  % (31937)Time elapsed: 0.128 s
% 0.22/0.54  % (31937)------------------------------
% 0.22/0.54  % (31937)------------------------------
% 0.22/0.54  % (31939)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (31940)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (31944)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f381,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(subsumption_resolution,[],[f380,f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ~v1_xboole_0(sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f41])).
% 0.22/0.54  % (31964)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ((~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k3_xboole_0(sK3,sK4)) & m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))) & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))) & v2_lattice3(k2_yellow_1(sK2)) & ~v1_xboole_0(sK2)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f40,f39,f38])).
% 0.22/0.54  % (31962)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK2),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2)))) & v2_lattice3(k2_yellow_1(sK2)) & ~v1_xboole_0(sK2))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK2),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2)))) => (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,X2),k3_xboole_0(sK3,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2)))) & m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,X2),k3_xboole_0(sK3,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2)))) => (~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k3_xboole_0(sK3,sK4)) & m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0))),
% 0.22/0.54    inference(flattening,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ? [X0] : ((? [X1] : (? [X2] : (~r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v2_lattice3(k2_yellow_1(X0))) & ~v1_xboole_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f14])).
% 0.22/0.54  % (31939)Refutation not found, incomplete strategy% (31939)------------------------------
% 0.22/0.54  % (31939)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (31939)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (31939)Memory used [KB]: 10746
% 0.22/0.54  % (31939)Time elapsed: 0.128 s
% 0.22/0.54  % (31939)------------------------------
% 0.22/0.54  % (31939)------------------------------
% 0.22/0.54  fof(f14,negated_conjecture,(
% 0.22/0.54    ~! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 0.22/0.54    inference(negated_conjecture,[],[f13])).
% 0.22/0.54  fof(f13,conjecture,(
% 0.22/0.54    ! [X0] : (~v1_xboole_0(X0) => (v2_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k11_lattice3(k2_yellow_1(X0),X1,X2),k3_xboole_0(X1,X2))))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_1)).
% 0.22/0.54  fof(f380,plain,(
% 0.22/0.54    v1_xboole_0(sK2)),
% 0.22/0.54    inference(resolution,[],[f379,f61])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0] : (~v1_xboole_0(X0) => ~v2_struct_0(k2_yellow_1(X0)))),
% 0.22/0.54    inference(pure_predicate_removal,[],[f10])).
% 0.22/0.54  fof(f10,axiom,(
% 0.22/0.54    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).
% 0.22/0.54  fof(f379,plain,(
% 0.22/0.54    v2_struct_0(k2_yellow_1(sK2))),
% 0.22/0.54    inference(subsumption_resolution,[],[f376,f338])).
% 0.22/0.54  fof(f338,plain,(
% 0.22/0.54    r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | v2_struct_0(k2_yellow_1(sK2))),
% 0.22/0.54    inference(subsumption_resolution,[],[f337,f52])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    v2_lattice3(k2_yellow_1(sK2))),
% 0.22/0.54    inference(cnf_transformation,[],[f41])).
% 0.22/0.54  fof(f337,plain,(
% 0.22/0.54    r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | v2_struct_0(k2_yellow_1(sK2)) | ~v2_lattice3(k2_yellow_1(sK2))),
% 0.22/0.54    inference(subsumption_resolution,[],[f336,f82])).
% 0.22/0.54  fof(f82,plain,(
% 0.22/0.54    m1_subset_1(sK3,sK2)),
% 0.22/0.54    inference(backward_demodulation,[],[f53,f59])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f11])).
% 0.22/0.54  fof(f11,axiom,(
% 0.22/0.54    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.22/0.54  fof(f53,plain,(
% 0.22/0.54    m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2)))),
% 0.22/0.54    inference(cnf_transformation,[],[f41])).
% 0.22/0.54  fof(f336,plain,(
% 0.22/0.54    r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | v2_struct_0(k2_yellow_1(sK2)) | ~m1_subset_1(sK3,sK2) | ~v2_lattice3(k2_yellow_1(sK2))),
% 0.22/0.54    inference(subsumption_resolution,[],[f335,f83])).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    m1_subset_1(sK4,sK2)),
% 0.22/0.54    inference(backward_demodulation,[],[f54,f59])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2)))),
% 0.22/0.54    inference(cnf_transformation,[],[f41])).
% 0.22/0.54  fof(f335,plain,(
% 0.22/0.54    r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | v2_struct_0(k2_yellow_1(sK2)) | ~m1_subset_1(sK4,sK2) | ~m1_subset_1(sK3,sK2) | ~v2_lattice3(k2_yellow_1(sK2))),
% 0.22/0.54    inference(resolution,[],[f334,f124])).
% 0.22/0.54  fof(f124,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (m1_subset_1(k12_lattice3(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~v2_lattice3(k2_yellow_1(X0))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f123,f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 0.22/0.54    inference(pure_predicate_removal,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.22/0.54    inference(pure_predicate_removal,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.22/0.54  fof(f123,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (m1_subset_1(k12_lattice3(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~v2_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f122,f58])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 0.22/0.54    inference(pure_predicate_removal,[],[f8])).
% 0.22/0.54  fof(f8,axiom,(
% 0.22/0.54    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.22/0.54  fof(f122,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (m1_subset_1(k12_lattice3(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~l1_orders_2(k2_yellow_1(X0)) | ~v2_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.54    inference(superposition,[],[f78,f59])).
% 0.22/0.54  fof(f78,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.22/0.54    inference(flattening,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  % (31966)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k12_lattice3)).
% 0.22/0.54  fof(f334,plain,(
% 0.22/0.54    ~m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | v2_struct_0(k2_yellow_1(sK2))),
% 0.22/0.54    inference(subsumption_resolution,[],[f333,f51])).
% 0.22/0.54  fof(f333,plain,(
% 0.22/0.54    v2_struct_0(k2_yellow_1(sK2)) | r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | v1_xboole_0(sK2)),
% 0.22/0.54    inference(subsumption_resolution,[],[f330,f83])).
% 0.22/0.54  % (31962)Refutation not found, incomplete strategy% (31962)------------------------------
% 0.22/0.54  % (31962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (31961)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (31962)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (31962)Memory used [KB]: 6268
% 0.22/0.54  % (31962)Time elapsed: 0.131 s
% 0.22/0.54  % (31962)------------------------------
% 0.22/0.54  % (31962)------------------------------
% 0.22/0.54  fof(f330,plain,(
% 0.22/0.54    v2_struct_0(k2_yellow_1(sK2)) | ~m1_subset_1(sK4,sK2) | r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | v1_xboole_0(sK2)),
% 0.22/0.54    inference(resolution,[],[f329,f87])).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | r1_tarski(X1,X2) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f86,f59])).
% 0.22/0.54  fof(f86,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f62,f59])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,axiom,(
% 0.22/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).
% 0.22/0.54  fof(f329,plain,(
% 0.22/0.54    r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | v2_struct_0(k2_yellow_1(sK2))),
% 0.22/0.54    inference(subsumption_resolution,[],[f328,f52])).
% 0.22/0.54  fof(f328,plain,(
% 0.22/0.54    v2_struct_0(k2_yellow_1(sK2)) | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~v2_lattice3(k2_yellow_1(sK2))),
% 0.22/0.54    inference(subsumption_resolution,[],[f327,f82])).
% 0.22/0.54  % (31947)Refutation not found, incomplete strategy% (31947)------------------------------
% 0.22/0.54  % (31947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (31947)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (31947)Memory used [KB]: 10618
% 0.22/0.54  % (31947)Time elapsed: 0.126 s
% 0.22/0.54  % (31947)------------------------------
% 0.22/0.54  % (31947)------------------------------
% 0.22/0.54  fof(f327,plain,(
% 0.22/0.54    v2_struct_0(k2_yellow_1(sK2)) | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~m1_subset_1(sK3,sK2) | ~v2_lattice3(k2_yellow_1(sK2))),
% 0.22/0.54    inference(subsumption_resolution,[],[f326,f83])).
% 0.22/0.54  fof(f326,plain,(
% 0.22/0.54    v2_struct_0(k2_yellow_1(sK2)) | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~m1_subset_1(sK4,sK2) | ~m1_subset_1(sK3,sK2) | ~v2_lattice3(k2_yellow_1(sK2))),
% 0.22/0.54    inference(resolution,[],[f286,f124])).
% 0.22/0.54  fof(f286,plain,(
% 0.22/0.54    ~m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | v2_struct_0(k2_yellow_1(sK2)) | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4)),
% 0.22/0.54    inference(forward_demodulation,[],[f285,f59])).
% 0.22/0.54  fof(f285,plain,(
% 0.22/0.54    v2_struct_0(k2_yellow_1(sK2)) | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))),
% 0.22/0.54    inference(subsumption_resolution,[],[f284,f83])).
% 0.22/0.54  fof(f284,plain,(
% 0.22/0.54    ~m1_subset_1(sK4,sK2) | v2_struct_0(k2_yellow_1(sK2)) | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))),
% 0.22/0.54    inference(forward_demodulation,[],[f283,f59])).
% 0.22/0.54  fof(f283,plain,(
% 0.22/0.54    v2_struct_0(k2_yellow_1(sK2)) | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))),
% 0.22/0.54    inference(subsumption_resolution,[],[f282,f56])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f18])).
% 0.22/0.54  fof(f282,plain,(
% 0.22/0.54    v2_struct_0(k2_yellow_1(sK2)) | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~v3_orders_2(k2_yellow_1(sK2))),
% 0.22/0.54    inference(subsumption_resolution,[],[f281,f58])).
% 0.22/0.54  fof(f281,plain,(
% 0.22/0.54    v2_struct_0(k2_yellow_1(sK2)) | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~l1_orders_2(k2_yellow_1(sK2)) | ~v3_orders_2(k2_yellow_1(sK2))),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f276])).
% 0.22/0.54  fof(f276,plain,(
% 0.22/0.54    v2_struct_0(k2_yellow_1(sK2)) | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | ~m1_subset_1(sK4,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~l1_orders_2(k2_yellow_1(sK2)) | ~v3_orders_2(k2_yellow_1(sK2)) | v2_struct_0(k2_yellow_1(sK2))),
% 0.22/0.54    inference(resolution,[],[f274,f77])).
% 0.22/0.54  fof(f77,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.22/0.54  fof(f274,plain,(
% 0.22/0.54    r1_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | v2_struct_0(k2_yellow_1(sK2))),
% 0.22/0.54    inference(resolution,[],[f272,f67])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3) | r1_orders_2(X1,X0,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f49])).
% 0.22/0.54  fof(f49,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (~r1_orders_2(X1,sK5(X0,X1,X2,X3),X0) & r1_orders_2(X1,sK5(X0,X1,X2,X3),X2) & r1_orders_2(X1,sK5(X0,X1,X2,X3),X3) & m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X1))) | ~r1_orders_2(X1,X0,X2) | ~r1_orders_2(X1,X0,X3)) & ((! [X5] : (r1_orders_2(X1,X5,X0) | ~r1_orders_2(X1,X5,X2) | ~r1_orders_2(X1,X5,X3) | ~m1_subset_1(X5,u1_struct_0(X1))) & r1_orders_2(X1,X0,X2) & r1_orders_2(X1,X0,X3)) | ~sP0(X0,X1,X2,X3)))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f47,f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X1,X4,X0) & r1_orders_2(X1,X4,X2) & r1_orders_2(X1,X4,X3) & m1_subset_1(X4,u1_struct_0(X1))) => (~r1_orders_2(X1,sK5(X0,X1,X2,X3),X0) & r1_orders_2(X1,sK5(X0,X1,X2,X3),X2) & r1_orders_2(X1,sK5(X0,X1,X2,X3),X3) & m1_subset_1(sK5(X0,X1,X2,X3),u1_struct_0(X1))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (~r1_orders_2(X1,X4,X0) & r1_orders_2(X1,X4,X2) & r1_orders_2(X1,X4,X3) & m1_subset_1(X4,u1_struct_0(X1))) | ~r1_orders_2(X1,X0,X2) | ~r1_orders_2(X1,X0,X3)) & ((! [X5] : (r1_orders_2(X1,X5,X0) | ~r1_orders_2(X1,X5,X2) | ~r1_orders_2(X1,X5,X3) | ~m1_subset_1(X5,u1_struct_0(X1))) & r1_orders_2(X1,X0,X2) & r1_orders_2(X1,X0,X3)) | ~sP0(X0,X1,X2,X3)))),
% 0.22/0.54    inference(rectify,[],[f46])).
% 0.22/0.54  % (31963)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ! [X3,X0,X2,X1] : ((sP0(X3,X0,X2,X1) | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | ~sP0(X3,X0,X2,X1)))),
% 0.22/0.54    inference(flattening,[],[f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ! [X3,X0,X2,X1] : ((sP0(X3,X0,X2,X1) | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | ~sP0(X3,X0,X2,X1)))),
% 0.22/0.54    inference(nnf_transformation,[],[f35])).
% 0.22/0.54  % (31959)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    ! [X3,X0,X2,X1] : (sP0(X3,X0,X2,X1) <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))),
% 0.22/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.54  fof(f272,plain,(
% 0.22/0.54    sP0(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),k2_yellow_1(sK2),sK4,sK3) | v2_struct_0(k2_yellow_1(sK2))),
% 0.22/0.54    inference(subsumption_resolution,[],[f270,f83])).
% 0.22/0.54  fof(f270,plain,(
% 0.22/0.54    ~m1_subset_1(sK4,sK2) | v2_struct_0(k2_yellow_1(sK2)) | sP0(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),k2_yellow_1(sK2),sK4,sK3)),
% 0.22/0.54    inference(resolution,[],[f248,f194])).
% 0.22/0.54  fof(f194,plain,(
% 0.22/0.54    ~sP1(sK3,sK4,k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4)) | sP0(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),k2_yellow_1(sK2),sK4,sK3)),
% 0.22/0.54    inference(forward_demodulation,[],[f192,f188])).
% 0.22/0.54  fof(f188,plain,(
% 0.22/0.54    k12_lattice3(k2_yellow_1(sK2),sK4,sK3) = k12_lattice3(k2_yellow_1(sK2),sK3,sK4)),
% 0.22/0.54    inference(backward_demodulation,[],[f177,f185])).
% 0.22/0.54  fof(f185,plain,(
% 0.22/0.54    k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k12_lattice3(k2_yellow_1(sK2),sK3,sK4)),
% 0.22/0.54    inference(resolution,[],[f171,f82])).
% 0.22/0.54  fof(f171,plain,(
% 0.22/0.54    ( ! [X1] : (~m1_subset_1(X1,sK2) | k11_lattice3(k2_yellow_1(sK2),X1,sK4) = k12_lattice3(k2_yellow_1(sK2),X1,sK4)) )),
% 0.22/0.54    inference(resolution,[],[f169,f83])).
% 0.22/0.54  fof(f169,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,sK2) | ~m1_subset_1(X1,sK2) | k11_lattice3(k2_yellow_1(sK2),X1,X0) = k12_lattice3(k2_yellow_1(sK2),X1,X0)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f168,f59])).
% 0.22/0.54  % (31954)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.54  fof(f168,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,sK2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2))) | k11_lattice3(k2_yellow_1(sK2),X1,X0) = k12_lattice3(k2_yellow_1(sK2),X1,X0)) )),
% 0.22/0.54    inference(forward_demodulation,[],[f167,f59])).
% 0.22/0.54  fof(f167,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2))) | k11_lattice3(k2_yellow_1(sK2),X1,X0) = k12_lattice3(k2_yellow_1(sK2),X1,X0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f166,f57])).
% 0.22/0.54  fof(f166,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2))) | k11_lattice3(k2_yellow_1(sK2),X1,X0) = k12_lattice3(k2_yellow_1(sK2),X1,X0) | ~v5_orders_2(k2_yellow_1(sK2))) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f165,f58])).
% 0.22/0.54  fof(f165,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2))) | ~l1_orders_2(k2_yellow_1(sK2)) | k11_lattice3(k2_yellow_1(sK2),X1,X0) = k12_lattice3(k2_yellow_1(sK2),X1,X0) | ~v5_orders_2(k2_yellow_1(sK2))) )),
% 0.22/0.54    inference(resolution,[],[f79,f52])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~v2_lattice3(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~v5_orders_2(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f32])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.22/0.54    inference(flattening,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k12_lattice3(X0,X1,X2) = k11_lattice3(X0,X1,X2))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).
% 0.22/0.55  fof(f177,plain,(
% 0.22/0.55    k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k12_lattice3(k2_yellow_1(sK2),sK4,sK3)),
% 0.22/0.55    inference(backward_demodulation,[],[f157,f175])).
% 0.22/0.55  fof(f175,plain,(
% 0.22/0.55    k11_lattice3(k2_yellow_1(sK2),sK4,sK3) = k12_lattice3(k2_yellow_1(sK2),sK4,sK3)),
% 0.22/0.55    inference(resolution,[],[f170,f83])).
% 0.22/0.55  fof(f170,plain,(
% 0.22/0.55    ( ! [X0] : (~m1_subset_1(X0,sK2) | k11_lattice3(k2_yellow_1(sK2),X0,sK3) = k12_lattice3(k2_yellow_1(sK2),X0,sK3)) )),
% 0.22/0.55    inference(resolution,[],[f169,f82])).
% 0.22/0.55  fof(f157,plain,(
% 0.22/0.55    k11_lattice3(k2_yellow_1(sK2),sK3,sK4) = k11_lattice3(k2_yellow_1(sK2),sK4,sK3)),
% 0.22/0.55    inference(resolution,[],[f152,f83])).
% 0.22/0.55  % (31954)Refutation not found, incomplete strategy% (31954)------------------------------
% 0.22/0.55  % (31954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (31954)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (31954)Memory used [KB]: 10618
% 0.22/0.55  % (31954)Time elapsed: 0.139 s
% 0.22/0.55  % (31954)------------------------------
% 0.22/0.55  % (31954)------------------------------
% 0.22/0.55  fof(f152,plain,(
% 0.22/0.55    ( ! [X0] : (~m1_subset_1(X0,sK2) | k11_lattice3(k2_yellow_1(sK2),X0,sK3) = k11_lattice3(k2_yellow_1(sK2),sK3,X0)) )),
% 0.22/0.55    inference(resolution,[],[f151,f82])).
% 0.22/0.55  fof(f151,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,sK2) | ~m1_subset_1(X1,sK2) | k11_lattice3(k2_yellow_1(sK2),X1,X0) = k11_lattice3(k2_yellow_1(sK2),X0,X1)) )),
% 0.22/0.55    inference(forward_demodulation,[],[f150,f59])).
% 0.22/0.55  fof(f150,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,sK2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2))) | k11_lattice3(k2_yellow_1(sK2),X1,X0) = k11_lattice3(k2_yellow_1(sK2),X0,X1)) )),
% 0.22/0.55    inference(forward_demodulation,[],[f149,f59])).
% 0.22/0.55  fof(f149,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2))) | k11_lattice3(k2_yellow_1(sK2),X1,X0) = k11_lattice3(k2_yellow_1(sK2),X0,X1)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f148,f57])).
% 0.22/0.55  fof(f148,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2))) | k11_lattice3(k2_yellow_1(sK2),X1,X0) = k11_lattice3(k2_yellow_1(sK2),X0,X1) | ~v5_orders_2(k2_yellow_1(sK2))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f147,f58])).
% 0.22/0.55  fof(f147,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2))) | ~l1_orders_2(k2_yellow_1(sK2)) | k11_lattice3(k2_yellow_1(sK2),X1,X0) = k11_lattice3(k2_yellow_1(sK2),X0,X1) | ~v5_orders_2(k2_yellow_1(sK2))) )),
% 0.22/0.55    inference(resolution,[],[f74,f52])).
% 0.22/0.55  fof(f74,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v2_lattice3(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~v5_orders_2(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (! [X2] : (k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.22/0.55    inference(flattening,[],[f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (! [X2] : (k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_lattice3)).
% 0.22/0.55  fof(f192,plain,(
% 0.22/0.55    ~sP1(sK3,sK4,k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4)) | sP0(k12_lattice3(k2_yellow_1(sK2),sK4,sK3),k2_yellow_1(sK2),sK4,sK3)),
% 0.22/0.55    inference(backward_demodulation,[],[f184,f188])).
% 0.22/0.55  fof(f184,plain,(
% 0.22/0.55    ~sP1(sK3,sK4,k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK4,sK3)) | sP0(k12_lattice3(k2_yellow_1(sK2),sK4,sK3),k2_yellow_1(sK2),sK4,sK3)),
% 0.22/0.55    inference(superposition,[],[f81,f177])).
% 0.22/0.55  fof(f81,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2,k11_lattice3(X2,X0,X1)) | sP0(k11_lattice3(X2,X0,X1),X2,X1,X0)) )),
% 0.22/0.55    inference(equality_resolution,[],[f64])).
% 0.22/0.55  fof(f64,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (sP0(X3,X2,X1,X0) | k11_lattice3(X2,X0,X1) != X3 | ~sP1(X0,X1,X2,X3)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f44])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (((k11_lattice3(X2,X0,X1) = X3 | ~sP0(X3,X2,X1,X0)) & (sP0(X3,X2,X1,X0) | k11_lattice3(X2,X0,X1) != X3)) | ~sP1(X0,X1,X2,X3))),
% 0.22/0.55    inference(rectify,[],[f43])).
% 0.22/0.55  fof(f43,plain,(
% 0.22/0.55    ! [X1,X2,X0,X3] : (((k11_lattice3(X0,X1,X2) = X3 | ~sP0(X3,X0,X2,X1)) & (sP0(X3,X0,X2,X1) | k11_lattice3(X0,X1,X2) != X3)) | ~sP1(X1,X2,X0,X3))),
% 0.22/0.55    inference(nnf_transformation,[],[f36])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ! [X1,X2,X0,X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> sP0(X3,X0,X2,X1)) | ~sP1(X1,X2,X0,X3))),
% 0.22/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.55  fof(f248,plain,(
% 0.22/0.55    ( ! [X1] : (sP1(sK3,sK4,k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,X1)) | ~m1_subset_1(X1,sK2) | v2_struct_0(k2_yellow_1(sK2))) )),
% 0.22/0.55    inference(resolution,[],[f243,f83])).
% 0.22/0.55  fof(f243,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,sK2) | v2_struct_0(k2_yellow_1(sK2)) | ~m1_subset_1(X1,sK2) | sP1(sK3,X0,k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,X1))) )),
% 0.22/0.55    inference(resolution,[],[f230,f82])).
% 0.22/0.55  fof(f230,plain,(
% 0.22/0.55    ( ! [X4,X2,X3] : (~m1_subset_1(X3,sK2) | sP1(sK3,X2,k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),X3,X4)) | v2_struct_0(k2_yellow_1(sK2)) | ~m1_subset_1(X4,sK2) | ~m1_subset_1(X2,sK2)) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f229,f52])).
% 0.22/0.55  fof(f229,plain,(
% 0.22/0.55    ( ! [X4,X2,X3] : (~m1_subset_1(X2,sK2) | sP1(sK3,X2,k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),X3,X4)) | v2_struct_0(k2_yellow_1(sK2)) | ~m1_subset_1(X4,sK2) | ~m1_subset_1(X3,sK2) | ~v2_lattice3(k2_yellow_1(sK2))) )),
% 0.22/0.55    inference(resolution,[],[f223,f124])).
% 0.22/0.55  fof(f223,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,sK2) | ~m1_subset_1(X0,sK2) | sP1(sK3,X0,k2_yellow_1(sK2),X1) | v2_struct_0(k2_yellow_1(sK2))) )),
% 0.22/0.55    inference(resolution,[],[f222,f82])).
% 0.22/0.55  fof(f222,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,sK2) | ~m1_subset_1(X1,sK2) | ~m1_subset_1(X0,sK2) | sP1(X2,X1,k2_yellow_1(sK2),X0) | v2_struct_0(k2_yellow_1(sK2))) )),
% 0.22/0.55    inference(forward_demodulation,[],[f221,f59])).
% 0.22/0.55  % (31959)Refutation not found, incomplete strategy% (31959)------------------------------
% 0.22/0.55  % (31959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (31959)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (31959)Memory used [KB]: 10746
% 0.22/0.55  % (31959)Time elapsed: 0.140 s
% 0.22/0.55  % (31959)------------------------------
% 0.22/0.55  % (31959)------------------------------
% 0.22/0.55  fof(f221,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,sK2) | ~m1_subset_1(X0,sK2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2))) | sP1(X2,X1,k2_yellow_1(sK2),X0) | v2_struct_0(k2_yellow_1(sK2))) )),
% 0.22/0.55    inference(forward_demodulation,[],[f220,f59])).
% 0.22/0.55  fof(f220,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,sK2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2))) | sP1(X2,X1,k2_yellow_1(sK2),X0) | v2_struct_0(k2_yellow_1(sK2))) )),
% 0.22/0.55    inference(forward_demodulation,[],[f219,f59])).
% 0.22/0.55  % (31957)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (31963)Refutation not found, incomplete strategy% (31963)------------------------------
% 0.22/0.55  % (31963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (31963)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (31963)Memory used [KB]: 10746
% 0.22/0.55  % (31963)Time elapsed: 0.142 s
% 0.22/0.55  % (31963)------------------------------
% 0.22/0.55  % (31963)------------------------------
% 0.22/0.55  fof(f219,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2))) | sP1(X2,X1,k2_yellow_1(sK2),X0) | v2_struct_0(k2_yellow_1(sK2))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f218,f57])).
% 0.22/0.55  % (31946)Refutation not found, incomplete strategy% (31946)------------------------------
% 0.22/0.55  % (31946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (31946)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (31946)Memory used [KB]: 10618
% 0.22/0.55  % (31946)Time elapsed: 0.142 s
% 0.22/0.55  % (31946)------------------------------
% 0.22/0.55  % (31946)------------------------------
% 0.22/0.55  fof(f218,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2))) | sP1(X2,X1,k2_yellow_1(sK2),X0) | ~v5_orders_2(k2_yellow_1(sK2)) | v2_struct_0(k2_yellow_1(sK2))) )),
% 0.22/0.55    inference(subsumption_resolution,[],[f217,f58])).
% 0.22/0.55  fof(f217,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK2))) | ~l1_orders_2(k2_yellow_1(sK2)) | sP1(X2,X1,k2_yellow_1(sK2),X0) | ~v5_orders_2(k2_yellow_1(sK2)) | v2_struct_0(k2_yellow_1(sK2))) )),
% 0.22/0.55    inference(resolution,[],[f73,f52])).
% 0.22/0.55  fof(f73,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~v2_lattice3(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | sP1(X1,X2,X0,X3) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f37])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (sP1(X1,X2,X0,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.55    inference(definition_folding,[],[f24,f36,f35])).
% 0.22/0.55  % (31945)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.55    inference(flattening,[],[f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.55    inference(ennf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l28_lattice3)).
% 0.22/0.55  fof(f376,plain,(
% 0.22/0.55    ~r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK4) | v2_struct_0(k2_yellow_1(sK2))),
% 0.22/0.55    inference(resolution,[],[f355,f190])).
% 0.22/0.55  fof(f190,plain,(
% 0.22/0.55    ~r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),k3_xboole_0(sK3,sK4))),
% 0.22/0.55    inference(backward_demodulation,[],[f179,f188])).
% 0.22/0.55  fof(f179,plain,(
% 0.22/0.55    ~r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK4,sK3),k3_xboole_0(sK3,sK4))),
% 0.22/0.55    inference(backward_demodulation,[],[f55,f177])).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    ~r1_tarski(k11_lattice3(k2_yellow_1(sK2),sK3,sK4),k3_xboole_0(sK3,sK4))),
% 0.22/0.55    inference(cnf_transformation,[],[f41])).
% 0.22/0.55  fof(f355,plain,(
% 0.22/0.55    ( ! [X1] : (r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),k3_xboole_0(sK3,X1)) | ~r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),X1) | v2_struct_0(k2_yellow_1(sK2))) )),
% 0.22/0.55    inference(resolution,[],[f353,f80])).
% 0.22/0.55  fof(f80,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f34])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.55    inference(flattening,[],[f33])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.22/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.22/0.55  fof(f353,plain,(
% 0.22/0.55    r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | v2_struct_0(k2_yellow_1(sK2))),
% 0.22/0.55    inference(subsumption_resolution,[],[f352,f52])).
% 0.22/0.55  fof(f352,plain,(
% 0.22/0.55    r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | v2_struct_0(k2_yellow_1(sK2)) | ~v2_lattice3(k2_yellow_1(sK2))),
% 0.22/0.55    inference(subsumption_resolution,[],[f351,f82])).
% 0.22/0.55  fof(f351,plain,(
% 0.22/0.55    r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | v2_struct_0(k2_yellow_1(sK2)) | ~m1_subset_1(sK3,sK2) | ~v2_lattice3(k2_yellow_1(sK2))),
% 0.22/0.55    inference(subsumption_resolution,[],[f350,f83])).
% 0.22/0.55  fof(f350,plain,(
% 0.22/0.55    r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | v2_struct_0(k2_yellow_1(sK2)) | ~m1_subset_1(sK4,sK2) | ~m1_subset_1(sK3,sK2) | ~v2_lattice3(k2_yellow_1(sK2))),
% 0.22/0.55    inference(resolution,[],[f349,f124])).
% 0.22/0.55  fof(f349,plain,(
% 0.22/0.55    ~m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | v2_struct_0(k2_yellow_1(sK2))),
% 0.22/0.55    inference(subsumption_resolution,[],[f348,f51])).
% 0.22/0.55  fof(f348,plain,(
% 0.22/0.55    v2_struct_0(k2_yellow_1(sK2)) | r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | v1_xboole_0(sK2)),
% 0.22/0.55    inference(subsumption_resolution,[],[f345,f82])).
% 0.22/0.55  fof(f345,plain,(
% 0.22/0.55    v2_struct_0(k2_yellow_1(sK2)) | ~m1_subset_1(sK3,sK2) | r1_tarski(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | v1_xboole_0(sK2)),
% 0.22/0.55    inference(resolution,[],[f344,f87])).
% 0.22/0.55  fof(f344,plain,(
% 0.22/0.55    r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | v2_struct_0(k2_yellow_1(sK2))),
% 0.22/0.55    inference(subsumption_resolution,[],[f343,f52])).
% 0.22/0.55  fof(f343,plain,(
% 0.22/0.55    v2_struct_0(k2_yellow_1(sK2)) | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~v2_lattice3(k2_yellow_1(sK2))),
% 0.22/0.55    inference(subsumption_resolution,[],[f342,f82])).
% 0.22/0.55  fof(f342,plain,(
% 0.22/0.55    v2_struct_0(k2_yellow_1(sK2)) | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(sK3,sK2) | ~v2_lattice3(k2_yellow_1(sK2))),
% 0.22/0.55    inference(subsumption_resolution,[],[f341,f83])).
% 0.22/0.55  fof(f341,plain,(
% 0.22/0.55    v2_struct_0(k2_yellow_1(sK2)) | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(sK4,sK2) | ~m1_subset_1(sK3,sK2) | ~v2_lattice3(k2_yellow_1(sK2))),
% 0.22/0.55    inference(resolution,[],[f299,f124])).
% 0.22/0.55  % (31945)Refutation not found, incomplete strategy% (31945)------------------------------
% 0.22/0.55  % (31945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (31945)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (31945)Memory used [KB]: 10746
% 0.22/0.55  % (31945)Time elapsed: 0.141 s
% 0.22/0.55  % (31945)------------------------------
% 0.22/0.55  % (31945)------------------------------
% 0.22/0.55  fof(f299,plain,(
% 0.22/0.55    ~m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK2) | v2_struct_0(k2_yellow_1(sK2)) | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3)),
% 0.22/0.55    inference(forward_demodulation,[],[f298,f59])).
% 0.22/0.55  fof(f298,plain,(
% 0.22/0.55    v2_struct_0(k2_yellow_1(sK2)) | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))),
% 0.22/0.55    inference(subsumption_resolution,[],[f297,f82])).
% 0.22/0.55  fof(f297,plain,(
% 0.22/0.55    ~m1_subset_1(sK3,sK2) | v2_struct_0(k2_yellow_1(sK2)) | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))),
% 0.22/0.55    inference(forward_demodulation,[],[f296,f59])).
% 0.22/0.55  fof(f296,plain,(
% 0.22/0.55    v2_struct_0(k2_yellow_1(sK2)) | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2)))),
% 0.22/0.55    inference(subsumption_resolution,[],[f295,f56])).
% 0.22/0.55  fof(f295,plain,(
% 0.22/0.55    v2_struct_0(k2_yellow_1(sK2)) | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~v3_orders_2(k2_yellow_1(sK2))),
% 0.22/0.55    inference(subsumption_resolution,[],[f294,f58])).
% 0.22/0.55  fof(f294,plain,(
% 0.22/0.55    v2_struct_0(k2_yellow_1(sK2)) | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~l1_orders_2(k2_yellow_1(sK2)) | ~v3_orders_2(k2_yellow_1(sK2))),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f289])).
% 0.22/0.55  fof(f289,plain,(
% 0.22/0.55    v2_struct_0(k2_yellow_1(sK2)) | r3_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | ~m1_subset_1(sK3,u1_struct_0(k2_yellow_1(sK2))) | ~m1_subset_1(k12_lattice3(k2_yellow_1(sK2),sK3,sK4),u1_struct_0(k2_yellow_1(sK2))) | ~l1_orders_2(k2_yellow_1(sK2)) | ~v3_orders_2(k2_yellow_1(sK2)) | v2_struct_0(k2_yellow_1(sK2))),
% 0.22/0.55    inference(resolution,[],[f275,f77])).
% 0.22/0.55  fof(f275,plain,(
% 0.22/0.55    r1_orders_2(k2_yellow_1(sK2),k12_lattice3(k2_yellow_1(sK2),sK3,sK4),sK3) | v2_struct_0(k2_yellow_1(sK2))),
% 0.22/0.55    inference(resolution,[],[f272,f66])).
% 0.22/0.55  fof(f66,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3) | r1_orders_2(X1,X0,X3)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f49])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (31944)------------------------------
% 0.22/0.55  % (31944)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (31944)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (31944)Memory used [KB]: 6652
% 0.22/0.55  % (31944)Time elapsed: 0.073 s
% 0.22/0.55  % (31944)------------------------------
% 0.22/0.55  % (31944)------------------------------
% 0.22/0.55  % (31936)Success in time 0.181 s
%------------------------------------------------------------------------------
