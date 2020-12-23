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
% DateTime   : Thu Dec  3 13:16:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  160 (1349 expanded)
%              Number of leaves         :   16 ( 478 expanded)
%              Depth                    :   49
%              Number of atoms          :  685 (5494 expanded)
%              Number of equality atoms :   48 ( 480 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1543,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1531,f998])).

fof(f998,plain,(
    r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(subsumption_resolution,[],[f997,f79])).

fof(f79,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f46,f55])).

fof(f55,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f46,plain,(
    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    & v1_lattice3(k2_yellow_1(sK0))
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f35,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))
                & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
            & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
        & v1_lattice3(k2_yellow_1(X0))
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(sK0),X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) )
      & v1_lattice3(k2_yellow_1(sK0))
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(sK0),X1,X2))
            & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
        & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k2_xboole_0(sK1,X2),k10_lattice3(k2_yellow_1(sK0),sK1,X2))
          & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k2_xboole_0(sK1,X2),k10_lattice3(k2_yellow_1(sK0),sK1,X2))
        & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
   => ( ~ r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
      & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v1_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v1_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( v1_lattice3(k2_yellow_1(X0))
         => ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
                 => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_lattice3(k2_yellow_1(X0))
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_1)).

fof(f997,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(forward_demodulation,[],[f996,f55])).

fof(f996,plain,
    ( r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f995,f367])).

fof(f367,plain,(
    m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) ),
    inference(resolution,[],[f275,f78])).

fof(f78,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(forward_demodulation,[],[f47,f55])).

fof(f47,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f275,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,sK0)
      | m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,X1),sK0) ) ),
    inference(resolution,[],[f132,f79])).

fof(f132,plain,(
    ! [X14,X15] :
      ( ~ m1_subset_1(X14,sK0)
      | ~ m1_subset_1(X15,sK0)
      | m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X14,X15),sK0) ) ),
    inference(forward_demodulation,[],[f131,f55])).

fof(f131,plain,(
    ! [X14,X15] :
      ( ~ m1_subset_1(X15,sK0)
      | m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X14,X15),sK0)
      | ~ m1_subset_1(X14,u1_struct_0(k2_yellow_1(sK0))) ) ),
    inference(forward_demodulation,[],[f130,f55])).

fof(f130,plain,(
    ! [X14,X15] :
      ( m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X14,X15),sK0)
      | ~ m1_subset_1(X15,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X14,u1_struct_0(k2_yellow_1(sK0))) ) ),
    inference(forward_demodulation,[],[f129,f55])).

fof(f129,plain,(
    ! [X14,X15] :
      ( m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X14,X15),u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X15,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X14,u1_struct_0(k2_yellow_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f128,f52])).

fof(f52,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v4_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

fof(f128,plain,(
    ! [X14,X15] :
      ( m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X14,X15),u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X15,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X14,u1_struct_0(k2_yellow_1(sK0)))
      | ~ v5_orders_2(k2_yellow_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f94,f54])).

fof(f54,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f94,plain,(
    ! [X14,X15] :
      ( m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X14,X15),u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X15,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X14,u1_struct_0(k2_yellow_1(sK0)))
      | ~ l1_orders_2(k2_yellow_1(sK0))
      | ~ v5_orders_2(k2_yellow_1(sK0)) ) ),
    inference(resolution,[],[f45,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k13_lattice3)).

fof(f45,plain,(
    v1_lattice3(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f995,plain,
    ( ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(forward_demodulation,[],[f994,f55])).

fof(f994,plain,
    ( r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f992,f44])).

fof(f44,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f992,plain,
    ( r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f829,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f829,plain,(
    r3_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(subsumption_resolution,[],[f828,f79])).

fof(f828,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | r3_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(forward_demodulation,[],[f827,f55])).

fof(f827,plain,
    ( r3_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f826,f367])).

fof(f826,plain,
    ( ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | r3_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(forward_demodulation,[],[f825,f55])).

fof(f825,plain,
    ( r3_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f824,f82])).

fof(f82,plain,(
    ~ v2_struct_0(k2_yellow_1(sK0)) ),
    inference(resolution,[],[f44,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).

fof(f824,plain,
    ( r3_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f823,f50])).

fof(f50,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f823,plain,
    ( r3_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ v3_orders_2(k2_yellow_1(sK0))
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f746,f54])).

fof(f746,plain,
    ( r3_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v3_orders_2(k2_yellow_1(sK0))
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(resolution,[],[f711,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f711,plain,(
    r1_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(backward_demodulation,[],[f647,f681])).

fof(f681,plain,(
    k13_lattice3(k2_yellow_1(sK0),sK1,sK2) = k13_lattice3(k2_yellow_1(sK0),sK2,sK1) ),
    inference(backward_demodulation,[],[f504,f675])).

fof(f675,plain,(
    k10_lattice3(k2_yellow_1(sK0),sK1,sK2) = k13_lattice3(k2_yellow_1(sK0),sK1,sK2) ),
    inference(resolution,[],[f344,f78])).

fof(f344,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,sK0)
      | k13_lattice3(k2_yellow_1(sK0),sK1,X1) = k10_lattice3(k2_yellow_1(sK0),sK1,X1) ) ),
    inference(resolution,[],[f136,f79])).

fof(f136,plain,(
    ! [X17,X16] :
      ( ~ m1_subset_1(X16,sK0)
      | ~ m1_subset_1(X17,sK0)
      | k13_lattice3(k2_yellow_1(sK0),X16,X17) = k10_lattice3(k2_yellow_1(sK0),X16,X17) ) ),
    inference(forward_demodulation,[],[f135,f55])).

fof(f135,plain,(
    ! [X17,X16] :
      ( ~ m1_subset_1(X17,sK0)
      | k13_lattice3(k2_yellow_1(sK0),X16,X17) = k10_lattice3(k2_yellow_1(sK0),X16,X17)
      | ~ m1_subset_1(X16,u1_struct_0(k2_yellow_1(sK0))) ) ),
    inference(forward_demodulation,[],[f134,f55])).

fof(f134,plain,(
    ! [X17,X16] :
      ( k13_lattice3(k2_yellow_1(sK0),X16,X17) = k10_lattice3(k2_yellow_1(sK0),X16,X17)
      | ~ m1_subset_1(X17,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X16,u1_struct_0(k2_yellow_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f133,f52])).

fof(f133,plain,(
    ! [X17,X16] :
      ( k13_lattice3(k2_yellow_1(sK0),X16,X17) = k10_lattice3(k2_yellow_1(sK0),X16,X17)
      | ~ m1_subset_1(X17,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X16,u1_struct_0(k2_yellow_1(sK0)))
      | ~ v5_orders_2(k2_yellow_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f95,f54])).

fof(f95,plain,(
    ! [X17,X16] :
      ( k13_lattice3(k2_yellow_1(sK0),X16,X17) = k10_lattice3(k2_yellow_1(sK0),X16,X17)
      | ~ m1_subset_1(X17,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X16,u1_struct_0(k2_yellow_1(sK0)))
      | ~ l1_orders_2(k2_yellow_1(sK0))
      | ~ v5_orders_2(k2_yellow_1(sK0)) ) ),
    inference(resolution,[],[f45,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(f504,plain,(
    k10_lattice3(k2_yellow_1(sK0),sK1,sK2) = k13_lattice3(k2_yellow_1(sK0),sK2,sK1) ),
    inference(subsumption_resolution,[],[f503,f78])).

fof(f503,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | k10_lattice3(k2_yellow_1(sK0),sK1,sK2) = k13_lattice3(k2_yellow_1(sK0),sK2,sK1) ),
    inference(forward_demodulation,[],[f502,f55])).

fof(f502,plain,
    ( k10_lattice3(k2_yellow_1(sK0),sK1,sK2) = k13_lattice3(k2_yellow_1(sK0),sK2,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f501,f79])).

fof(f501,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | k10_lattice3(k2_yellow_1(sK0),sK1,sK2) = k13_lattice3(k2_yellow_1(sK0),sK2,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(forward_demodulation,[],[f500,f55])).

fof(f500,plain,
    ( k10_lattice3(k2_yellow_1(sK0),sK1,sK2) = k13_lattice3(k2_yellow_1(sK0),sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f499,f52])).

fof(f499,plain,
    ( k10_lattice3(k2_yellow_1(sK0),sK1,sK2) = k13_lattice3(k2_yellow_1(sK0),sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ v5_orders_2(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f498,f45])).

fof(f498,plain,
    ( k10_lattice3(k2_yellow_1(sK0),sK1,sK2) = k13_lattice3(k2_yellow_1(sK0),sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ v1_lattice3(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f449,f54])).

fof(f449,plain,
    ( k10_lattice3(k2_yellow_1(sK0),sK1,sK2) = k13_lattice3(k2_yellow_1(sK0),sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v1_lattice3(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0)) ),
    inference(superposition,[],[f440,f73])).

fof(f440,plain,(
    k10_lattice3(k2_yellow_1(sK0),sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK2,sK1) ),
    inference(resolution,[],[f338,f79])).

fof(f338,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | k10_lattice3(k2_yellow_1(sK0),sK2,X0) = k10_lattice3(k2_yellow_1(sK0),X0,sK2) ) ),
    inference(resolution,[],[f127,f78])).

fof(f127,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X12,sK0)
      | ~ m1_subset_1(X13,sK0)
      | k10_lattice3(k2_yellow_1(sK0),X12,X13) = k10_lattice3(k2_yellow_1(sK0),X13,X12) ) ),
    inference(forward_demodulation,[],[f126,f55])).

fof(f126,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X13,sK0)
      | k10_lattice3(k2_yellow_1(sK0),X12,X13) = k10_lattice3(k2_yellow_1(sK0),X13,X12)
      | ~ m1_subset_1(X12,u1_struct_0(k2_yellow_1(sK0))) ) ),
    inference(forward_demodulation,[],[f125,f55])).

fof(f125,plain,(
    ! [X12,X13] :
      ( k10_lattice3(k2_yellow_1(sK0),X12,X13) = k10_lattice3(k2_yellow_1(sK0),X13,X12)
      | ~ m1_subset_1(X13,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X12,u1_struct_0(k2_yellow_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f124,f52])).

fof(f124,plain,(
    ! [X12,X13] :
      ( k10_lattice3(k2_yellow_1(sK0),X12,X13) = k10_lattice3(k2_yellow_1(sK0),X13,X12)
      | ~ m1_subset_1(X13,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X12,u1_struct_0(k2_yellow_1(sK0)))
      | ~ v5_orders_2(k2_yellow_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f93,f54])).

fof(f93,plain,(
    ! [X12,X13] :
      ( k10_lattice3(k2_yellow_1(sK0),X12,X13) = k10_lattice3(k2_yellow_1(sK0),X13,X12)
      | ~ m1_subset_1(X13,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X12,u1_struct_0(k2_yellow_1(sK0)))
      | ~ l1_orders_2(k2_yellow_1(sK0))
      | ~ v5_orders_2(k2_yellow_1(sK0)) ) ),
    inference(resolution,[],[f45,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_lattice3)).

fof(f647,plain,(
    r1_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK2,sK1)) ),
    inference(subsumption_resolution,[],[f646,f78])).

fof(f646,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | r1_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK2,sK1)) ),
    inference(forward_demodulation,[],[f645,f55])).

fof(f645,plain,
    ( r1_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK2,sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f644,f79])).

fof(f644,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | r1_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK2,sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(forward_demodulation,[],[f643,f55])).

fof(f643,plain,
    ( r1_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK2,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f642,f284])).

fof(f284,plain,(
    m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK2,sK1),sK0) ),
    inference(resolution,[],[f274,f79])).

fof(f274,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK0)
      | m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK2,X0),sK0) ) ),
    inference(resolution,[],[f132,f78])).

fof(f642,plain,
    ( ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK2,sK1),sK0)
    | r1_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK2,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(forward_demodulation,[],[f641,f55])).

fof(f641,plain,
    ( ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK2,sK1),u1_struct_0(k2_yellow_1(sK0)))
    | r1_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK2,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f640,f82])).

fof(f640,plain,
    ( ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK2,sK1),u1_struct_0(k2_yellow_1(sK0)))
    | r1_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK2,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f639,f52])).

fof(f639,plain,
    ( ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK2,sK1),u1_struct_0(k2_yellow_1(sK0)))
    | r1_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK2,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f638,f45])).

fof(f638,plain,
    ( ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK2,sK1),u1_struct_0(k2_yellow_1(sK0)))
    | r1_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK2,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ v1_lattice3(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f574,f54])).

fof(f574,plain,
    ( ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK2,sK1),u1_struct_0(k2_yellow_1(sK0)))
    | r1_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK2,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v1_lattice3(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(superposition,[],[f76,f511])).

fof(f511,plain,(
    k10_lattice3(k2_yellow_1(sK0),sK2,sK1) = k13_lattice3(k2_yellow_1(sK0),sK2,sK1) ),
    inference(backward_demodulation,[],[f440,f504])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
                        & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3))
                        & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3))
                        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).

fof(f41,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK3(X0,X1,X2,X3))
        & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3))
        & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3))
        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f39])).

% (26505)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k10_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k10_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k10_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k10_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k10_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X2,X4)
                              & r1_orders_2(X0,X1,X4) )
                           => r1_orders_2(X0,X3,X4) ) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l26_lattice3)).

fof(f1531,plain,(
    ~ r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(resolution,[],[f1494,f270])).

fof(f270,plain,
    ( ~ r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(resolution,[],[f208,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f208,plain,(
    ~ r1_tarski(k2_xboole_0(sK1,sK2),k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(subsumption_resolution,[],[f207,f79])).

fof(f207,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | ~ r1_tarski(k2_xboole_0(sK1,sK2),k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(forward_demodulation,[],[f206,f55])).

fof(f206,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,sK2),k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f205,f78])).

fof(f205,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ r1_tarski(k2_xboole_0(sK1,sK2),k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(forward_demodulation,[],[f204,f55])).

fof(f204,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,sK2),k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f203,f52])).

fof(f203,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,sK2),k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ v5_orders_2(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f202,f45])).

fof(f202,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,sK2),k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ v1_lattice3(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f162,f54])).

fof(f162,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,sK2),k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v1_lattice3(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0)) ),
    inference(superposition,[],[f48,f73])).

fof(f48,plain,(
    ~ r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(cnf_transformation,[],[f36])).

fof(f1494,plain,(
    r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(subsumption_resolution,[],[f1493,f78])).

fof(f1493,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(forward_demodulation,[],[f1492,f55])).

fof(f1492,plain,
    ( r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f1491,f367])).

fof(f1491,plain,
    ( ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(forward_demodulation,[],[f1490,f55])).

fof(f1490,plain,
    ( r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f1488,f44])).

fof(f1488,plain,
    ( r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f960,f59])).

fof(f960,plain,(
    r3_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(subsumption_resolution,[],[f959,f78])).

fof(f959,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | r3_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(forward_demodulation,[],[f958,f55])).

fof(f958,plain,
    ( r3_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f957,f367])).

fof(f957,plain,
    ( ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)
    | r3_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(forward_demodulation,[],[f956,f55])).

fof(f956,plain,
    ( r3_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f955,f82])).

fof(f955,plain,
    ( r3_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f954,f50])).

fof(f954,plain,
    ( r3_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ v3_orders_2(k2_yellow_1(sK0))
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f877,f54])).

fof(f877,plain,
    ( r3_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v3_orders_2(k2_yellow_1(sK0))
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(resolution,[],[f712,f71])).

fof(f712,plain,(
    r1_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(backward_demodulation,[],[f657,f681])).

fof(f657,plain,(
    r1_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK2,sK1)) ),
    inference(subsumption_resolution,[],[f656,f78])).

fof(f656,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | r1_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK2,sK1)) ),
    inference(forward_demodulation,[],[f655,f55])).

fof(f655,plain,
    ( r1_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK2,sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f654,f79])).

fof(f654,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | r1_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK2,sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(forward_demodulation,[],[f653,f55])).

fof(f653,plain,
    ( r1_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK2,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f652,f284])).

fof(f652,plain,
    ( ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK2,sK1),sK0)
    | r1_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK2,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(forward_demodulation,[],[f651,f55])).

fof(f651,plain,
    ( ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK2,sK1),u1_struct_0(k2_yellow_1(sK0)))
    | r1_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK2,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f650,f82])).

fof(f650,plain,
    ( ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK2,sK1),u1_struct_0(k2_yellow_1(sK0)))
    | r1_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK2,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f649,f52])).

fof(f649,plain,
    ( ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK2,sK1),u1_struct_0(k2_yellow_1(sK0)))
    | r1_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK2,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f648,f45])).

fof(f648,plain,
    ( ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK2,sK1),u1_struct_0(k2_yellow_1(sK0)))
    | r1_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK2,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ v1_lattice3(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f576,f54])).

fof(f576,plain,
    ( ~ m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK2,sK1),u1_struct_0(k2_yellow_1(sK0)))
    | r1_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK2,sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v1_lattice3(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0))
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(superposition,[],[f77,f511])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | k10_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:26:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (26503)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.47  % (26491)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.47  % (26503)Refutation not found, incomplete strategy% (26503)------------------------------
% 0.22/0.47  % (26503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (26503)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (26503)Memory used [KB]: 6140
% 0.22/0.47  % (26503)Time elapsed: 0.002 s
% 0.22/0.47  % (26503)------------------------------
% 0.22/0.47  % (26503)------------------------------
% 0.22/0.47  % (26495)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.48  % (26496)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (26498)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  % (26504)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (26504)Refutation not found, incomplete strategy% (26504)------------------------------
% 0.22/0.49  % (26504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (26504)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (26504)Memory used [KB]: 1663
% 0.22/0.49  % (26504)Time elapsed: 0.063 s
% 0.22/0.49  % (26504)------------------------------
% 0.22/0.49  % (26504)------------------------------
% 0.22/0.50  % (26494)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (26492)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (26500)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (26492)Refutation not found, incomplete strategy% (26492)------------------------------
% 0.22/0.50  % (26492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (26492)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (26492)Memory used [KB]: 10618
% 0.22/0.50  % (26492)Time elapsed: 0.083 s
% 0.22/0.50  % (26492)------------------------------
% 0.22/0.50  % (26492)------------------------------
% 0.22/0.50  % (26495)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f1543,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(subsumption_resolution,[],[f1531,f998])).
% 0.22/0.50  fof(f998,plain,(
% 0.22/0.50    r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.22/0.50    inference(subsumption_resolution,[],[f997,f79])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    m1_subset_1(sK1,sK0)),
% 0.22/0.50    inference(forward_demodulation,[],[f46,f55])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ((~r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))) & v1_lattice3(k2_yellow_1(sK0)) & ~v1_xboole_0(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f35,f34,f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v1_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(sK0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) & v1_lattice3(k2_yellow_1(sK0)) & ~v1_xboole_0(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(sK0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) => (? [X2] : (~r1_tarski(k2_xboole_0(sK1,X2),k10_lattice3(k2_yellow_1(sK0),sK1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ? [X2] : (~r1_tarski(k2_xboole_0(sK1,X2),k10_lattice3(k2_yellow_1(sK0),sK1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) => (~r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v1_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0))),
% 0.22/0.50    inference(flattening,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ? [X0] : ((? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v1_lattice3(k2_yellow_1(X0))) & ~v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,negated_conjecture,(
% 0.22/0.50    ~! [X0] : (~v1_xboole_0(X0) => (v1_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f13])).
% 0.22/0.50  fof(f13,conjecture,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(X0) => (v1_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_1)).
% 0.22/0.50  fof(f997,plain,(
% 0.22/0.50    ~m1_subset_1(sK1,sK0) | r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.22/0.50    inference(forward_demodulation,[],[f996,f55])).
% 0.22/0.50  fof(f996,plain,(
% 0.22/0.50    r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.50    inference(subsumption_resolution,[],[f995,f367])).
% 0.22/0.50  fof(f367,plain,(
% 0.22/0.50    m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0)),
% 0.22/0.50    inference(resolution,[],[f275,f78])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    m1_subset_1(sK2,sK0)),
% 0.22/0.50    inference(forward_demodulation,[],[f47,f55])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f275,plain,(
% 0.22/0.50    ( ! [X1] : (~m1_subset_1(X1,sK0) | m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,X1),sK0)) )),
% 0.22/0.50    inference(resolution,[],[f132,f79])).
% 0.22/0.50  fof(f132,plain,(
% 0.22/0.50    ( ! [X14,X15] : (~m1_subset_1(X14,sK0) | ~m1_subset_1(X15,sK0) | m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X14,X15),sK0)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f131,f55])).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    ( ! [X14,X15] : (~m1_subset_1(X15,sK0) | m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X14,X15),sK0) | ~m1_subset_1(X14,u1_struct_0(k2_yellow_1(sK0)))) )),
% 0.22/0.50    inference(forward_demodulation,[],[f130,f55])).
% 0.22/0.50  fof(f130,plain,(
% 0.22/0.50    ( ! [X14,X15] : (m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X14,X15),sK0) | ~m1_subset_1(X15,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X14,u1_struct_0(k2_yellow_1(sK0)))) )),
% 0.22/0.50    inference(forward_demodulation,[],[f129,f55])).
% 0.22/0.50  fof(f129,plain,(
% 0.22/0.50    ( ! [X14,X15] : (m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X14,X15),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X15,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X14,u1_struct_0(k2_yellow_1(sK0)))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f128,f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.22/0.50  fof(f128,plain,(
% 0.22/0.50    ( ! [X14,X15] : (m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X14,X15),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X15,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X14,u1_struct_0(k2_yellow_1(sK0))) | ~v5_orders_2(k2_yellow_1(sK0))) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f94,f54])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    ( ! [X14,X15] : (m1_subset_1(k13_lattice3(k2_yellow_1(sK0),X14,X15),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X15,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X14,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0))) )),
% 0.22/0.50    inference(resolution,[],[f45,f72])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.22/0.50    inference(flattening,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k13_lattice3)).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    v1_lattice3(k2_yellow_1(sK0))),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f995,plain,(
% 0.22/0.50    ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.50    inference(forward_demodulation,[],[f994,f55])).
% 0.22/0.50  fof(f994,plain,(
% 0.22/0.50    r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.50    inference(subsumption_resolution,[],[f992,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ~v1_xboole_0(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f992,plain,(
% 0.22/0.50    r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | v1_xboole_0(sK0)),
% 0.22/0.50    inference(resolution,[],[f829,f59])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,axiom,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).
% 0.22/0.50  fof(f829,plain,(
% 0.22/0.50    r3_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.22/0.50    inference(subsumption_resolution,[],[f828,f79])).
% 0.22/0.50  fof(f828,plain,(
% 0.22/0.50    ~m1_subset_1(sK1,sK0) | r3_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.22/0.50    inference(forward_demodulation,[],[f827,f55])).
% 0.22/0.50  fof(f827,plain,(
% 0.22/0.50    r3_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.50    inference(subsumption_resolution,[],[f826,f367])).
% 0.22/0.50  fof(f826,plain,(
% 0.22/0.50    ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | r3_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.50    inference(forward_demodulation,[],[f825,f55])).
% 0.22/0.50  fof(f825,plain,(
% 0.22/0.50    r3_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.50    inference(subsumption_resolution,[],[f824,f82])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    ~v2_struct_0(k2_yellow_1(sK0))),
% 0.22/0.50    inference(resolution,[],[f44,f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : ((v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).
% 0.22/0.50  fof(f824,plain,(
% 0.22/0.50    r3_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | v2_struct_0(k2_yellow_1(sK0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f823,f50])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f9])).
% 0.22/0.50  fof(f823,plain,(
% 0.22/0.50    r3_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~v3_orders_2(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0))),
% 0.22/0.50    inference(subsumption_resolution,[],[f746,f54])).
% 0.22/0.50  fof(f746,plain,(
% 0.22/0.50    r3_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0))),
% 0.22/0.50    inference(resolution,[],[f711,f71])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.22/0.51  fof(f711,plain,(
% 0.22/0.51    r1_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.22/0.51    inference(backward_demodulation,[],[f647,f681])).
% 0.22/0.51  fof(f681,plain,(
% 0.22/0.51    k13_lattice3(k2_yellow_1(sK0),sK1,sK2) = k13_lattice3(k2_yellow_1(sK0),sK2,sK1)),
% 0.22/0.51    inference(backward_demodulation,[],[f504,f675])).
% 0.22/0.51  fof(f675,plain,(
% 0.22/0.51    k10_lattice3(k2_yellow_1(sK0),sK1,sK2) = k13_lattice3(k2_yellow_1(sK0),sK1,sK2)),
% 0.22/0.51    inference(resolution,[],[f344,f78])).
% 0.22/0.51  fof(f344,plain,(
% 0.22/0.51    ( ! [X1] : (~m1_subset_1(X1,sK0) | k13_lattice3(k2_yellow_1(sK0),sK1,X1) = k10_lattice3(k2_yellow_1(sK0),sK1,X1)) )),
% 0.22/0.51    inference(resolution,[],[f136,f79])).
% 0.22/0.51  fof(f136,plain,(
% 0.22/0.51    ( ! [X17,X16] : (~m1_subset_1(X16,sK0) | ~m1_subset_1(X17,sK0) | k13_lattice3(k2_yellow_1(sK0),X16,X17) = k10_lattice3(k2_yellow_1(sK0),X16,X17)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f135,f55])).
% 0.22/0.51  fof(f135,plain,(
% 0.22/0.51    ( ! [X17,X16] : (~m1_subset_1(X17,sK0) | k13_lattice3(k2_yellow_1(sK0),X16,X17) = k10_lattice3(k2_yellow_1(sK0),X16,X17) | ~m1_subset_1(X16,u1_struct_0(k2_yellow_1(sK0)))) )),
% 0.22/0.51    inference(forward_demodulation,[],[f134,f55])).
% 0.22/0.51  fof(f134,plain,(
% 0.22/0.51    ( ! [X17,X16] : (k13_lattice3(k2_yellow_1(sK0),X16,X17) = k10_lattice3(k2_yellow_1(sK0),X16,X17) | ~m1_subset_1(X17,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X16,u1_struct_0(k2_yellow_1(sK0)))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f133,f52])).
% 0.22/0.51  fof(f133,plain,(
% 0.22/0.51    ( ! [X17,X16] : (k13_lattice3(k2_yellow_1(sK0),X16,X17) = k10_lattice3(k2_yellow_1(sK0),X16,X17) | ~m1_subset_1(X17,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X16,u1_struct_0(k2_yellow_1(sK0))) | ~v5_orders_2(k2_yellow_1(sK0))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f95,f54])).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    ( ! [X17,X16] : (k13_lattice3(k2_yellow_1(sK0),X16,X17) = k10_lattice3(k2_yellow_1(sK0),X16,X17) | ~m1_subset_1(X17,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X16,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0))) )),
% 0.22/0.51    inference(resolution,[],[f45,f73])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.22/0.51    inference(flattening,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).
% 0.22/0.51  fof(f504,plain,(
% 0.22/0.51    k10_lattice3(k2_yellow_1(sK0),sK1,sK2) = k13_lattice3(k2_yellow_1(sK0),sK2,sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f503,f78])).
% 0.22/0.51  fof(f503,plain,(
% 0.22/0.51    ~m1_subset_1(sK2,sK0) | k10_lattice3(k2_yellow_1(sK0),sK1,sK2) = k13_lattice3(k2_yellow_1(sK0),sK2,sK1)),
% 0.22/0.51    inference(forward_demodulation,[],[f502,f55])).
% 0.22/0.51  fof(f502,plain,(
% 0.22/0.51    k10_lattice3(k2_yellow_1(sK0),sK1,sK2) = k13_lattice3(k2_yellow_1(sK0),sK2,sK1) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f501,f79])).
% 0.22/0.51  fof(f501,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,sK0) | k10_lattice3(k2_yellow_1(sK0),sK1,sK2) = k13_lattice3(k2_yellow_1(sK0),sK2,sK1) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.51    inference(forward_demodulation,[],[f500,f55])).
% 0.22/0.51  fof(f500,plain,(
% 0.22/0.51    k10_lattice3(k2_yellow_1(sK0),sK1,sK2) = k13_lattice3(k2_yellow_1(sK0),sK2,sK1) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f499,f52])).
% 0.22/0.51  fof(f499,plain,(
% 0.22/0.51    k10_lattice3(k2_yellow_1(sK0),sK1,sK2) = k13_lattice3(k2_yellow_1(sK0),sK2,sK1) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~v5_orders_2(k2_yellow_1(sK0))),
% 0.22/0.51    inference(subsumption_resolution,[],[f498,f45])).
% 0.22/0.51  fof(f498,plain,(
% 0.22/0.51    k10_lattice3(k2_yellow_1(sK0),sK1,sK2) = k13_lattice3(k2_yellow_1(sK0),sK2,sK1) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~v1_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0))),
% 0.22/0.51    inference(subsumption_resolution,[],[f449,f54])).
% 0.22/0.51  fof(f449,plain,(
% 0.22/0.51    k10_lattice3(k2_yellow_1(sK0),sK1,sK2) = k13_lattice3(k2_yellow_1(sK0),sK2,sK1) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v1_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0))),
% 0.22/0.51    inference(superposition,[],[f440,f73])).
% 0.22/0.51  fof(f440,plain,(
% 0.22/0.51    k10_lattice3(k2_yellow_1(sK0),sK1,sK2) = k10_lattice3(k2_yellow_1(sK0),sK2,sK1)),
% 0.22/0.51    inference(resolution,[],[f338,f79])).
% 0.22/0.51  fof(f338,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,sK0) | k10_lattice3(k2_yellow_1(sK0),sK2,X0) = k10_lattice3(k2_yellow_1(sK0),X0,sK2)) )),
% 0.22/0.51    inference(resolution,[],[f127,f78])).
% 0.22/0.51  fof(f127,plain,(
% 0.22/0.51    ( ! [X12,X13] : (~m1_subset_1(X12,sK0) | ~m1_subset_1(X13,sK0) | k10_lattice3(k2_yellow_1(sK0),X12,X13) = k10_lattice3(k2_yellow_1(sK0),X13,X12)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f126,f55])).
% 0.22/0.51  fof(f126,plain,(
% 0.22/0.51    ( ! [X12,X13] : (~m1_subset_1(X13,sK0) | k10_lattice3(k2_yellow_1(sK0),X12,X13) = k10_lattice3(k2_yellow_1(sK0),X13,X12) | ~m1_subset_1(X12,u1_struct_0(k2_yellow_1(sK0)))) )),
% 0.22/0.51    inference(forward_demodulation,[],[f125,f55])).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    ( ! [X12,X13] : (k10_lattice3(k2_yellow_1(sK0),X12,X13) = k10_lattice3(k2_yellow_1(sK0),X13,X12) | ~m1_subset_1(X13,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X12,u1_struct_0(k2_yellow_1(sK0)))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f124,f52])).
% 0.22/0.51  fof(f124,plain,(
% 0.22/0.51    ( ! [X12,X13] : (k10_lattice3(k2_yellow_1(sK0),X12,X13) = k10_lattice3(k2_yellow_1(sK0),X13,X12) | ~m1_subset_1(X13,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X12,u1_struct_0(k2_yellow_1(sK0))) | ~v5_orders_2(k2_yellow_1(sK0))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f93,f54])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    ( ! [X12,X13] : (k10_lattice3(k2_yellow_1(sK0),X12,X13) = k10_lattice3(k2_yellow_1(sK0),X13,X12) | ~m1_subset_1(X13,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(X12,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0))) )),
% 0.22/0.51    inference(resolution,[],[f45,f69])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.22/0.51    inference(flattening,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_lattice3)).
% 0.22/0.51  fof(f647,plain,(
% 0.22/0.51    r1_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK2,sK1))),
% 0.22/0.51    inference(subsumption_resolution,[],[f646,f78])).
% 0.22/0.51  fof(f646,plain,(
% 0.22/0.51    ~m1_subset_1(sK2,sK0) | r1_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK2,sK1))),
% 0.22/0.51    inference(forward_demodulation,[],[f645,f55])).
% 0.22/0.51  fof(f645,plain,(
% 0.22/0.51    r1_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK2,sK1)) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f644,f79])).
% 0.22/0.51  fof(f644,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,sK0) | r1_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK2,sK1)) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.51    inference(forward_demodulation,[],[f643,f55])).
% 0.22/0.51  fof(f643,plain,(
% 0.22/0.51    r1_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK2,sK1)) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f642,f284])).
% 0.22/0.51  fof(f284,plain,(
% 0.22/0.51    m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK2,sK1),sK0)),
% 0.22/0.51    inference(resolution,[],[f274,f79])).
% 0.22/0.51  fof(f274,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,sK0) | m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK2,X0),sK0)) )),
% 0.22/0.51    inference(resolution,[],[f132,f78])).
% 0.22/0.51  fof(f642,plain,(
% 0.22/0.51    ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK2,sK1),sK0) | r1_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK2,sK1)) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.51    inference(forward_demodulation,[],[f641,f55])).
% 0.22/0.51  fof(f641,plain,(
% 0.22/0.51    ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK2,sK1),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK2,sK1)) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f640,f82])).
% 0.22/0.51  fof(f640,plain,(
% 0.22/0.51    ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK2,sK1),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK2,sK1)) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | v2_struct_0(k2_yellow_1(sK0))),
% 0.22/0.51    inference(subsumption_resolution,[],[f639,f52])).
% 0.22/0.51  fof(f639,plain,(
% 0.22/0.51    ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK2,sK1),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK2,sK1)) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~v5_orders_2(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0))),
% 0.22/0.51    inference(subsumption_resolution,[],[f638,f45])).
% 0.22/0.51  fof(f638,plain,(
% 0.22/0.51    ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK2,sK1),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK2,sK1)) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~v1_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0))),
% 0.22/0.51    inference(subsumption_resolution,[],[f574,f54])).
% 0.22/0.51  fof(f574,plain,(
% 0.22/0.51    ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK2,sK1),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),sK1,k13_lattice3(k2_yellow_1(sK0),sK2,sK1)) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v1_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0))),
% 0.22/0.51    inference(superposition,[],[f76,f511])).
% 0.22/0.51  fof(f511,plain,(
% 0.22/0.51    k10_lattice3(k2_yellow_1(sK0),sK2,sK1) = k13_lattice3(k2_yellow_1(sK0),sK2,sK1)),
% 0.22/0.51    inference(backward_demodulation,[],[f440,f504])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r1_orders_2(X0,X2,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f63])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X2,X3) | k10_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,X3,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3)) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f40,f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3)) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(rectify,[],[f39])).
% 0.22/0.51  % (26505)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k10_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3))) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k10_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k10_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l26_lattice3)).
% 0.22/0.51  fof(f1531,plain,(
% 0.22/0.51    ~r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.22/0.51    inference(resolution,[],[f1494,f270])).
% 0.22/0.51  fof(f270,plain,(
% 0.22/0.51    ~r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.22/0.51    inference(resolution,[],[f208,f74])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.22/0.51    inference(flattening,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.22/0.51  fof(f208,plain,(
% 0.22/0.51    ~r1_tarski(k2_xboole_0(sK1,sK2),k13_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f207,f79])).
% 0.22/0.51  fof(f207,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,sK0) | ~r1_tarski(k2_xboole_0(sK1,sK2),k13_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.22/0.51    inference(forward_demodulation,[],[f206,f55])).
% 0.22/0.51  fof(f206,plain,(
% 0.22/0.51    ~r1_tarski(k2_xboole_0(sK1,sK2),k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f205,f78])).
% 0.22/0.51  fof(f205,plain,(
% 0.22/0.51    ~m1_subset_1(sK2,sK0) | ~r1_tarski(k2_xboole_0(sK1,sK2),k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.51    inference(forward_demodulation,[],[f204,f55])).
% 0.22/0.51  fof(f204,plain,(
% 0.22/0.51    ~r1_tarski(k2_xboole_0(sK1,sK2),k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f203,f52])).
% 0.22/0.51  fof(f203,plain,(
% 0.22/0.51    ~r1_tarski(k2_xboole_0(sK1,sK2),k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~v5_orders_2(k2_yellow_1(sK0))),
% 0.22/0.51    inference(subsumption_resolution,[],[f202,f45])).
% 0.22/0.51  fof(f202,plain,(
% 0.22/0.51    ~r1_tarski(k2_xboole_0(sK1,sK2),k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~v1_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0))),
% 0.22/0.51    inference(subsumption_resolution,[],[f162,f54])).
% 0.22/0.51  fof(f162,plain,(
% 0.22/0.51    ~r1_tarski(k2_xboole_0(sK1,sK2),k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v1_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0))),
% 0.22/0.51    inference(superposition,[],[f48,f73])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ~r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.22/0.51    inference(cnf_transformation,[],[f36])).
% 0.22/0.51  fof(f1494,plain,(
% 0.22/0.51    r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f1493,f78])).
% 0.22/0.51  fof(f1493,plain,(
% 0.22/0.51    ~m1_subset_1(sK2,sK0) | r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.22/0.51    inference(forward_demodulation,[],[f1492,f55])).
% 0.22/0.51  fof(f1492,plain,(
% 0.22/0.51    r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f1491,f367])).
% 0.22/0.51  fof(f1491,plain,(
% 0.22/0.51    ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.51    inference(forward_demodulation,[],[f1490,f55])).
% 0.22/0.51  fof(f1490,plain,(
% 0.22/0.51    r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f1488,f44])).
% 0.22/0.51  fof(f1488,plain,(
% 0.22/0.51    r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | v1_xboole_0(sK0)),
% 0.22/0.51    inference(resolution,[],[f960,f59])).
% 0.22/0.51  fof(f960,plain,(
% 0.22/0.51    r3_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f959,f78])).
% 0.22/0.51  fof(f959,plain,(
% 0.22/0.51    ~m1_subset_1(sK2,sK0) | r3_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.22/0.51    inference(forward_demodulation,[],[f958,f55])).
% 0.22/0.51  fof(f958,plain,(
% 0.22/0.51    r3_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f957,f367])).
% 0.22/0.51  fof(f957,plain,(
% 0.22/0.51    ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),sK0) | r3_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.51    inference(forward_demodulation,[],[f956,f55])).
% 0.22/0.51  fof(f956,plain,(
% 0.22/0.51    r3_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f955,f82])).
% 0.22/0.51  fof(f955,plain,(
% 0.22/0.51    r3_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | v2_struct_0(k2_yellow_1(sK0))),
% 0.22/0.51    inference(subsumption_resolution,[],[f954,f50])).
% 0.22/0.51  fof(f954,plain,(
% 0.22/0.51    r3_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~v3_orders_2(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0))),
% 0.22/0.51    inference(subsumption_resolution,[],[f877,f54])).
% 0.22/0.51  fof(f877,plain,(
% 0.22/0.51    r3_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK1,sK2),u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v3_orders_2(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0))),
% 0.22/0.51    inference(resolution,[],[f712,f71])).
% 0.22/0.51  fof(f712,plain,(
% 0.22/0.51    r1_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.22/0.51    inference(backward_demodulation,[],[f657,f681])).
% 0.22/0.51  fof(f657,plain,(
% 0.22/0.51    r1_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK2,sK1))),
% 0.22/0.51    inference(subsumption_resolution,[],[f656,f78])).
% 0.22/0.51  fof(f656,plain,(
% 0.22/0.51    ~m1_subset_1(sK2,sK0) | r1_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK2,sK1))),
% 0.22/0.51    inference(forward_demodulation,[],[f655,f55])).
% 0.22/0.51  fof(f655,plain,(
% 0.22/0.51    r1_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK2,sK1)) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f654,f79])).
% 0.22/0.51  fof(f654,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,sK0) | r1_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK2,sK1)) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.51    inference(forward_demodulation,[],[f653,f55])).
% 0.22/0.51  fof(f653,plain,(
% 0.22/0.51    r1_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK2,sK1)) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f652,f284])).
% 0.22/0.51  fof(f652,plain,(
% 0.22/0.51    ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK2,sK1),sK0) | r1_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK2,sK1)) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.51    inference(forward_demodulation,[],[f651,f55])).
% 0.22/0.51  fof(f651,plain,(
% 0.22/0.51    ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK2,sK1),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK2,sK1)) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.22/0.51    inference(subsumption_resolution,[],[f650,f82])).
% 0.22/0.51  fof(f650,plain,(
% 0.22/0.51    ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK2,sK1),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK2,sK1)) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | v2_struct_0(k2_yellow_1(sK0))),
% 0.22/0.51    inference(subsumption_resolution,[],[f649,f52])).
% 0.22/0.51  fof(f649,plain,(
% 0.22/0.51    ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK2,sK1),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK2,sK1)) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~v5_orders_2(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0))),
% 0.22/0.51    inference(subsumption_resolution,[],[f648,f45])).
% 0.22/0.51  fof(f648,plain,(
% 0.22/0.51    ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK2,sK1),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK2,sK1)) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~v1_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0))),
% 0.22/0.51    inference(subsumption_resolution,[],[f576,f54])).
% 0.22/0.51  fof(f576,plain,(
% 0.22/0.51    ~m1_subset_1(k13_lattice3(k2_yellow_1(sK0),sK2,sK1),u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),sK2,k13_lattice3(k2_yellow_1(sK0),sK2,sK1)) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v1_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0))),
% 0.22/0.51    inference(superposition,[],[f77,f511])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,k10_lattice3(X0,X1,X2)) | ~m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(equality_resolution,[],[f62])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X1,X3) | k10_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f42])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (26495)------------------------------
% 0.22/0.51  % (26495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (26495)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (26495)Memory used [KB]: 2302
% 0.22/0.51  % (26495)Time elapsed: 0.084 s
% 0.22/0.51  % (26495)------------------------------
% 0.22/0.51  % (26495)------------------------------
% 0.22/0.51  % (26502)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.51  % (26487)Success in time 0.148 s
%------------------------------------------------------------------------------
