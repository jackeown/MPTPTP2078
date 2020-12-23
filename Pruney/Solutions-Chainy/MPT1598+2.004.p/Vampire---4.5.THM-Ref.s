%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 351 expanded)
%              Number of leaves         :   16 ( 101 expanded)
%              Depth                    :   33
%              Number of atoms          :  640 (1744 expanded)
%              Number of equality atoms :   27 ( 104 expanded)
%              Maximal formula depth    :   17 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f200,plain,(
    $false ),
    inference(subsumption_resolution,[],[f199,f45])).

fof(f45,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    & v1_lattice3(k2_yellow_1(sK0))
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f36,f35,f34])).

fof(f34,plain,
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

fof(f35,plain,
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

fof(f36,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k2_xboole_0(sK1,X2),k10_lattice3(k2_yellow_1(sK0),sK1,X2))
        & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0))) )
   => ( ~ r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
      & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v1_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & v1_lattice3(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( v1_lattice3(k2_yellow_1(X0))
         => ! [X1] :
              ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
                 => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_lattice3(k2_yellow_1(X0))
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_1)).

fof(f199,plain,(
    v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f198,f46])).

fof(f46,plain,(
    v1_lattice3(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f37])).

fof(f198,plain,
    ( ~ v1_lattice3(k2_yellow_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f197,f75])).

fof(f75,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(backward_demodulation,[],[f48,f53])).

fof(f53,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f48,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f197,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ v1_lattice3(k2_yellow_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f191,f74])).

fof(f74,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f47,f53])).

fof(f47,plain,(
    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f191,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | ~ m1_subset_1(sK2,sK0)
    | ~ v1_lattice3(k2_yellow_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f190,f184])).

fof(f184,plain,(
    ~ r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(subsumption_resolution,[],[f183,f45])).

fof(f183,plain,
    ( v1_xboole_0(sK0)
    | ~ r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(subsumption_resolution,[],[f182,f75])).

fof(f182,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK0)
    | ~ r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(subsumption_resolution,[],[f181,f46])).

fof(f181,plain,
    ( ~ v1_lattice3(k2_yellow_1(sK0))
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK0)
    | ~ r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(subsumption_resolution,[],[f176,f74])).

fof(f176,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | ~ v1_lattice3(k2_yellow_1(sK0))
    | ~ m1_subset_1(sK2,sK0)
    | v1_xboole_0(sK0)
    | ~ r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(resolution,[],[f175,f106])).

fof(f106,plain,
    ( ~ r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(subsumption_resolution,[],[f105,f74])).

fof(f105,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | ~ r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(forward_demodulation,[],[f104,f53])).

fof(f104,plain,
    ( ~ r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f103,f75])).

fof(f103,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | ~ r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(forward_demodulation,[],[f102,f53])).

fof(f102,plain,
    ( ~ r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f101,f51])).

fof(f51,plain,(
    ! [X0] : v5_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v5_orders_2(k2_yellow_1(X0))
      & v3_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,plain,(
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

fof(f101,plain,
    ( ~ r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ v5_orders_2(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f100,f46])).

fof(f100,plain,
    ( ~ r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ v1_lattice3(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f92,f52])).

fof(f52,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f92,plain,
    ( ~ r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ v1_lattice3(k2_yellow_1(sK0))
    | ~ v5_orders_2(k2_yellow_1(sK0)) ),
    inference(superposition,[],[f82,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(f82,plain,
    ( ~ r1_tarski(sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))
    | ~ r1_tarski(sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(resolution,[],[f70,f49])).

fof(f49,plain,(
    ~ r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f175,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k13_lattice3(k2_yellow_1(X1),X0,X2))
      | ~ m1_subset_1(X0,X1)
      | ~ v1_lattice3(k2_yellow_1(X1))
      | ~ m1_subset_1(X2,X1)
      | v1_xboole_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f174])).

fof(f174,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X1)
      | ~ m1_subset_1(X0,X1)
      | ~ v1_lattice3(k2_yellow_1(X1))
      | r1_tarski(X2,k13_lattice3(k2_yellow_1(X1),X0,X2))
      | ~ m1_subset_1(X2,X1)
      | v1_xboole_0(X1) ) ),
    inference(forward_demodulation,[],[f173,f53])).

fof(f173,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | ~ v1_lattice3(k2_yellow_1(X1))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
      | r1_tarski(X2,k13_lattice3(k2_yellow_1(X1),X0,X2))
      | ~ m1_subset_1(X2,X1)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f172,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k13_lattice3(k2_yellow_1(X0),X1,X2),X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_lattice3(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f86,f51])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k13_lattice3(k2_yellow_1(X0),X1,X2),X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f85,f52])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k13_lattice3(k2_yellow_1(X0),X1,X2),X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v1_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f68,f53])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k13_lattice3)).

fof(f172,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | ~ v1_lattice3(k2_yellow_1(X1))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(X1),X0,X2),X1)
      | r1_tarski(X2,k13_lattice3(k2_yellow_1(X1),X0,X2))
      | ~ m1_subset_1(X2,X1)
      | v1_xboole_0(X1) ) ),
    inference(forward_demodulation,[],[f171,f53])).

fof(f171,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
      | ~ v1_lattice3(k2_yellow_1(X1))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(X1),X0,X2),X1)
      | r1_tarski(X2,k13_lattice3(k2_yellow_1(X1),X0,X2))
      | ~ m1_subset_1(X2,X1)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f170,f50])).

fof(f50,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
      | ~ v1_lattice3(k2_yellow_1(X1))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
      | ~ v3_orders_2(k2_yellow_1(X1))
      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(X1),X0,X2),X1)
      | r1_tarski(X2,k13_lattice3(k2_yellow_1(X1),X0,X2))
      | ~ m1_subset_1(X2,X1)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f169,f51])).

fof(f169,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
      | ~ v1_lattice3(k2_yellow_1(X1))
      | ~ v5_orders_2(k2_yellow_1(X1))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
      | ~ v3_orders_2(k2_yellow_1(X1))
      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(X1),X0,X2),X1)
      | r1_tarski(X2,k13_lattice3(k2_yellow_1(X1),X0,X2))
      | ~ m1_subset_1(X2,X1)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f164,f52])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
      | ~ l1_orders_2(k2_yellow_1(X1))
      | ~ v1_lattice3(k2_yellow_1(X1))
      | ~ v5_orders_2(k2_yellow_1(X1))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
      | ~ v3_orders_2(k2_yellow_1(X1))
      | ~ m1_subset_1(k13_lattice3(k2_yellow_1(X1),X0,X2),X1)
      | r1_tarski(X2,k13_lattice3(k2_yellow_1(X1),X0,X2))
      | ~ m1_subset_1(X2,X1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f163,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f78,f53])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f55,f53])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) )
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f163,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X2,k13_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v3_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f162,f68])).

fof(f162,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | r3_orders_2(X0,X2,k13_lattice3(X0,X1,X2))
      | ~ v3_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f161,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_lattice3(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f161,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | r3_orders_2(X0,X2,k13_lattice3(X0,X1,X2))
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f156])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | r3_orders_2(X0,X2,k13_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f72,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X2,k13_lattice3(X0,X1,X2))
      | ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | k13_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
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
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f41,f42])).

fof(f42,plain,(
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

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
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
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
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
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
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
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k13_lattice3(X0,X1,X2) = X3
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
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k13_lattice3(X0,X1,X2) = X3
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
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k13_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X2,X4)
                              & r1_orders_2(X0,X1,X4) )
                           => r1_orders_2(X0,X3,X4) ) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_yellow_0)).

fof(f190,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k13_lattice3(k2_yellow_1(X0),X2,X1))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_lattice3(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f189])).

fof(f189,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | r1_tarski(X2,k13_lattice3(k2_yellow_1(X0),X2,X1))
      | ~ m1_subset_1(X1,X0)
      | ~ v1_lattice3(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f188,f53])).

fof(f188,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | r1_tarski(X2,k13_lattice3(k2_yellow_1(X0),X2,X1))
      | ~ m1_subset_1(X1,X0)
      | ~ v1_lattice3(k2_yellow_1(X0))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) ) ),
    inference(duplicate_literal_removal,[],[f187])).

fof(f187,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,X0)
      | r1_tarski(X2,k13_lattice3(k2_yellow_1(X0),X2,X1))
      | ~ m1_subset_1(X1,X0)
      | ~ v1_lattice3(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) ) ),
    inference(forward_demodulation,[],[f186,f53])).

fof(f186,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k13_lattice3(k2_yellow_1(X0),X2,X1))
      | ~ m1_subset_1(X1,X0)
      | ~ v1_lattice3(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) ) ),
    inference(subsumption_resolution,[],[f185,f51])).

fof(f185,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k13_lattice3(k2_yellow_1(X0),X2,X1))
      | ~ m1_subset_1(X1,X0)
      | ~ v1_lattice3(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(subsumption_resolution,[],[f180,f52])).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k13_lattice3(k2_yellow_1(X0),X2,X1))
      | ~ m1_subset_1(X1,X0)
      | ~ v1_lattice3(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f177])).

fof(f177,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k13_lattice3(k2_yellow_1(X0),X2,X1))
      | ~ m1_subset_1(X1,X0)
      | ~ v1_lattice3(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ v1_lattice3(k2_yellow_1(X0))
      | ~ v5_orders_2(k2_yellow_1(X0)) ) ),
    inference(superposition,[],[f175,f128])).

fof(f128,plain,(
    ! [X4,X5,X3] :
      ( k13_lattice3(X3,X4,X5) = k13_lattice3(X3,X5,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v1_lattice3(X3)
      | ~ v5_orders_2(X3) ) ),
    inference(duplicate_literal_removal,[],[f115])).

fof(f115,plain,(
    ! [X4,X5,X3] :
      ( k13_lattice3(X3,X4,X5) = k13_lattice3(X3,X5,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v1_lattice3(X3)
      | ~ v5_orders_2(X3)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v1_lattice3(X3)
      | ~ v5_orders_2(X3) ) ),
    inference(superposition,[],[f99,f69])).

fof(f99,plain,(
    ! [X4,X5,X3] :
      ( k10_lattice3(X3,X5,X4) = k13_lattice3(X3,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v1_lattice3(X3)
      | ~ v5_orders_2(X3) ) ),
    inference(duplicate_literal_removal,[],[f90])).

fof(f90,plain,(
    ! [X4,X5,X3] :
      ( k10_lattice3(X3,X5,X4) = k13_lattice3(X3,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v1_lattice3(X3)
      | ~ v5_orders_2(X3)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v1_lattice3(X3)
      | ~ v5_orders_2(X3) ) ),
    inference(superposition,[],[f69,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

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
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_lattice3)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:46:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (6398)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.46  % (6388)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.46  % (6398)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % (6390)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.46  % (6381)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (6387)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.47  % (6380)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f200,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(subsumption_resolution,[],[f199,f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ~v1_xboole_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ((~r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))) & v1_lattice3(k2_yellow_1(sK0)) & ~v1_xboole_0(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f36,f35,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v1_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(sK0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) & v1_lattice3(k2_yellow_1(sK0)) & ~v1_xboole_0(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(sK0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))) => (? [X2] : (~r1_tarski(k2_xboole_0(sK1,X2),k10_lattice3(k2_yellow_1(sK0),sK1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) & m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ? [X2] : (~r1_tarski(k2_xboole_0(sK1,X2),k10_lattice3(k2_yellow_1(sK0),sK1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(sK0)))) => (~r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v1_lattice3(k2_yellow_1(X0)) & ~v1_xboole_0(X0))),
% 0.21/0.47    inference(flattening,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ? [X0] : ((? [X1] : (? [X2] : (~r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & v1_lattice3(k2_yellow_1(X0))) & ~v1_xboole_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (~v1_xboole_0(X0) => (v1_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))))))),
% 0.21/0.47    inference(negated_conjecture,[],[f12])).
% 0.21/0.47  fof(f12,conjecture,(
% 0.21/0.47    ! [X0] : (~v1_xboole_0(X0) => (v1_lattice3(k2_yellow_1(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => r1_tarski(k2_xboole_0(X1,X2),k10_lattice3(k2_yellow_1(X0),X1,X2))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_1)).
% 0.21/0.47  fof(f199,plain,(
% 0.21/0.47    v1_xboole_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f198,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    v1_lattice3(k2_yellow_1(sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f37])).
% 0.21/0.47  fof(f198,plain,(
% 0.21/0.47    ~v1_lattice3(k2_yellow_1(sK0)) | v1_xboole_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f197,f75])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    m1_subset_1(sK2,sK0)),
% 0.21/0.47    inference(backward_demodulation,[],[f48,f53])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.47    inference(cnf_transformation,[],[f37])).
% 0.21/0.47  fof(f197,plain,(
% 0.21/0.47    ~m1_subset_1(sK2,sK0) | ~v1_lattice3(k2_yellow_1(sK0)) | v1_xboole_0(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f191,f74])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    m1_subset_1(sK1,sK0)),
% 0.21/0.47    inference(backward_demodulation,[],[f47,f53])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.47    inference(cnf_transformation,[],[f37])).
% 0.21/0.47  fof(f191,plain,(
% 0.21/0.47    ~m1_subset_1(sK1,sK0) | ~m1_subset_1(sK2,sK0) | ~v1_lattice3(k2_yellow_1(sK0)) | v1_xboole_0(sK0)),
% 0.21/0.47    inference(resolution,[],[f190,f184])).
% 0.21/0.47  fof(f184,plain,(
% 0.21/0.47    ~r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.21/0.47    inference(subsumption_resolution,[],[f183,f45])).
% 0.21/0.47  fof(f183,plain,(
% 0.21/0.47    v1_xboole_0(sK0) | ~r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.21/0.47    inference(subsumption_resolution,[],[f182,f75])).
% 0.21/0.47  fof(f182,plain,(
% 0.21/0.47    ~m1_subset_1(sK2,sK0) | v1_xboole_0(sK0) | ~r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.21/0.47    inference(subsumption_resolution,[],[f181,f46])).
% 0.21/0.47  fof(f181,plain,(
% 0.21/0.47    ~v1_lattice3(k2_yellow_1(sK0)) | ~m1_subset_1(sK2,sK0) | v1_xboole_0(sK0) | ~r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.21/0.47    inference(subsumption_resolution,[],[f176,f74])).
% 0.21/0.47  fof(f176,plain,(
% 0.21/0.47    ~m1_subset_1(sK1,sK0) | ~v1_lattice3(k2_yellow_1(sK0)) | ~m1_subset_1(sK2,sK0) | v1_xboole_0(sK0) | ~r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.21/0.47    inference(resolution,[],[f175,f106])).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    ~r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.21/0.47    inference(subsumption_resolution,[],[f105,f74])).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    ~m1_subset_1(sK1,sK0) | ~r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.21/0.47    inference(forward_demodulation,[],[f104,f53])).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    ~r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.47    inference(subsumption_resolution,[],[f103,f75])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    ~m1_subset_1(sK2,sK0) | ~r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.47    inference(forward_demodulation,[],[f102,f53])).
% 0.21/0.47  fof(f102,plain,(
% 0.21/0.47    ~r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.47    inference(subsumption_resolution,[],[f101,f51])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X0] : (v5_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)))),
% 0.21/0.47    inference(pure_predicate_removal,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.47    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    ~r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~v5_orders_2(k2_yellow_1(sK0))),
% 0.21/0.47    inference(subsumption_resolution,[],[f100,f46])).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    ~r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~v1_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0))),
% 0.21/0.47    inference(subsumption_resolution,[],[f92,f52])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 0.21/0.47    inference(pure_predicate_removal,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    ~r1_tarski(sK2,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~r1_tarski(sK1,k13_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | ~v1_lattice3(k2_yellow_1(sK0)) | ~v5_orders_2(k2_yellow_1(sK0))),
% 0.21/0.47    inference(superposition,[],[f82,f69])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.47    inference(flattening,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => k13_lattice3(X0,X1,X2) = k10_lattice3(X0,X1,X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    ~r1_tarski(sK2,k10_lattice3(k2_yellow_1(sK0),sK1,sK2)) | ~r1_tarski(sK1,k10_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.21/0.47    inference(resolution,[],[f70,f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ~r1_tarski(k2_xboole_0(sK1,sK2),k10_lattice3(k2_yellow_1(sK0),sK1,sK2))),
% 0.21/0.47    inference(cnf_transformation,[],[f37])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.21/0.47  fof(f175,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(X2,k13_lattice3(k2_yellow_1(X1),X0,X2)) | ~m1_subset_1(X0,X1) | ~v1_lattice3(k2_yellow_1(X1)) | ~m1_subset_1(X2,X1) | v1_xboole_0(X1)) )),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f174])).
% 0.21/0.47  fof(f174,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X1) | ~m1_subset_1(X0,X1) | ~v1_lattice3(k2_yellow_1(X1)) | r1_tarski(X2,k13_lattice3(k2_yellow_1(X1),X0,X2)) | ~m1_subset_1(X2,X1) | v1_xboole_0(X1)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f173,f53])).
% 0.21/0.47  fof(f173,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X0,X1) | ~v1_lattice3(k2_yellow_1(X1)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) | r1_tarski(X2,k13_lattice3(k2_yellow_1(X1),X0,X2)) | ~m1_subset_1(X2,X1) | v1_xboole_0(X1)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f172,f87])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (m1_subset_1(k13_lattice3(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~v1_lattice3(k2_yellow_1(X0))) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f86,f51])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (m1_subset_1(k13_lattice3(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~v1_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f85,f52])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (m1_subset_1(k13_lattice3(k2_yellow_1(X0),X1,X2),X0) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~l1_orders_2(k2_yellow_1(X0)) | ~v1_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.47    inference(superposition,[],[f68,f53])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.47    inference(flattening,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k13_lattice3)).
% 0.21/0.47  fof(f172,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X0,X1) | ~v1_lattice3(k2_yellow_1(X1)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) | ~m1_subset_1(k13_lattice3(k2_yellow_1(X1),X0,X2),X1) | r1_tarski(X2,k13_lattice3(k2_yellow_1(X1),X0,X2)) | ~m1_subset_1(X2,X1) | v1_xboole_0(X1)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f171,f53])).
% 0.21/0.47  fof(f171,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) | ~v1_lattice3(k2_yellow_1(X1)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) | ~m1_subset_1(k13_lattice3(k2_yellow_1(X1),X0,X2),X1) | r1_tarski(X2,k13_lattice3(k2_yellow_1(X1),X0,X2)) | ~m1_subset_1(X2,X1) | v1_xboole_0(X1)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f170,f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) | ~v1_lattice3(k2_yellow_1(X1)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) | ~v3_orders_2(k2_yellow_1(X1)) | ~m1_subset_1(k13_lattice3(k2_yellow_1(X1),X0,X2),X1) | r1_tarski(X2,k13_lattice3(k2_yellow_1(X1),X0,X2)) | ~m1_subset_1(X2,X1) | v1_xboole_0(X1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f169,f51])).
% 0.21/0.48  fof(f169,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) | ~v1_lattice3(k2_yellow_1(X1)) | ~v5_orders_2(k2_yellow_1(X1)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) | ~v3_orders_2(k2_yellow_1(X1)) | ~m1_subset_1(k13_lattice3(k2_yellow_1(X1),X0,X2),X1) | r1_tarski(X2,k13_lattice3(k2_yellow_1(X1),X0,X2)) | ~m1_subset_1(X2,X1) | v1_xboole_0(X1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f164,f52])).
% 0.21/0.48  fof(f164,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) | ~l1_orders_2(k2_yellow_1(X1)) | ~v1_lattice3(k2_yellow_1(X1)) | ~v5_orders_2(k2_yellow_1(X1)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) | ~v3_orders_2(k2_yellow_1(X1)) | ~m1_subset_1(k13_lattice3(k2_yellow_1(X1),X0,X2),X1) | r1_tarski(X2,k13_lattice3(k2_yellow_1(X1),X0,X2)) | ~m1_subset_1(X2,X1) | v1_xboole_0(X1)) )),
% 0.21/0.48    inference(resolution,[],[f163,f79])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0) | r1_tarski(X1,X2) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f78,f53])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f55,f53])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (((r3_orders_2(k2_yellow_1(X0),X1,X2) | ~r1_tarski(X1,X2)) & (r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).
% 0.21/0.48  fof(f163,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r3_orders_2(X0,X2,k13_lattice3(X0,X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v3_orders_2(X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f162,f68])).
% 0.21/0.48  fof(f162,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | r3_orders_2(X0,X2,k13_lattice3(X0,X1,X2)) | ~v3_orders_2(X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f161,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_lattice3(X0) | ~v2_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : (~v2_struct_0(X0) | ~v1_lattice3(X0) | ~l1_orders_2(X0))),
% 0.21/0.48    inference(flattening,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : ((~v2_struct_0(X0) | ~v1_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : (l1_orders_2(X0) => (v1_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | r3_orders_2(X0,X2,k13_lattice3(X0,X1,X2)) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f156])).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0) | r3_orders_2(X0,X2,k13_lattice3(X0,X1,X2)) | ~m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(resolution,[],[f72,f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_orders_2(X0,X2,k13_lattice3(X0,X1,X2)) | ~m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X2,X3) | k13_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k13_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,X3,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3)) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k13_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f41,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,X3,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X2,sK3(X0,X1,X2,X3)) & r1_orders_2(X0,X1,sK3(X0,X1,X2,X3)) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k13_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X5] : (r1_orders_2(X0,X3,X5) | ~r1_orders_2(X0,X2,X5) | ~r1_orders_2(X0,X1,X5) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k13_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.48    inference(rectify,[],[f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k13_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3)) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k13_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.48    inference(flattening,[],[f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k13_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X3,X4) & r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X3))) & ((! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)) | k13_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k13_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X3,X4) | ~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.48    inference(flattening,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k13_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X3,X4) | (~r1_orders_2(X0,X2,X4) | ~r1_orders_2(X0,X1,X4))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k13_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X4) & r1_orders_2(X0,X1,X4)) => r1_orders_2(X0,X3,X4))) & r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X3)))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_yellow_0)).
% 0.21/0.48  fof(f190,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X2,k13_lattice3(k2_yellow_1(X0),X2,X1)) | ~m1_subset_1(X2,X0) | ~m1_subset_1(X1,X0) | ~v1_lattice3(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f189])).
% 0.21/0.48  fof(f189,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | ~m1_subset_1(X2,X0) | r1_tarski(X2,k13_lattice3(k2_yellow_1(X0),X2,X1)) | ~m1_subset_1(X1,X0) | ~v1_lattice3(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f188,f53])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | r1_tarski(X2,k13_lattice3(k2_yellow_1(X0),X2,X1)) | ~m1_subset_1(X1,X0) | ~v1_lattice3(k2_yellow_1(X0)) | v1_xboole_0(X0) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f187])).
% 0.21/0.48  fof(f187,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,X0) | r1_tarski(X2,k13_lattice3(k2_yellow_1(X0),X2,X1)) | ~m1_subset_1(X1,X0) | ~v1_lattice3(k2_yellow_1(X0)) | ~m1_subset_1(X2,X0) | v1_xboole_0(X0) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f186,f53])).
% 0.21/0.48  fof(f186,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X2,k13_lattice3(k2_yellow_1(X0),X2,X1)) | ~m1_subset_1(X1,X0) | ~v1_lattice3(k2_yellow_1(X0)) | ~m1_subset_1(X2,X0) | v1_xboole_0(X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f185,f51])).
% 0.21/0.48  fof(f185,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X2,k13_lattice3(k2_yellow_1(X0),X2,X1)) | ~m1_subset_1(X1,X0) | ~v1_lattice3(k2_yellow_1(X0)) | ~m1_subset_1(X2,X0) | v1_xboole_0(X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f180,f52])).
% 0.21/0.48  fof(f180,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X2,k13_lattice3(k2_yellow_1(X0),X2,X1)) | ~m1_subset_1(X1,X0) | ~v1_lattice3(k2_yellow_1(X0)) | ~m1_subset_1(X2,X0) | v1_xboole_0(X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~l1_orders_2(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f177])).
% 0.21/0.48  fof(f177,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r1_tarski(X2,k13_lattice3(k2_yellow_1(X0),X2,X1)) | ~m1_subset_1(X1,X0) | ~v1_lattice3(k2_yellow_1(X0)) | ~m1_subset_1(X2,X0) | v1_xboole_0(X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~l1_orders_2(k2_yellow_1(X0)) | ~v1_lattice3(k2_yellow_1(X0)) | ~v5_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.48    inference(superposition,[],[f175,f128])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    ( ! [X4,X5,X3] : (k13_lattice3(X3,X4,X5) = k13_lattice3(X3,X5,X4) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~l1_orders_2(X3) | ~v1_lattice3(X3) | ~v5_orders_2(X3)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f115])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    ( ! [X4,X5,X3] : (k13_lattice3(X3,X4,X5) = k13_lattice3(X3,X5,X4) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~l1_orders_2(X3) | ~v1_lattice3(X3) | ~v5_orders_2(X3) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l1_orders_2(X3) | ~v1_lattice3(X3) | ~v5_orders_2(X3)) )),
% 0.21/0.48    inference(superposition,[],[f99,f69])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    ( ! [X4,X5,X3] : (k10_lattice3(X3,X5,X4) = k13_lattice3(X3,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l1_orders_2(X3) | ~v1_lattice3(X3) | ~v5_orders_2(X3)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f90])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    ( ! [X4,X5,X3] : (k10_lattice3(X3,X5,X4) = k13_lattice3(X3,X4,X5) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l1_orders_2(X3) | ~v1_lattice3(X3) | ~v5_orders_2(X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~l1_orders_2(X3) | ~v1_lattice3(X3) | ~v5_orders_2(X3)) )),
% 0.21/0.48    inference(superposition,[],[f69,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.48    inference(flattening,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : ((l1_orders_2(X0) & v1_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k10_lattice3(X0,X1,X2) = k10_lattice3(X0,X2,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_lattice3)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (6398)------------------------------
% 0.21/0.48  % (6398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (6398)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (6398)Memory used [KB]: 1663
% 0.21/0.48  % (6398)Time elapsed: 0.064 s
% 0.21/0.48  % (6398)------------------------------
% 0.21/0.48  % (6398)------------------------------
% 0.21/0.48  % (6381)Refutation not found, incomplete strategy% (6381)------------------------------
% 0.21/0.48  % (6381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (6381)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (6381)Memory used [KB]: 10618
% 0.21/0.48  % (6381)Time elapsed: 0.070 s
% 0.21/0.48  % (6381)------------------------------
% 0.21/0.48  % (6381)------------------------------
% 0.21/0.48  % (6379)Success in time 0.126 s
%------------------------------------------------------------------------------
