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
% DateTime   : Thu Dec  3 13:16:36 EST 2020

% Result     : Theorem 1.87s
% Output     : Refutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 679 expanded)
%              Number of leaves         :   13 ( 162 expanded)
%              Depth                    :   36
%              Number of atoms          :  333 (1891 expanded)
%              Number of equality atoms :   28 ( 179 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1095,plain,(
    $false ),
    inference(subsumption_resolution,[],[f763,f35])).

fof(f35,plain,(
    ~ r2_hidden(k3_tarski(sK0),sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ~ r2_hidden(k3_tarski(X0),X0)
      & v2_yellow_0(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ~ r2_hidden(k3_tarski(X0),X0)
      & v2_yellow_0(k2_yellow_1(X0))
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ( v2_yellow_0(k2_yellow_1(X0))
         => r2_hidden(k3_tarski(X0),X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v2_yellow_0(k2_yellow_1(X0))
       => r2_hidden(k3_tarski(X0),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow_1)).

fof(f763,plain,(
    r2_hidden(k3_tarski(sK0),sK0) ),
    inference(backward_demodulation,[],[f77,f761])).

fof(f761,plain,(
    k3_tarski(sK0) = sK1(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f760,f33])).

fof(f33,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f760,plain,
    ( k3_tarski(sK0) = sK1(k2_yellow_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f759,f40])).

fof(f40,plain,(
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
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_orders_2(k2_yellow_1(X0))
        & ~ v2_struct_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).

fof(f759,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | k3_tarski(sK0) = sK1(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f757,f77])).

fof(f757,plain,
    ( k3_tarski(sK0) = sK1(k2_yellow_1(sK0))
    | ~ r2_hidden(sK1(k2_yellow_1(sK0)),sK0)
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(duplicate_literal_removal,[],[f739])).

fof(f739,plain,
    ( k3_tarski(sK0) = sK1(k2_yellow_1(sK0))
    | ~ r2_hidden(sK1(k2_yellow_1(sK0)),sK0)
    | v2_struct_0(k2_yellow_1(sK0))
    | v2_struct_0(k2_yellow_1(sK0))
    | k3_tarski(sK0) = sK1(k2_yellow_1(sK0))
    | ~ r2_hidden(sK1(k2_yellow_1(sK0)),sK0) ),
    inference(resolution,[],[f737,f729])).

fof(f729,plain,(
    ! [X9] :
      ( r2_hidden(sK4(sK0,X9),sK1(k2_yellow_1(sK0)))
      | v2_struct_0(k2_yellow_1(sK0))
      | k3_tarski(sK0) = X9
      | ~ r2_hidden(X9,sK0) ) ),
    inference(subsumption_resolution,[],[f728,f590])).

fof(f590,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | v2_struct_0(k2_yellow_1(sK0))
      | r2_hidden(X1,sK1(k2_yellow_1(sK0)))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f589,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f589,plain,(
    ! [X0] :
      ( r1_tarski(X0,sK1(k2_yellow_1(sK0)))
      | ~ r2_hidden(X0,sK0)
      | v2_struct_0(k2_yellow_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f588,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f588,plain,(
    ! [X0] :
      ( v2_struct_0(k2_yellow_1(sK0))
      | ~ r2_hidden(X0,sK0)
      | ~ m1_subset_1(X0,sK0)
      | r1_tarski(X0,sK1(k2_yellow_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f587,f75])).

fof(f75,plain,(
    m1_subset_1(sK1(k2_yellow_1(sK0)),sK0) ),
    inference(forward_demodulation,[],[f74,f38])).

fof(f38,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0)
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f74,plain,(
    m1_subset_1(sK1(k2_yellow_1(sK0)),u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f73,f37])).

fof(f37,plain,(
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

fof(f73,plain,
    ( m1_subset_1(sK1(k2_yellow_1(sK0)),u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0)) ),
    inference(resolution,[],[f43,f34])).

fof(f34,plain,(
    v2_yellow_0(k2_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v2_yellow_0(X0)
      | m1_subset_1(sK1(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_yellow_0(X0)
      <=> ? [X1] :
            ( r2_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_yellow_0(X0)
      <=> ? [X1] :
            ( r2_lattice3(X0,u1_struct_0(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_0)).

fof(f587,plain,(
    ! [X0] :
      ( v2_struct_0(k2_yellow_1(sK0))
      | ~ r2_hidden(X0,sK0)
      | ~ m1_subset_1(X0,sK0)
      | r1_tarski(X0,sK1(k2_yellow_1(sK0)))
      | ~ m1_subset_1(sK1(k2_yellow_1(sK0)),sK0) ) ),
    inference(subsumption_resolution,[],[f586,f33])).

fof(f586,plain,(
    ! [X0] :
      ( v2_struct_0(k2_yellow_1(sK0))
      | ~ r2_hidden(X0,sK0)
      | ~ m1_subset_1(X0,sK0)
      | v1_xboole_0(sK0)
      | r1_tarski(X0,sK1(k2_yellow_1(sK0)))
      | ~ m1_subset_1(sK1(k2_yellow_1(sK0)),sK0) ) ),
    inference(resolution,[],[f582,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0) ) ),
    inference(forward_demodulation,[],[f66,f38])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    inference(forward_demodulation,[],[f42,f38])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | r1_tarski(X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f582,plain,(
    ! [X1] :
      ( r3_orders_2(k2_yellow_1(sK0),X1,sK1(k2_yellow_1(sK0)))
      | v2_struct_0(k2_yellow_1(sK0))
      | ~ r2_hidden(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f581,f75])).

fof(f581,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK1(k2_yellow_1(sK0)),sK0)
      | ~ r2_hidden(X1,sK0)
      | v2_struct_0(k2_yellow_1(sK0))
      | r3_orders_2(k2_yellow_1(sK0),X1,sK1(k2_yellow_1(sK0))) ) ),
    inference(forward_demodulation,[],[f580,f38])).

fof(f580,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ m1_subset_1(sK1(k2_yellow_1(sK0)),u1_struct_0(k2_yellow_1(sK0)))
      | v2_struct_0(k2_yellow_1(sK0))
      | r3_orders_2(k2_yellow_1(sK0),X1,sK1(k2_yellow_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f579,f50])).

fof(f579,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,sK0)
      | ~ r2_hidden(X1,sK0)
      | ~ m1_subset_1(sK1(k2_yellow_1(sK0)),u1_struct_0(k2_yellow_1(sK0)))
      | v2_struct_0(k2_yellow_1(sK0))
      | r3_orders_2(k2_yellow_1(sK0),X1,sK1(k2_yellow_1(sK0))) ) ),
    inference(forward_demodulation,[],[f578,f38])).

fof(f578,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(sK1(k2_yellow_1(sK0)),u1_struct_0(k2_yellow_1(sK0)))
      | v2_struct_0(k2_yellow_1(sK0))
      | r3_orders_2(k2_yellow_1(sK0),X1,sK1(k2_yellow_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f577,f37])).

fof(f577,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ l1_orders_2(k2_yellow_1(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(sK1(k2_yellow_1(sK0)),u1_struct_0(k2_yellow_1(sK0)))
      | v2_struct_0(k2_yellow_1(sK0))
      | r3_orders_2(k2_yellow_1(sK0),X1,sK1(k2_yellow_1(sK0))) ) ),
    inference(subsumption_resolution,[],[f572,f36])).

fof(f36,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v4_orders_2(k2_yellow_1(X0))
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

fof(f572,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ v3_orders_2(k2_yellow_1(sK0))
      | ~ l1_orders_2(k2_yellow_1(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0)))
      | ~ m1_subset_1(sK1(k2_yellow_1(sK0)),u1_struct_0(k2_yellow_1(sK0)))
      | v2_struct_0(k2_yellow_1(sK0))
      | r3_orders_2(k2_yellow_1(sK0),X1,sK1(k2_yellow_1(sK0))) ) ),
    inference(resolution,[],[f570,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r3_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f570,plain,(
    ! [X0] :
      ( r1_orders_2(k2_yellow_1(sK0),X0,sK1(k2_yellow_1(sK0)))
      | ~ r2_hidden(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f569,f50])).

fof(f569,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r1_orders_2(k2_yellow_1(sK0),X0,sK1(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f568,f75])).

fof(f568,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1(k2_yellow_1(sK0)),sK0)
      | ~ r2_hidden(X0,sK0)
      | r1_orders_2(k2_yellow_1(sK0),X0,sK1(k2_yellow_1(sK0)))
      | ~ m1_subset_1(X0,sK0) ) ),
    inference(resolution,[],[f181,f81])).

fof(f81,plain,(
    r2_lattice3(k2_yellow_1(sK0),sK0,sK1(k2_yellow_1(sK0))) ),
    inference(forward_demodulation,[],[f80,f38])).

fof(f80,plain,(
    r2_lattice3(k2_yellow_1(sK0),u1_struct_0(k2_yellow_1(sK0)),sK1(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f79,f37])).

fof(f79,plain,
    ( r2_lattice3(k2_yellow_1(sK0),u1_struct_0(k2_yellow_1(sK0)),sK1(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0)) ),
    inference(resolution,[],[f44,f34])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v2_yellow_0(X0)
      | r2_lattice3(X0,u1_struct_0(X0),sK1(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f181,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_lattice3(k2_yellow_1(X1),X3,X0)
      | ~ m1_subset_1(X0,X1)
      | ~ r2_hidden(X2,X3)
      | r1_orders_2(k2_yellow_1(X1),X2,X0)
      | ~ m1_subset_1(X2,X1) ) ),
    inference(forward_demodulation,[],[f180,f38])).

fof(f180,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
      | ~ r2_hidden(X2,X3)
      | r1_orders_2(k2_yellow_1(X1),X2,X0)
      | ~ r2_lattice3(k2_yellow_1(X1),X3,X0) ) ),
    inference(forward_demodulation,[],[f179,f38])).

fof(f179,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1)))
      | ~ r2_hidden(X2,X3)
      | r1_orders_2(k2_yellow_1(X1),X2,X0)
      | ~ r2_lattice3(k2_yellow_1(X1),X3,X0) ) ),
    inference(resolution,[],[f46,f37])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X3,X2)
      | ~ r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

fof(f728,plain,(
    ! [X9] :
      ( r2_hidden(sK4(sK0,X9),sK1(k2_yellow_1(sK0)))
      | v2_struct_0(k2_yellow_1(sK0))
      | k3_tarski(sK0) = X9
      | ~ r2_hidden(X9,sK0)
      | r2_hidden(sK4(sK0,X9),X9) ) ),
    inference(duplicate_literal_removal,[],[f719])).

fof(f719,plain,(
    ! [X9] :
      ( r2_hidden(sK4(sK0,X9),sK1(k2_yellow_1(sK0)))
      | v2_struct_0(k2_yellow_1(sK0))
      | k3_tarski(sK0) = X9
      | ~ r2_hidden(X9,sK0)
      | r2_hidden(sK4(sK0,X9),X9)
      | k3_tarski(sK0) = X9 ) ),
    inference(resolution,[],[f605,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),sK6(X0,X1))
      | r2_hidden(sK4(X0,X1),X1)
      | k3_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(f605,plain,(
    ! [X21,X20] :
      ( ~ r2_hidden(X20,sK6(sK0,X21))
      | r2_hidden(X20,sK1(k2_yellow_1(sK0)))
      | v2_struct_0(k2_yellow_1(sK0))
      | k3_tarski(sK0) = X21
      | ~ r2_hidden(X21,sK0) ) ),
    inference(resolution,[],[f590,f191])).

fof(f191,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X1,X0),X1)
      | k3_tarski(X1) = X0
      | ~ r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f182])).

fof(f182,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k3_tarski(X1) = X0
      | r2_hidden(sK6(X1,X0),X1)
      | r2_hidden(sK6(X1,X0),X1)
      | k3_tarski(X1) = X0 ) ),
    inference(resolution,[],[f178,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r2_hidden(sK4(X0,X1),X1)
      | k3_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f178,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X1,X2),X0)
      | ~ r2_hidden(X0,X1)
      | k3_tarski(X1) = X2
      | r2_hidden(sK6(X1,X2),X1) ) ),
    inference(duplicate_literal_removal,[],[f174])).

fof(f174,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(sK4(X1,X2),X0)
      | k3_tarski(X1) = X2
      | r2_hidden(sK6(X1,X2),X1)
      | k3_tarski(X1) = X2 ) ),
    inference(resolution,[],[f55,f57])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(sK4(X0,X1),X3)
      | k3_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f737,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(sK0,sK1(k2_yellow_1(sK0))),X0)
      | k3_tarski(sK0) = sK1(k2_yellow_1(sK0))
      | ~ r2_hidden(X0,sK0)
      | v2_struct_0(k2_yellow_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f736,f77])).

fof(f736,plain,(
    ! [X0] :
      ( v2_struct_0(k2_yellow_1(sK0))
      | k3_tarski(sK0) = sK1(k2_yellow_1(sK0))
      | ~ r2_hidden(sK1(k2_yellow_1(sK0)),sK0)
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(sK4(sK0,sK1(k2_yellow_1(sK0))),X0) ) ),
    inference(duplicate_literal_removal,[],[f730])).

fof(f730,plain,(
    ! [X0] :
      ( v2_struct_0(k2_yellow_1(sK0))
      | k3_tarski(sK0) = sK1(k2_yellow_1(sK0))
      | ~ r2_hidden(sK1(k2_yellow_1(sK0)),sK0)
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(sK4(sK0,sK1(k2_yellow_1(sK0))),X0)
      | k3_tarski(sK0) = sK1(k2_yellow_1(sK0)) ) ),
    inference(resolution,[],[f729,f55])).

fof(f77,plain,(
    r2_hidden(sK1(k2_yellow_1(sK0)),sK0) ),
    inference(subsumption_resolution,[],[f76,f33])).

fof(f76,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(sK1(k2_yellow_1(sK0)),sK0) ),
    inference(resolution,[],[f75,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:54:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.49  % (17520)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.49  % (17512)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.49  % (17504)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (17509)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.50  % (17498)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (17525)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.50  % (17502)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (17500)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (17499)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (17514)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (17526)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (17505)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (17501)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (17510)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (17516)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (17517)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (17515)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (17518)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (17513)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (17507)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (17506)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (17518)Refutation not found, incomplete strategy% (17518)------------------------------
% 0.21/0.53  % (17518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (17518)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (17518)Memory used [KB]: 10746
% 0.21/0.53  % (17518)Time elapsed: 0.134 s
% 0.21/0.53  % (17518)------------------------------
% 0.21/0.53  % (17518)------------------------------
% 0.21/0.53  % (17521)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (17503)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (17524)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (17523)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (17524)Refutation not found, incomplete strategy% (17524)------------------------------
% 0.21/0.53  % (17524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (17524)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (17524)Memory used [KB]: 10746
% 0.21/0.53  % (17524)Time elapsed: 0.130 s
% 0.21/0.53  % (17524)------------------------------
% 0.21/0.53  % (17524)------------------------------
% 0.21/0.53  % (17508)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (17508)Refutation not found, incomplete strategy% (17508)------------------------------
% 0.21/0.54  % (17508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (17508)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (17508)Memory used [KB]: 10618
% 0.21/0.54  % (17508)Time elapsed: 0.140 s
% 0.21/0.54  % (17508)------------------------------
% 0.21/0.54  % (17508)------------------------------
% 0.21/0.54  % (17519)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (17511)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (17522)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.56  % (17527)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.56  % (17519)Refutation not found, incomplete strategy% (17519)------------------------------
% 0.21/0.56  % (17519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (17519)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (17519)Memory used [KB]: 1791
% 0.21/0.56  % (17519)Time elapsed: 0.170 s
% 0.21/0.56  % (17519)------------------------------
% 0.21/0.56  % (17519)------------------------------
% 1.87/0.60  % (17504)Refutation found. Thanks to Tanya!
% 1.87/0.60  % SZS status Theorem for theBenchmark
% 1.87/0.60  % SZS output start Proof for theBenchmark
% 1.87/0.60  fof(f1095,plain,(
% 1.87/0.60    $false),
% 1.87/0.60    inference(subsumption_resolution,[],[f763,f35])).
% 1.87/0.60  fof(f35,plain,(
% 1.87/0.60    ~r2_hidden(k3_tarski(sK0),sK0)),
% 1.87/0.60    inference(cnf_transformation,[],[f21])).
% 1.87/0.60  fof(f21,plain,(
% 1.87/0.60    ? [X0] : (~r2_hidden(k3_tarski(X0),X0) & v2_yellow_0(k2_yellow_1(X0)) & ~v1_xboole_0(X0))),
% 1.87/0.60    inference(flattening,[],[f20])).
% 1.87/0.60  fof(f20,plain,(
% 1.87/0.60    ? [X0] : ((~r2_hidden(k3_tarski(X0),X0) & v2_yellow_0(k2_yellow_1(X0))) & ~v1_xboole_0(X0))),
% 1.87/0.60    inference(ennf_transformation,[],[f14])).
% 1.87/0.60  fof(f14,negated_conjecture,(
% 1.87/0.60    ~! [X0] : (~v1_xboole_0(X0) => (v2_yellow_0(k2_yellow_1(X0)) => r2_hidden(k3_tarski(X0),X0)))),
% 1.87/0.60    inference(negated_conjecture,[],[f13])).
% 1.87/0.60  fof(f13,conjecture,(
% 1.87/0.60    ! [X0] : (~v1_xboole_0(X0) => (v2_yellow_0(k2_yellow_1(X0)) => r2_hidden(k3_tarski(X0),X0)))),
% 1.87/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow_1)).
% 1.87/0.60  fof(f763,plain,(
% 1.87/0.60    r2_hidden(k3_tarski(sK0),sK0)),
% 1.87/0.60    inference(backward_demodulation,[],[f77,f761])).
% 1.87/0.60  fof(f761,plain,(
% 1.87/0.60    k3_tarski(sK0) = sK1(k2_yellow_1(sK0))),
% 1.87/0.60    inference(subsumption_resolution,[],[f760,f33])).
% 1.87/0.60  fof(f33,plain,(
% 1.87/0.60    ~v1_xboole_0(sK0)),
% 1.87/0.60    inference(cnf_transformation,[],[f21])).
% 1.87/0.60  fof(f760,plain,(
% 1.87/0.60    k3_tarski(sK0) = sK1(k2_yellow_1(sK0)) | v1_xboole_0(sK0)),
% 1.87/0.60    inference(resolution,[],[f759,f40])).
% 1.87/0.60  fof(f40,plain,(
% 1.87/0.60    ( ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 1.87/0.60    inference(cnf_transformation,[],[f22])).
% 1.87/0.60  fof(f22,plain,(
% 1.87/0.60    ! [X0] : (~v2_struct_0(k2_yellow_1(X0)) | v1_xboole_0(X0))),
% 1.87/0.60    inference(ennf_transformation,[],[f17])).
% 1.87/0.60  fof(f17,plain,(
% 1.87/0.60    ! [X0] : (~v1_xboole_0(X0) => ~v2_struct_0(k2_yellow_1(X0)))),
% 1.87/0.60    inference(pure_predicate_removal,[],[f10])).
% 1.87/0.60  fof(f10,axiom,(
% 1.87/0.60    ! [X0] : (~v1_xboole_0(X0) => (v1_orders_2(k2_yellow_1(X0)) & ~v2_struct_0(k2_yellow_1(X0))))),
% 1.87/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).
% 1.87/0.60  fof(f759,plain,(
% 1.87/0.60    v2_struct_0(k2_yellow_1(sK0)) | k3_tarski(sK0) = sK1(k2_yellow_1(sK0))),
% 1.87/0.60    inference(subsumption_resolution,[],[f757,f77])).
% 1.87/0.60  fof(f757,plain,(
% 1.87/0.60    k3_tarski(sK0) = sK1(k2_yellow_1(sK0)) | ~r2_hidden(sK1(k2_yellow_1(sK0)),sK0) | v2_struct_0(k2_yellow_1(sK0))),
% 1.87/0.60    inference(duplicate_literal_removal,[],[f739])).
% 1.87/0.60  fof(f739,plain,(
% 1.87/0.60    k3_tarski(sK0) = sK1(k2_yellow_1(sK0)) | ~r2_hidden(sK1(k2_yellow_1(sK0)),sK0) | v2_struct_0(k2_yellow_1(sK0)) | v2_struct_0(k2_yellow_1(sK0)) | k3_tarski(sK0) = sK1(k2_yellow_1(sK0)) | ~r2_hidden(sK1(k2_yellow_1(sK0)),sK0)),
% 1.87/0.60    inference(resolution,[],[f737,f729])).
% 1.87/0.60  fof(f729,plain,(
% 1.87/0.60    ( ! [X9] : (r2_hidden(sK4(sK0,X9),sK1(k2_yellow_1(sK0))) | v2_struct_0(k2_yellow_1(sK0)) | k3_tarski(sK0) = X9 | ~r2_hidden(X9,sK0)) )),
% 1.87/0.60    inference(subsumption_resolution,[],[f728,f590])).
% 1.87/0.60  fof(f590,plain,(
% 1.87/0.60    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | v2_struct_0(k2_yellow_1(sK0)) | r2_hidden(X1,sK1(k2_yellow_1(sK0))) | ~r2_hidden(X1,X0)) )),
% 1.87/0.60    inference(resolution,[],[f589,f52])).
% 1.87/0.60  fof(f52,plain,(
% 1.87/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.87/0.60    inference(cnf_transformation,[],[f30])).
% 1.87/0.60  fof(f30,plain,(
% 1.87/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.87/0.60    inference(ennf_transformation,[],[f1])).
% 1.87/0.60  fof(f1,axiom,(
% 1.87/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.87/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.87/0.60  fof(f589,plain,(
% 1.87/0.60    ( ! [X0] : (r1_tarski(X0,sK1(k2_yellow_1(sK0))) | ~r2_hidden(X0,sK0) | v2_struct_0(k2_yellow_1(sK0))) )),
% 1.87/0.60    inference(subsumption_resolution,[],[f588,f50])).
% 1.87/0.60  fof(f50,plain,(
% 1.87/0.60    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.87/0.60    inference(cnf_transformation,[],[f27])).
% 1.87/0.60  fof(f27,plain,(
% 1.87/0.60    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.87/0.60    inference(ennf_transformation,[],[f3])).
% 1.87/0.60  fof(f3,axiom,(
% 1.87/0.60    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.87/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.87/0.60  fof(f588,plain,(
% 1.87/0.60    ( ! [X0] : (v2_struct_0(k2_yellow_1(sK0)) | ~r2_hidden(X0,sK0) | ~m1_subset_1(X0,sK0) | r1_tarski(X0,sK1(k2_yellow_1(sK0)))) )),
% 1.87/0.60    inference(subsumption_resolution,[],[f587,f75])).
% 1.87/0.60  fof(f75,plain,(
% 1.87/0.60    m1_subset_1(sK1(k2_yellow_1(sK0)),sK0)),
% 1.87/0.60    inference(forward_demodulation,[],[f74,f38])).
% 1.87/0.60  fof(f38,plain,(
% 1.87/0.60    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 1.87/0.60    inference(cnf_transformation,[],[f11])).
% 1.87/0.60  fof(f11,axiom,(
% 1.87/0.60    ! [X0] : (u1_orders_2(k2_yellow_1(X0)) = k1_yellow_1(X0) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 1.87/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).
% 1.87/0.60  fof(f74,plain,(
% 1.87/0.60    m1_subset_1(sK1(k2_yellow_1(sK0)),u1_struct_0(k2_yellow_1(sK0)))),
% 1.87/0.60    inference(subsumption_resolution,[],[f73,f37])).
% 1.87/0.60  fof(f37,plain,(
% 1.87/0.60    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 1.87/0.60    inference(cnf_transformation,[],[f18])).
% 1.87/0.60  fof(f18,plain,(
% 1.87/0.60    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 1.87/0.60    inference(pure_predicate_removal,[],[f8])).
% 1.87/0.60  fof(f8,axiom,(
% 1.87/0.60    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 1.87/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 1.87/0.60  fof(f73,plain,(
% 1.87/0.60    m1_subset_1(sK1(k2_yellow_1(sK0)),u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0))),
% 1.87/0.60    inference(resolution,[],[f43,f34])).
% 1.87/0.60  fof(f34,plain,(
% 1.87/0.60    v2_yellow_0(k2_yellow_1(sK0))),
% 1.87/0.60    inference(cnf_transformation,[],[f21])).
% 1.87/0.60  fof(f43,plain,(
% 1.87/0.60    ( ! [X0] : (~v2_yellow_0(X0) | m1_subset_1(sK1(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.87/0.60    inference(cnf_transformation,[],[f24])).
% 1.87/0.60  fof(f24,plain,(
% 1.87/0.60    ! [X0] : ((v2_yellow_0(X0) <=> ? [X1] : (r2_lattice3(X0,u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.87/0.60    inference(ennf_transformation,[],[f7])).
% 1.87/0.60  fof(f7,axiom,(
% 1.87/0.60    ! [X0] : (l1_orders_2(X0) => (v2_yellow_0(X0) <=> ? [X1] : (r2_lattice3(X0,u1_struct_0(X0),X1) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 1.87/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_yellow_0)).
% 1.87/0.60  fof(f587,plain,(
% 1.87/0.60    ( ! [X0] : (v2_struct_0(k2_yellow_1(sK0)) | ~r2_hidden(X0,sK0) | ~m1_subset_1(X0,sK0) | r1_tarski(X0,sK1(k2_yellow_1(sK0))) | ~m1_subset_1(sK1(k2_yellow_1(sK0)),sK0)) )),
% 1.87/0.60    inference(subsumption_resolution,[],[f586,f33])).
% 1.87/0.60  fof(f586,plain,(
% 1.87/0.60    ( ! [X0] : (v2_struct_0(k2_yellow_1(sK0)) | ~r2_hidden(X0,sK0) | ~m1_subset_1(X0,sK0) | v1_xboole_0(sK0) | r1_tarski(X0,sK1(k2_yellow_1(sK0))) | ~m1_subset_1(sK1(k2_yellow_1(sK0)),sK0)) )),
% 1.87/0.60    inference(resolution,[],[f582,f67])).
% 1.87/0.60  fof(f67,plain,(
% 1.87/0.60    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0) | r1_tarski(X1,X2) | ~m1_subset_1(X2,X0)) )),
% 1.87/0.60    inference(forward_demodulation,[],[f66,f38])).
% 1.87/0.60  fof(f66,plain,(
% 1.87/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2)) )),
% 1.87/0.60    inference(forward_demodulation,[],[f42,f38])).
% 1.87/0.60  fof(f42,plain,(
% 1.87/0.60    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | r1_tarski(X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2)) )),
% 1.87/0.60    inference(cnf_transformation,[],[f23])).
% 1.87/0.60  fof(f23,plain,(
% 1.87/0.60    ! [X0] : (! [X1] : (! [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) | v1_xboole_0(X0))),
% 1.87/0.60    inference(ennf_transformation,[],[f12])).
% 1.87/0.60  fof(f12,axiom,(
% 1.87/0.60    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 1.87/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).
% 1.87/0.60  fof(f582,plain,(
% 1.87/0.60    ( ! [X1] : (r3_orders_2(k2_yellow_1(sK0),X1,sK1(k2_yellow_1(sK0))) | v2_struct_0(k2_yellow_1(sK0)) | ~r2_hidden(X1,sK0)) )),
% 1.87/0.60    inference(subsumption_resolution,[],[f581,f75])).
% 1.87/0.60  fof(f581,plain,(
% 1.87/0.60    ( ! [X1] : (~m1_subset_1(sK1(k2_yellow_1(sK0)),sK0) | ~r2_hidden(X1,sK0) | v2_struct_0(k2_yellow_1(sK0)) | r3_orders_2(k2_yellow_1(sK0),X1,sK1(k2_yellow_1(sK0)))) )),
% 1.87/0.60    inference(forward_demodulation,[],[f580,f38])).
% 1.87/0.60  fof(f580,plain,(
% 1.87/0.60    ( ! [X1] : (~r2_hidden(X1,sK0) | ~m1_subset_1(sK1(k2_yellow_1(sK0)),u1_struct_0(k2_yellow_1(sK0))) | v2_struct_0(k2_yellow_1(sK0)) | r3_orders_2(k2_yellow_1(sK0),X1,sK1(k2_yellow_1(sK0)))) )),
% 1.87/0.60    inference(subsumption_resolution,[],[f579,f50])).
% 1.87/0.60  fof(f579,plain,(
% 1.87/0.60    ( ! [X1] : (~m1_subset_1(X1,sK0) | ~r2_hidden(X1,sK0) | ~m1_subset_1(sK1(k2_yellow_1(sK0)),u1_struct_0(k2_yellow_1(sK0))) | v2_struct_0(k2_yellow_1(sK0)) | r3_orders_2(k2_yellow_1(sK0),X1,sK1(k2_yellow_1(sK0)))) )),
% 1.87/0.60    inference(forward_demodulation,[],[f578,f38])).
% 1.87/0.60  fof(f578,plain,(
% 1.87/0.60    ( ! [X1] : (~r2_hidden(X1,sK0) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1(k2_yellow_1(sK0)),u1_struct_0(k2_yellow_1(sK0))) | v2_struct_0(k2_yellow_1(sK0)) | r3_orders_2(k2_yellow_1(sK0),X1,sK1(k2_yellow_1(sK0)))) )),
% 1.87/0.60    inference(subsumption_resolution,[],[f577,f37])).
% 1.87/0.60  fof(f577,plain,(
% 1.87/0.60    ( ! [X1] : (~r2_hidden(X1,sK0) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1(k2_yellow_1(sK0)),u1_struct_0(k2_yellow_1(sK0))) | v2_struct_0(k2_yellow_1(sK0)) | r3_orders_2(k2_yellow_1(sK0),X1,sK1(k2_yellow_1(sK0)))) )),
% 1.87/0.60    inference(subsumption_resolution,[],[f572,f36])).
% 1.87/0.60  fof(f36,plain,(
% 1.87/0.60    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 1.87/0.60    inference(cnf_transformation,[],[f19])).
% 1.87/0.60  fof(f19,plain,(
% 1.87/0.60    ! [X0] : v3_orders_2(k2_yellow_1(X0))),
% 1.87/0.60    inference(pure_predicate_removal,[],[f16])).
% 1.87/0.60  fof(f16,plain,(
% 1.87/0.60    ! [X0] : (v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 1.87/0.60    inference(pure_predicate_removal,[],[f15])).
% 1.87/0.60  fof(f15,plain,(
% 1.87/0.60    ! [X0] : (v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 1.87/0.60    inference(pure_predicate_removal,[],[f9])).
% 1.87/0.60  fof(f9,axiom,(
% 1.87/0.60    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 1.87/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).
% 1.87/0.60  fof(f572,plain,(
% 1.87/0.60    ( ! [X1] : (~r2_hidden(X1,sK0) | ~v3_orders_2(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK1(k2_yellow_1(sK0)),u1_struct_0(k2_yellow_1(sK0))) | v2_struct_0(k2_yellow_1(sK0)) | r3_orders_2(k2_yellow_1(sK0),X1,sK1(k2_yellow_1(sK0)))) )),
% 1.87/0.60    inference(resolution,[],[f570,f61])).
% 1.87/0.60  fof(f61,plain,(
% 1.87/0.60    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | r3_orders_2(X0,X1,X2)) )),
% 1.87/0.60    inference(cnf_transformation,[],[f32])).
% 1.87/0.60  fof(f32,plain,(
% 1.87/0.60    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.87/0.60    inference(flattening,[],[f31])).
% 1.87/0.60  fof(f31,plain,(
% 1.87/0.60    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.87/0.60    inference(ennf_transformation,[],[f5])).
% 1.87/0.60  fof(f5,axiom,(
% 1.87/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 1.87/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 1.87/0.60  fof(f570,plain,(
% 1.87/0.60    ( ! [X0] : (r1_orders_2(k2_yellow_1(sK0),X0,sK1(k2_yellow_1(sK0))) | ~r2_hidden(X0,sK0)) )),
% 1.87/0.60    inference(subsumption_resolution,[],[f569,f50])).
% 1.87/0.60  fof(f569,plain,(
% 1.87/0.60    ( ! [X0] : (~r2_hidden(X0,sK0) | r1_orders_2(k2_yellow_1(sK0),X0,sK1(k2_yellow_1(sK0))) | ~m1_subset_1(X0,sK0)) )),
% 1.87/0.60    inference(subsumption_resolution,[],[f568,f75])).
% 1.87/0.60  fof(f568,plain,(
% 1.87/0.60    ( ! [X0] : (~m1_subset_1(sK1(k2_yellow_1(sK0)),sK0) | ~r2_hidden(X0,sK0) | r1_orders_2(k2_yellow_1(sK0),X0,sK1(k2_yellow_1(sK0))) | ~m1_subset_1(X0,sK0)) )),
% 1.87/0.60    inference(resolution,[],[f181,f81])).
% 1.87/0.60  fof(f81,plain,(
% 1.87/0.60    r2_lattice3(k2_yellow_1(sK0),sK0,sK1(k2_yellow_1(sK0)))),
% 1.87/0.60    inference(forward_demodulation,[],[f80,f38])).
% 1.87/0.60  fof(f80,plain,(
% 1.87/0.60    r2_lattice3(k2_yellow_1(sK0),u1_struct_0(k2_yellow_1(sK0)),sK1(k2_yellow_1(sK0)))),
% 1.87/0.60    inference(subsumption_resolution,[],[f79,f37])).
% 1.87/0.60  fof(f79,plain,(
% 1.87/0.60    r2_lattice3(k2_yellow_1(sK0),u1_struct_0(k2_yellow_1(sK0)),sK1(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0))),
% 1.87/0.60    inference(resolution,[],[f44,f34])).
% 1.87/0.60  fof(f44,plain,(
% 1.87/0.60    ( ! [X0] : (~v2_yellow_0(X0) | r2_lattice3(X0,u1_struct_0(X0),sK1(X0)) | ~l1_orders_2(X0)) )),
% 1.87/0.60    inference(cnf_transformation,[],[f24])).
% 1.87/0.60  fof(f181,plain,(
% 1.87/0.60    ( ! [X2,X0,X3,X1] : (~r2_lattice3(k2_yellow_1(X1),X3,X0) | ~m1_subset_1(X0,X1) | ~r2_hidden(X2,X3) | r1_orders_2(k2_yellow_1(X1),X2,X0) | ~m1_subset_1(X2,X1)) )),
% 1.87/0.60    inference(forward_demodulation,[],[f180,f38])).
% 1.87/0.60  fof(f180,plain,(
% 1.87/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,X1) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) | ~r2_hidden(X2,X3) | r1_orders_2(k2_yellow_1(X1),X2,X0) | ~r2_lattice3(k2_yellow_1(X1),X3,X0)) )),
% 1.87/0.60    inference(forward_demodulation,[],[f179,f38])).
% 1.87/0.60  fof(f179,plain,(
% 1.87/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(k2_yellow_1(X1))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X1))) | ~r2_hidden(X2,X3) | r1_orders_2(k2_yellow_1(X1),X2,X0) | ~r2_lattice3(k2_yellow_1(X1),X3,X0)) )),
% 1.87/0.60    inference(resolution,[],[f46,f37])).
% 1.87/0.60  fof(f46,plain,(
% 1.87/0.60    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X1) | r1_orders_2(X0,X3,X2) | ~r2_lattice3(X0,X1,X2)) )),
% 1.87/0.60    inference(cnf_transformation,[],[f26])).
% 1.87/0.60  fof(f26,plain,(
% 1.87/0.60    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.87/0.60    inference(flattening,[],[f25])).
% 1.87/0.60  fof(f25,plain,(
% 1.87/0.60    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.87/0.60    inference(ennf_transformation,[],[f6])).
% 1.87/0.60  fof(f6,axiom,(
% 1.87/0.60    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 1.87/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).
% 1.87/0.60  fof(f728,plain,(
% 1.87/0.60    ( ! [X9] : (r2_hidden(sK4(sK0,X9),sK1(k2_yellow_1(sK0))) | v2_struct_0(k2_yellow_1(sK0)) | k3_tarski(sK0) = X9 | ~r2_hidden(X9,sK0) | r2_hidden(sK4(sK0,X9),X9)) )),
% 1.87/0.60    inference(duplicate_literal_removal,[],[f719])).
% 1.87/0.60  fof(f719,plain,(
% 1.87/0.60    ( ! [X9] : (r2_hidden(sK4(sK0,X9),sK1(k2_yellow_1(sK0))) | v2_struct_0(k2_yellow_1(sK0)) | k3_tarski(sK0) = X9 | ~r2_hidden(X9,sK0) | r2_hidden(sK4(sK0,X9),X9) | k3_tarski(sK0) = X9) )),
% 1.87/0.60    inference(resolution,[],[f605,f56])).
% 1.87/0.60  fof(f56,plain,(
% 1.87/0.60    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),sK6(X0,X1)) | r2_hidden(sK4(X0,X1),X1) | k3_tarski(X0) = X1) )),
% 1.87/0.60    inference(cnf_transformation,[],[f2])).
% 1.87/0.60  fof(f2,axiom,(
% 1.87/0.60    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 1.87/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).
% 1.87/0.60  fof(f605,plain,(
% 1.87/0.60    ( ! [X21,X20] : (~r2_hidden(X20,sK6(sK0,X21)) | r2_hidden(X20,sK1(k2_yellow_1(sK0))) | v2_struct_0(k2_yellow_1(sK0)) | k3_tarski(sK0) = X21 | ~r2_hidden(X21,sK0)) )),
% 1.87/0.60    inference(resolution,[],[f590,f191])).
% 1.87/0.60  fof(f191,plain,(
% 1.87/0.60    ( ! [X0,X1] : (r2_hidden(sK6(X1,X0),X1) | k3_tarski(X1) = X0 | ~r2_hidden(X0,X1)) )),
% 1.87/0.60    inference(duplicate_literal_removal,[],[f182])).
% 1.87/0.60  fof(f182,plain,(
% 1.87/0.60    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k3_tarski(X1) = X0 | r2_hidden(sK6(X1,X0),X1) | r2_hidden(sK6(X1,X0),X1) | k3_tarski(X1) = X0) )),
% 1.87/0.60    inference(resolution,[],[f178,f57])).
% 1.87/0.60  fof(f57,plain,(
% 1.87/0.60    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1) | k3_tarski(X0) = X1) )),
% 1.87/0.60    inference(cnf_transformation,[],[f2])).
% 1.87/0.60  fof(f178,plain,(
% 1.87/0.60    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X1,X2),X0) | ~r2_hidden(X0,X1) | k3_tarski(X1) = X2 | r2_hidden(sK6(X1,X2),X1)) )),
% 1.87/0.60    inference(duplicate_literal_removal,[],[f174])).
% 1.87/0.60  fof(f174,plain,(
% 1.87/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(sK4(X1,X2),X0) | k3_tarski(X1) = X2 | r2_hidden(sK6(X1,X2),X1) | k3_tarski(X1) = X2) )),
% 1.87/0.60    inference(resolution,[],[f55,f57])).
% 1.87/0.60  fof(f55,plain,(
% 1.87/0.60    ( ! [X0,X3,X1] : (~r2_hidden(sK4(X0,X1),X1) | ~r2_hidden(X3,X0) | ~r2_hidden(sK4(X0,X1),X3) | k3_tarski(X0) = X1) )),
% 1.87/0.60    inference(cnf_transformation,[],[f2])).
% 1.87/0.60  fof(f737,plain,(
% 1.87/0.60    ( ! [X0] : (~r2_hidden(sK4(sK0,sK1(k2_yellow_1(sK0))),X0) | k3_tarski(sK0) = sK1(k2_yellow_1(sK0)) | ~r2_hidden(X0,sK0) | v2_struct_0(k2_yellow_1(sK0))) )),
% 1.87/0.60    inference(subsumption_resolution,[],[f736,f77])).
% 1.87/0.60  fof(f736,plain,(
% 1.87/0.60    ( ! [X0] : (v2_struct_0(k2_yellow_1(sK0)) | k3_tarski(sK0) = sK1(k2_yellow_1(sK0)) | ~r2_hidden(sK1(k2_yellow_1(sK0)),sK0) | ~r2_hidden(X0,sK0) | ~r2_hidden(sK4(sK0,sK1(k2_yellow_1(sK0))),X0)) )),
% 1.87/0.60    inference(duplicate_literal_removal,[],[f730])).
% 1.87/0.60  fof(f730,plain,(
% 1.87/0.60    ( ! [X0] : (v2_struct_0(k2_yellow_1(sK0)) | k3_tarski(sK0) = sK1(k2_yellow_1(sK0)) | ~r2_hidden(sK1(k2_yellow_1(sK0)),sK0) | ~r2_hidden(X0,sK0) | ~r2_hidden(sK4(sK0,sK1(k2_yellow_1(sK0))),X0) | k3_tarski(sK0) = sK1(k2_yellow_1(sK0))) )),
% 1.87/0.60    inference(resolution,[],[f729,f55])).
% 1.87/0.60  fof(f77,plain,(
% 1.87/0.60    r2_hidden(sK1(k2_yellow_1(sK0)),sK0)),
% 1.87/0.60    inference(subsumption_resolution,[],[f76,f33])).
% 1.87/0.60  fof(f76,plain,(
% 1.87/0.60    v1_xboole_0(sK0) | r2_hidden(sK1(k2_yellow_1(sK0)),sK0)),
% 1.87/0.60    inference(resolution,[],[f75,f51])).
% 1.87/0.60  fof(f51,plain,(
% 1.87/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.87/0.60    inference(cnf_transformation,[],[f29])).
% 1.87/0.60  fof(f29,plain,(
% 1.87/0.60    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.87/0.60    inference(flattening,[],[f28])).
% 1.87/0.60  fof(f28,plain,(
% 1.87/0.60    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.87/0.60    inference(ennf_transformation,[],[f4])).
% 1.87/0.60  fof(f4,axiom,(
% 1.87/0.60    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.87/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.87/0.60  % SZS output end Proof for theBenchmark
% 1.87/0.60  % (17504)------------------------------
% 1.87/0.60  % (17504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.60  % (17504)Termination reason: Refutation
% 1.87/0.60  
% 1.87/0.60  % (17504)Memory used [KB]: 7931
% 1.87/0.60  % (17504)Time elapsed: 0.141 s
% 1.87/0.60  % (17504)------------------------------
% 1.87/0.60  % (17504)------------------------------
% 1.87/0.60  % (17497)Success in time 0.248 s
%------------------------------------------------------------------------------
