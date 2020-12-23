%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 441 expanded)
%              Number of leaves         :   12 ( 110 expanded)
%              Depth                    :   54
%              Number of atoms          :  370 (1369 expanded)
%              Number of equality atoms :   17 ( 159 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f145,plain,(
    $false ),
    inference(subsumption_resolution,[],[f144,f32])).

fof(f32,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <~> r1_tarski(X1,X2) )
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
               => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
                <=> r1_tarski(X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
             => ( r3_orders_2(k2_yellow_1(X0),X1,X2)
              <=> r1_tarski(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

fof(f144,plain,(
    v1_xboole_0(sK0) ),
    inference(forward_demodulation,[],[f143,f37])).

fof(f37,plain,(
    ! [X0] : u1_struct_0(k2_yellow_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k1_yellow_1(X0) = u1_orders_2(k2_yellow_1(X0))
      & u1_struct_0(k2_yellow_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

fof(f143,plain,(
    v1_xboole_0(u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f142,f77])).

fof(f77,plain,(
    ! [X0] : l1_struct_0(k2_yellow_1(X0)) ),
    inference(resolution,[],[f39,f36])).

fof(f36,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : l1_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

fof(f39,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f142,plain,
    ( ~ l1_struct_0(k2_yellow_1(sK0))
    | v1_xboole_0(u1_struct_0(k2_yellow_1(sK0))) ),
    inference(resolution,[],[f141,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v2_struct_0(X0) )
     => v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).

fof(f141,plain,(
    v2_struct_0(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f140,f72])).

fof(f72,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(backward_demodulation,[],[f30,f37])).

fof(f30,plain,(
    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f140,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(forward_demodulation,[],[f139,f37])).

fof(f139,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f138,f73])).

fof(f73,plain,(
    m1_subset_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f31,f37])).

fof(f31,plain,(
    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f138,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(forward_demodulation,[],[f137,f37])).

fof(f137,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f136,f115])).

fof(f115,plain,(
    ~ r3_orders_2(k2_yellow_1(sK0),sK1,sK2) ),
    inference(resolution,[],[f114,f29])).

fof(f29,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r3_orders_2(k2_yellow_1(sK0),sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f114,plain,(
    r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f113,f73])).

fof(f113,plain,
    ( r1_tarski(sK1,sK2)
    | ~ m1_subset_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f112,f32])).

fof(f112,plain,
    ( r1_tarski(sK1,sK2)
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK1,sK0) ),
    inference(resolution,[],[f111,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f111,plain,
    ( ~ r2_hidden(sK1,sK0)
    | r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f110,f72])).

fof(f110,plain,
    ( r1_tarski(sK1,sK2)
    | ~ r2_hidden(sK1,sK0)
    | ~ m1_subset_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f109,f32])).

fof(f109,plain,
    ( r1_tarski(sK1,sK2)
    | ~ r2_hidden(sK1,sK0)
    | v1_xboole_0(sK0)
    | ~ m1_subset_1(sK2,sK0) ),
    inference(resolution,[],[f108,f46])).

fof(f108,plain,
    ( ~ r2_hidden(sK2,sK0)
    | r1_tarski(sK1,sK2)
    | ~ r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f107,f32])).

fof(f107,plain,
    ( v1_xboole_0(sK0)
    | r1_tarski(sK1,sK2)
    | ~ r2_hidden(sK2,sK0)
    | ~ r2_hidden(sK1,sK0) ),
    inference(forward_demodulation,[],[f106,f37])).

fof(f106,plain,
    ( r1_tarski(sK1,sK2)
    | ~ r2_hidden(sK2,sK0)
    | ~ r2_hidden(sK1,sK0)
    | v1_xboole_0(u1_struct_0(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f105,f77])).

fof(f105,plain,
    ( r1_tarski(sK1,sK2)
    | ~ r2_hidden(sK2,sK0)
    | ~ r2_hidden(sK1,sK0)
    | ~ l1_struct_0(k2_yellow_1(sK0))
    | v1_xboole_0(u1_struct_0(k2_yellow_1(sK0))) ),
    inference(resolution,[],[f104,f42])).

fof(f104,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | r1_tarski(sK1,sK2)
    | ~ r2_hidden(sK2,sK0)
    | ~ r2_hidden(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,
    ( r1_tarski(sK1,sK2)
    | v2_struct_0(k2_yellow_1(sK0))
    | ~ r2_hidden(sK2,sK0)
    | r1_tarski(sK1,sK2)
    | ~ r2_hidden(sK1,sK0) ),
    inference(resolution,[],[f100,f75])).

fof(f75,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),u1_orders_2(k2_yellow_1(X0)))
      | ~ r2_hidden(X3,X0)
      | r1_tarski(X2,X3)
      | ~ r2_hidden(X2,X0) ) ),
    inference(subsumption_resolution,[],[f70,f57])).

fof(f57,plain,(
    ! [X0] : v1_relat_1(u1_orders_2(k2_yellow_1(X0))) ),
    inference(definition_unfolding,[],[f33,f56])).

fof(f56,plain,(
    ! [X0] : k1_wellord2(X0) = u1_orders_2(k2_yellow_1(X0)) ),
    inference(definition_unfolding,[],[f34,f38])).

fof(f38,plain,(
    ! [X0] : k1_yellow_1(X0) = u1_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0] : k1_wellord2(X0) = k1_yellow_1(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_wellord2(X0) = k1_yellow_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_yellow_1)).

fof(f33,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f70,plain,(
    ! [X2,X0,X3] :
      ( ~ v1_relat_1(u1_orders_2(k2_yellow_1(X0)))
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X0)
      | r1_tarski(X2,X3)
      | ~ r2_hidden(k4_tarski(X2,X3),u1_orders_2(k2_yellow_1(X0))) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X0)
      | r1_tarski(X2,X3)
      | ~ r2_hidden(k4_tarski(X2,X3),X1)
      | u1_orders_2(k2_yellow_1(X0)) != X1 ) ),
    inference(definition_unfolding,[],[f48,f56])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X0)
      | r1_tarski(X2,X3)
      | ~ r2_hidden(k4_tarski(X2,X3),X1)
      | k1_wellord2(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(f100,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0)))
    | r1_tarski(sK1,sK2)
    | v2_struct_0(k2_yellow_1(sK0)) ),
    inference(subsumption_resolution,[],[f99,f72])).

fof(f99,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | v2_struct_0(k2_yellow_1(sK0))
    | r1_tarski(sK1,sK2)
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0))) ),
    inference(forward_demodulation,[],[f98,f37])).

fof(f98,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | r1_tarski(sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f97,f73])).

fof(f97,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | v2_struct_0(k2_yellow_1(sK0))
    | r1_tarski(sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0))) ),
    inference(forward_demodulation,[],[f96,f37])).

fof(f96,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | r1_tarski(sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f94,f36])).

fof(f94,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | r1_tarski(sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0)) ),
    inference(resolution,[],[f92,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

fof(f92,plain,
    ( r1_orders_2(k2_yellow_1(sK0),sK1,sK2)
    | v2_struct_0(k2_yellow_1(sK0))
    | r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f91,f72])).

fof(f91,plain,
    ( v2_struct_0(k2_yellow_1(sK0))
    | r1_orders_2(k2_yellow_1(sK0),sK1,sK2)
    | ~ m1_subset_1(sK2,sK0)
    | r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f90,f73])).

fof(f90,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | v2_struct_0(k2_yellow_1(sK0))
    | r1_orders_2(k2_yellow_1(sK0),sK1,sK2)
    | ~ m1_subset_1(sK2,sK0)
    | r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f89,f28])).

fof(f28,plain,
    ( r3_orders_2(k2_yellow_1(sK0),sK1,sK2)
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X1,X0)
      | v2_struct_0(k2_yellow_1(X0))
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ m1_subset_1(X2,X0) ) ),
    inference(forward_demodulation,[],[f88,f37])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v2_struct_0(k2_yellow_1(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    inference(forward_demodulation,[],[f87,f37])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(k2_yellow_1(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    inference(subsumption_resolution,[],[f86,f36])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(k2_yellow_1(X0))
      | ~ l1_orders_2(k2_yellow_1(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))
      | r1_orders_2(k2_yellow_1(X0),X1,X2)
      | ~ r3_orders_2(k2_yellow_1(X0),X1,X2) ) ),
    inference(resolution,[],[f55,f35])).

fof(f35,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : v3_orders_2(k2_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v3_orders_2(k2_yellow_1(X0))
      & v1_orders_2(k2_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,plain,(
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

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f136,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | v2_struct_0(k2_yellow_1(sK0))
    | r3_orders_2(k2_yellow_1(sK0),sK1,sK2) ),
    inference(subsumption_resolution,[],[f135,f36])).

fof(f135,plain,
    ( ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | v2_struct_0(k2_yellow_1(sK0))
    | r3_orders_2(k2_yellow_1(sK0),sK1,sK2) ),
    inference(subsumption_resolution,[],[f133,f35])).

fof(f133,plain,
    ( ~ v3_orders_2(k2_yellow_1(sK0))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | v2_struct_0(k2_yellow_1(sK0))
    | r3_orders_2(k2_yellow_1(sK0),sK1,sK2) ),
    inference(resolution,[],[f132,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r3_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f132,plain,(
    r1_orders_2(k2_yellow_1(sK0),sK1,sK2) ),
    inference(subsumption_resolution,[],[f131,f72])).

fof(f131,plain,
    ( ~ m1_subset_1(sK2,sK0)
    | r1_orders_2(k2_yellow_1(sK0),sK1,sK2) ),
    inference(forward_demodulation,[],[f130,f37])).

fof(f130,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | r1_orders_2(k2_yellow_1(sK0),sK1,sK2) ),
    inference(subsumption_resolution,[],[f129,f73])).

fof(f129,plain,
    ( ~ m1_subset_1(sK1,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | r1_orders_2(k2_yellow_1(sK0),sK1,sK2) ),
    inference(forward_demodulation,[],[f128,f37])).

fof(f128,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | r1_orders_2(k2_yellow_1(sK0),sK1,sK2) ),
    inference(subsumption_resolution,[],[f126,f36])).

fof(f126,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))
    | ~ l1_orders_2(k2_yellow_1(sK0))
    | r1_orders_2(k2_yellow_1(sK0),sK1,sK2) ),
    inference(resolution,[],[f124,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f124,plain,(
    r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0))) ),
    inference(subsumption_resolution,[],[f123,f73])).

fof(f123,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f122,f32])).

fof(f122,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0)))
    | ~ m1_subset_1(sK1,sK0) ),
    inference(resolution,[],[f121,f72])).

fof(f121,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,X0)
      | v1_xboole_0(X0)
      | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(X0)))
      | ~ m1_subset_1(sK1,X0) ) ),
    inference(duplicate_literal_removal,[],[f120])).

fof(f120,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(X0)))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK2,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK1,X0) ) ),
    inference(resolution,[],[f118,f46])).

fof(f118,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK1,X0)
      | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(X0)))
      | v1_xboole_0(X0)
      | ~ m1_subset_1(sK2,X0) ) ),
    inference(resolution,[],[f116,f46])).

fof(f116,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,X0)
      | ~ r2_hidden(sK1,X0)
      | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(X0))) ) ),
    inference(resolution,[],[f114,f76])).

fof(f76,plain,(
    ! [X2,X0,X3] :
      ( ~ r1_tarski(X2,X3)
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(k4_tarski(X2,X3),u1_orders_2(k2_yellow_1(X0))) ) ),
    inference(subsumption_resolution,[],[f71,f57])).

fof(f71,plain,(
    ! [X2,X0,X3] :
      ( ~ v1_relat_1(u1_orders_2(k2_yellow_1(X0)))
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X2,X3)
      | r2_hidden(k4_tarski(X2,X3),u1_orders_2(k2_yellow_1(X0))) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X2,X3)
      | r2_hidden(k4_tarski(X2,X3),X1)
      | u1_orders_2(k2_yellow_1(X0)) != X1 ) ),
    inference(definition_unfolding,[],[f47,f56])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X2,X3)
      | r2_hidden(k4_tarski(X2,X3),X1)
      | k1_wellord2(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:03:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (25561)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (25552)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (25544)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (25566)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (25561)Refutation not found, incomplete strategy% (25561)------------------------------
% 0.21/0.52  % (25561)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (25561)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (25561)Memory used [KB]: 10746
% 0.21/0.52  % (25561)Time elapsed: 0.064 s
% 0.21/0.52  % (25561)------------------------------
% 0.21/0.52  % (25561)------------------------------
% 0.21/0.53  % (25557)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (25549)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (25544)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f144,f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ~v1_xboole_0(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : ((r3_orders_2(k2_yellow_1(X0),X1,X2) <~> r1_tarski(X1,X2)) & m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0)))) & m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0)))) & ~v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,negated_conjecture,(
% 0.21/0.53    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.21/0.53    inference(negated_conjecture,[],[f12])).
% 0.21/0.53  fof(f12,conjecture,(
% 0.21/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) => (r3_orders_2(k2_yellow_1(X0),X1,X2) <=> r1_tarski(X1,X2)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    v1_xboole_0(sK0)),
% 0.21/0.53    inference(forward_demodulation,[],[f143,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X0] : (u1_struct_0(k2_yellow_1(X0)) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0] : (k1_yellow_1(X0) = u1_orders_2(k2_yellow_1(X0)) & u1_struct_0(k2_yellow_1(X0)) = X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).
% 0.21/0.53  fof(f143,plain,(
% 0.21/0.53    v1_xboole_0(u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f142,f77])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    ( ! [X0] : (l1_struct_0(k2_yellow_1(X0))) )),
% 0.21/0.53    inference(resolution,[],[f39,f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X0] : (l1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : l1_orders_2(k2_yellow_1(X0))),
% 0.21/0.53    inference(pure_predicate_removal,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : (l1_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.21/0.53  fof(f142,plain,(
% 0.21/0.53    ~l1_struct_0(k2_yellow_1(sK0)) | v1_xboole_0(u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.53    inference(resolution,[],[f141,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0] : (~v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(u1_struct_0(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : ((l1_struct_0(X0) & v2_struct_0(X0)) => v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).
% 0.21/0.53  fof(f141,plain,(
% 0.21/0.53    v2_struct_0(k2_yellow_1(sK0))),
% 0.21/0.53    inference(subsumption_resolution,[],[f140,f72])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    m1_subset_1(sK2,sK0)),
% 0.21/0.53    inference(backward_demodulation,[],[f30,f37])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    ~m1_subset_1(sK2,sK0) | v2_struct_0(k2_yellow_1(sK0))),
% 0.21/0.53    inference(forward_demodulation,[],[f139,f37])).
% 0.21/0.53  fof(f139,plain,(
% 0.21/0.53    ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | v2_struct_0(k2_yellow_1(sK0))),
% 0.21/0.53    inference(subsumption_resolution,[],[f138,f73])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    m1_subset_1(sK1,sK0)),
% 0.21/0.53    inference(backward_demodulation,[],[f31,f37])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    ~m1_subset_1(sK1,sK0) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | v2_struct_0(k2_yellow_1(sK0))),
% 0.21/0.53    inference(forward_demodulation,[],[f137,f37])).
% 0.21/0.53  fof(f137,plain,(
% 0.21/0.53    ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | v2_struct_0(k2_yellow_1(sK0))),
% 0.21/0.53    inference(subsumption_resolution,[],[f136,f115])).
% 0.21/0.53  fof(f115,plain,(
% 0.21/0.53    ~r3_orders_2(k2_yellow_1(sK0),sK1,sK2)),
% 0.21/0.53    inference(resolution,[],[f114,f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ~r1_tarski(sK1,sK2) | ~r3_orders_2(k2_yellow_1(sK0),sK1,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    r1_tarski(sK1,sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f113,f73])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    r1_tarski(sK1,sK2) | ~m1_subset_1(sK1,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f112,f32])).
% 0.21/0.53  fof(f112,plain,(
% 0.21/0.53    r1_tarski(sK1,sK2) | v1_xboole_0(sK0) | ~m1_subset_1(sK1,sK0)),
% 0.21/0.53    inference(resolution,[],[f111,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(X1,X0) | v1_xboole_0(X0) | ~m1_subset_1(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    ~r2_hidden(sK1,sK0) | r1_tarski(sK1,sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f110,f72])).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    r1_tarski(sK1,sK2) | ~r2_hidden(sK1,sK0) | ~m1_subset_1(sK2,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f109,f32])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    r1_tarski(sK1,sK2) | ~r2_hidden(sK1,sK0) | v1_xboole_0(sK0) | ~m1_subset_1(sK2,sK0)),
% 0.21/0.53    inference(resolution,[],[f108,f46])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    ~r2_hidden(sK2,sK0) | r1_tarski(sK1,sK2) | ~r2_hidden(sK1,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f107,f32])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    v1_xboole_0(sK0) | r1_tarski(sK1,sK2) | ~r2_hidden(sK2,sK0) | ~r2_hidden(sK1,sK0)),
% 0.21/0.53    inference(forward_demodulation,[],[f106,f37])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    r1_tarski(sK1,sK2) | ~r2_hidden(sK2,sK0) | ~r2_hidden(sK1,sK0) | v1_xboole_0(u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f105,f77])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    r1_tarski(sK1,sK2) | ~r2_hidden(sK2,sK0) | ~r2_hidden(sK1,sK0) | ~l1_struct_0(k2_yellow_1(sK0)) | v1_xboole_0(u1_struct_0(k2_yellow_1(sK0)))),
% 0.21/0.53    inference(resolution,[],[f104,f42])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    v2_struct_0(k2_yellow_1(sK0)) | r1_tarski(sK1,sK2) | ~r2_hidden(sK2,sK0) | ~r2_hidden(sK1,sK0)),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f101])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    r1_tarski(sK1,sK2) | v2_struct_0(k2_yellow_1(sK0)) | ~r2_hidden(sK2,sK0) | r1_tarski(sK1,sK2) | ~r2_hidden(sK1,sK0)),
% 0.21/0.53    inference(resolution,[],[f100,f75])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),u1_orders_2(k2_yellow_1(X0))) | ~r2_hidden(X3,X0) | r1_tarski(X2,X3) | ~r2_hidden(X2,X0)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f70,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X0] : (v1_relat_1(u1_orders_2(k2_yellow_1(X0)))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f33,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0] : (k1_wellord2(X0) = u1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.53    inference(definition_unfolding,[],[f34,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X0] : (k1_yellow_1(X0) = u1_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f11])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X0] : (k1_wellord2(X0) = k1_yellow_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0] : k1_wellord2(X0) = k1_yellow_1(X0)),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_yellow_1)).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X2,X0,X3] : (~v1_relat_1(u1_orders_2(k2_yellow_1(X0))) | ~r2_hidden(X2,X0) | ~r2_hidden(X3,X0) | r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),u1_orders_2(k2_yellow_1(X0)))) )),
% 0.21/0.53    inference(equality_resolution,[],[f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X1) | ~r2_hidden(X2,X0) | ~r2_hidden(X3,X0) | r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1) | u1_orders_2(k2_yellow_1(X0)) != X1) )),
% 0.21/0.53    inference(definition_unfolding,[],[f48,f56])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X1) | ~r2_hidden(X2,X0) | ~r2_hidden(X3,X0) | r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1) | k1_wellord2(X0) != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0))) | r1_tarski(sK1,sK2) | v2_struct_0(k2_yellow_1(sK0))),
% 0.21/0.53    inference(subsumption_resolution,[],[f99,f72])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    ~m1_subset_1(sK2,sK0) | v2_struct_0(k2_yellow_1(sK0)) | r1_tarski(sK1,sK2) | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0)))),
% 0.21/0.53    inference(forward_demodulation,[],[f98,f37])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    v2_struct_0(k2_yellow_1(sK0)) | r1_tarski(sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f97,f73])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    ~m1_subset_1(sK1,sK0) | v2_struct_0(k2_yellow_1(sK0)) | r1_tarski(sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0)))),
% 0.21/0.53    inference(forward_demodulation,[],[f96,f37])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    v2_struct_0(k2_yellow_1(sK0)) | r1_tarski(sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f94,f36])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    v2_struct_0(k2_yellow_1(sK0)) | r1_tarski(sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0))),
% 0.21/0.53    inference(resolution,[],[f92,f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    r1_orders_2(k2_yellow_1(sK0),sK1,sK2) | v2_struct_0(k2_yellow_1(sK0)) | r1_tarski(sK1,sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f91,f72])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    v2_struct_0(k2_yellow_1(sK0)) | r1_orders_2(k2_yellow_1(sK0),sK1,sK2) | ~m1_subset_1(sK2,sK0) | r1_tarski(sK1,sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f90,f73])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    ~m1_subset_1(sK1,sK0) | v2_struct_0(k2_yellow_1(sK0)) | r1_orders_2(k2_yellow_1(sK0),sK1,sK2) | ~m1_subset_1(sK2,sK0) | r1_tarski(sK1,sK2)),
% 0.21/0.53    inference(resolution,[],[f89,f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    r3_orders_2(k2_yellow_1(sK0),sK1,sK2) | r1_tarski(sK1,sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r3_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X1,X0) | v2_struct_0(k2_yellow_1(X0)) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~m1_subset_1(X2,X0)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f88,f37])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,X0) | v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f87,f37])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v2_struct_0(k2_yellow_1(X0)) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f86,f36])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v2_struct_0(k2_yellow_1(X0)) | ~l1_orders_2(k2_yellow_1(X0)) | ~m1_subset_1(X1,u1_struct_0(k2_yellow_1(X0))) | ~m1_subset_1(X2,u1_struct_0(k2_yellow_1(X0))) | r1_orders_2(k2_yellow_1(X0),X1,X2) | ~r3_orders_2(k2_yellow_1(X0),X1,X2)) )),
% 0.21/0.53    inference(resolution,[],[f55,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X0] : (v3_orders_2(k2_yellow_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : v3_orders_2(k2_yellow_1(X0))),
% 0.21/0.53    inference(pure_predicate_removal,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0] : (v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.53    inference(pure_predicate_removal,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0] : (v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.53    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : (v5_orders_2(k2_yellow_1(X0)) & v4_orders_2(k2_yellow_1(X0)) & v3_orders_2(k2_yellow_1(X0)) & v1_orders_2(k2_yellow_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v3_orders_2(X0) | v2_struct_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.21/0.53  fof(f136,plain,(
% 0.21/0.53    ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | v2_struct_0(k2_yellow_1(sK0)) | r3_orders_2(k2_yellow_1(sK0),sK1,sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f135,f36])).
% 0.21/0.53  fof(f135,plain,(
% 0.21/0.53    ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | v2_struct_0(k2_yellow_1(sK0)) | r3_orders_2(k2_yellow_1(sK0),sK1,sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f133,f35])).
% 0.21/0.53  fof(f133,plain,(
% 0.21/0.53    ~v3_orders_2(k2_yellow_1(sK0)) | ~l1_orders_2(k2_yellow_1(sK0)) | ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | v2_struct_0(k2_yellow_1(sK0)) | r3_orders_2(k2_yellow_1(sK0),sK1,sK2)),
% 0.21/0.53    inference(resolution,[],[f132,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | v2_struct_0(X0) | r3_orders_2(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    r1_orders_2(k2_yellow_1(sK0),sK1,sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f131,f72])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    ~m1_subset_1(sK2,sK0) | r1_orders_2(k2_yellow_1(sK0),sK1,sK2)),
% 0.21/0.53    inference(forward_demodulation,[],[f130,f37])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),sK1,sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f129,f73])).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    ~m1_subset_1(sK1,sK0) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),sK1,sK2)),
% 0.21/0.53    inference(forward_demodulation,[],[f128,f37])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | r1_orders_2(k2_yellow_1(sK0),sK1,sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f126,f36])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    ~m1_subset_1(sK1,u1_struct_0(k2_yellow_1(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k2_yellow_1(sK0))) | ~l1_orders_2(k2_yellow_1(sK0)) | r1_orders_2(k2_yellow_1(sK0),sK1,sK2)),
% 0.21/0.53    inference(resolution,[],[f124,f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0)))),
% 0.21/0.53    inference(subsumption_resolution,[],[f123,f73])).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f122,f32])).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    v1_xboole_0(sK0) | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(sK0))) | ~m1_subset_1(sK1,sK0)),
% 0.21/0.53    inference(resolution,[],[f121,f72])).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(sK2,X0) | v1_xboole_0(X0) | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(X0))) | ~m1_subset_1(sK1,X0)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f120])).
% 0.21/0.53  fof(f120,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(X0))) | v1_xboole_0(X0) | ~m1_subset_1(sK2,X0) | v1_xboole_0(X0) | ~m1_subset_1(sK1,X0)) )),
% 0.21/0.53    inference(resolution,[],[f118,f46])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(sK1,X0) | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(X0))) | v1_xboole_0(X0) | ~m1_subset_1(sK2,X0)) )),
% 0.21/0.53    inference(resolution,[],[f116,f46])).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(sK2,X0) | ~r2_hidden(sK1,X0) | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(k2_yellow_1(X0)))) )),
% 0.21/0.53    inference(resolution,[],[f114,f76])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ( ! [X2,X0,X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0) | r2_hidden(k4_tarski(X2,X3),u1_orders_2(k2_yellow_1(X0)))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f71,f57])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X2,X0,X3] : (~v1_relat_1(u1_orders_2(k2_yellow_1(X0))) | ~r2_hidden(X2,X0) | ~r2_hidden(X3,X0) | ~r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),u1_orders_2(k2_yellow_1(X0)))) )),
% 0.21/0.53    inference(equality_resolution,[],[f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X1) | ~r2_hidden(X2,X0) | ~r2_hidden(X3,X0) | ~r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1) | u1_orders_2(k2_yellow_1(X0)) != X1) )),
% 0.21/0.53    inference(definition_unfolding,[],[f47,f56])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X1) | ~r2_hidden(X2,X0) | ~r2_hidden(X3,X0) | ~r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1) | k1_wellord2(X0) != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (25544)------------------------------
% 0.21/0.53  % (25544)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (25544)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (25544)Memory used [KB]: 6268
% 0.21/0.53  % (25544)Time elapsed: 0.074 s
% 0.21/0.53  % (25544)------------------------------
% 0.21/0.53  % (25544)------------------------------
% 0.21/0.53  % (25537)Success in time 0.174 s
%------------------------------------------------------------------------------
