%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:12 EST 2020

% Result     : Theorem 2.32s
% Output     : Refutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 272 expanded)
%              Number of leaves         :   20 (  77 expanded)
%              Depth                    :   17
%              Number of atoms          :  224 ( 604 expanded)
%              Number of equality atoms :   37 ( 114 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1657,plain,(
    $false ),
    inference(global_subsumption,[],[f47,f1656])).

fof(f1656,plain,(
    r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f1655,f717])).

fof(f717,plain,(
    k3_relat_1(sK0) = k3_tarski(k2_tarski(k2_relat_1(sK0),k1_relat_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f48,f101])).

fof(f101,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k3_tarski(k2_tarski(k2_relat_1(X0),k1_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(backward_demodulation,[],[f88,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f88,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f52,f63])).

fof(f63,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f48,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(f1655,plain,(
    r1_tarski(k3_tarski(k2_tarski(k2_relat_1(sK0),k1_relat_1(sK0))),k3_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f1648,f61])).

fof(f1648,plain,(
    r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK0),k2_relat_1(sK0))),k3_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f1459,f1564,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f86,f63])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f1564,plain,(
    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f1419,f1562,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f1562,plain,(
    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(superposition,[],[f90,f1300])).

fof(f1300,plain,(
    k1_relat_1(sK1) = k3_tarski(k2_tarski(k1_relat_1(sK0),k1_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f1299,f663])).

fof(f663,plain,(
    sK1 = k3_tarski(k2_tarski(sK0,sK1)) ),
    inference(forward_demodulation,[],[f662,f87])).

fof(f87,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f51,f63])).

fof(f51,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f662,plain,(
    k3_tarski(k2_tarski(sK1,k1_xboole_0)) = k3_tarski(k2_tarski(sK0,sK1)) ),
    inference(forward_demodulation,[],[f659,f61])).

fof(f659,plain,(
    k3_tarski(k2_tarski(sK1,k1_xboole_0)) = k3_tarski(k2_tarski(sK1,sK0)) ),
    inference(superposition,[],[f92,f602])).

fof(f602,plain,(
    k1_xboole_0 = k6_subset_1(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f50,f575,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f575,plain,(
    ! [X0] : r1_tarski(k6_subset_1(sK0,sK1),X0) ),
    inference(unit_resulting_resolution,[],[f286,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
      | r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f83,f63,f62])).

fof(f62,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f286,plain,(
    ! [X0] : r1_tarski(sK0,k3_tarski(k2_tarski(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f46,f90,f85])).

fof(f46,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f92,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k6_subset_1(X1,X0))) ),
    inference(definition_unfolding,[],[f64,f63,f62,f63])).

fof(f64,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1299,plain,(
    k1_relat_1(k3_tarski(k2_tarski(sK0,sK1))) = k3_tarski(k2_tarski(k1_relat_1(sK0),k1_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f1298,f61])).

fof(f1298,plain,(
    k3_tarski(k2_tarski(k1_relat_1(sK0),k1_relat_1(sK1))) = k1_relat_1(k3_tarski(k2_tarski(sK1,sK0))) ),
    inference(forward_demodulation,[],[f1288,f61])).

fof(f1288,plain,(
    k1_relat_1(k3_tarski(k2_tarski(sK1,sK0))) = k3_tarski(k2_tarski(k1_relat_1(sK1),k1_relat_1(sK0))) ),
    inference(unit_resulting_resolution,[],[f45,f48,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k1_relat_1(X0),k1_relat_1(X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f53,f63,f63])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).

fof(f45,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f90,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f59,f63])).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1419,plain,(
    r1_tarski(k1_relat_1(sK1),k3_relat_1(sK1)) ),
    inference(superposition,[],[f104,f716])).

fof(f716,plain,(
    k3_relat_1(sK1) = k3_tarski(k2_tarski(k2_relat_1(sK1),k1_relat_1(sK1))) ),
    inference(unit_resulting_resolution,[],[f45,f101])).

fof(f104,plain,(
    ! [X2,X1] : r1_tarski(X1,k3_tarski(k2_tarski(X2,X1))) ),
    inference(superposition,[],[f90,f61])).

fof(f1459,plain,(
    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f1180,f1420,f85])).

fof(f1420,plain,(
    r1_tarski(k2_relat_1(sK1),k3_relat_1(sK1)) ),
    inference(superposition,[],[f90,f716])).

fof(f1180,plain,(
    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f1134,f87])).

fof(f1134,plain,(
    r1_tarski(k2_relat_1(sK0),k3_tarski(k2_tarski(k2_relat_1(sK1),k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f1131,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_tarski(X1,X2)))
      | ~ r1_tarski(k6_subset_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f84,f62,f63])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f1131,plain,(
    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k1_xboole_0) ),
    inference(backward_demodulation,[],[f1024,f1129])).

fof(f1129,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f162,f383,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( sP6(sK5(X0,X1),X0)
      | r2_hidden(sK5(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f383,plain,(
    ! [X0] : ~ sP6(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f162,f74])).

fof(f74,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK7(X0,X2),X2),X0)
      | ~ sP6(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f162,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f131,f49,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f49,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f131,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_relat_1(sK2(k4_tarski(X1,X0)))) ),
    inference(unit_resulting_resolution,[],[f128,f100])).

fof(f100,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k2_relat_1(X0))
      | ~ sP6(X2,X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ sP6(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f128,plain,(
    ! [X0,X1] : sP6(X0,sK2(k4_tarski(X1,X0))) ),
    inference(unit_resulting_resolution,[],[f58,f75])).

fof(f75,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | sP6(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f58,plain,(
    ! [X0] : r2_hidden(X0,sK2(X0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | r2_tarski(X2,X1)
          | ~ r1_tarski(X2,X1) )
      & ! [X3] :
          ( r2_hidden(k1_zfmisc_1(X3),X1)
          | ~ r2_hidden(X3,X1) )
      & ! [X4,X5] :
          ( r2_hidden(X5,X1)
          | ~ r1_tarski(X5,X4)
          | ~ r2_hidden(X4,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | r2_tarski(X2,X1)
          | ~ r1_tarski(X2,X1) )
      & ! [X3] :
          ( r2_hidden(k1_zfmisc_1(X3),X1)
          | ~ r2_hidden(X3,X1) )
      & ! [X4,X5] :
          ( r2_hidden(X5,X1)
          | ~ r1_tarski(X5,X4)
          | ~ r2_hidden(X4,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & ~ r2_tarski(X2,X1)
            & r1_tarski(X2,X1) )
      & ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(k1_zfmisc_1(X3),X1) )
      & ! [X4,X5] :
          ( ( r1_tarski(X5,X4)
            & r2_hidden(X4,X1) )
         => r2_hidden(X5,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(rectify,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & ~ r2_tarski(X2,X1)
            & r1_tarski(X2,X1) )
      & ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(k1_zfmisc_1(X2),X1) )
      & ! [X2,X3] :
          ( ( r1_tarski(X3,X2)
            & r2_hidden(X2,X1) )
         => r2_hidden(X3,X1) )
      & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t136_zfmisc_1)).

fof(f1024,plain,(
    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1018,f602])).

fof(f1018,plain,(
    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f48,f45,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_relat_1)).

fof(f47,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:32:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.52  % (30303)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (30295)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (30319)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (30305)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (30311)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (30299)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (30291)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (30297)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (30296)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (30313)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (30293)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.46/0.55  % (30292)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.46/0.55  % (30318)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.46/0.55  % (30298)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.46/0.56  % (30310)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.46/0.56  % (30302)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.62/0.57  % (30315)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.62/0.57  % (30307)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.62/0.57  % (30316)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.62/0.57  % (30294)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.62/0.57  % (30314)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.62/0.58  % (30306)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.62/0.59  % (30308)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.62/0.59  % (30317)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.62/0.60  % (30312)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.62/0.60  % (30309)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.62/0.60  % (30304)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.62/0.61  % (30320)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.62/0.61  % (30301)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.62/0.61  % (30300)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 2.32/0.69  % (30315)Refutation found. Thanks to Tanya!
% 2.32/0.69  % SZS status Theorem for theBenchmark
% 2.32/0.69  % SZS output start Proof for theBenchmark
% 2.32/0.69  fof(f1657,plain,(
% 2.32/0.69    $false),
% 2.32/0.69    inference(global_subsumption,[],[f47,f1656])).
% 2.32/0.69  fof(f1656,plain,(
% 2.32/0.69    r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 2.32/0.69    inference(forward_demodulation,[],[f1655,f717])).
% 2.32/0.69  fof(f717,plain,(
% 2.32/0.69    k3_relat_1(sK0) = k3_tarski(k2_tarski(k2_relat_1(sK0),k1_relat_1(sK0)))),
% 2.32/0.69    inference(unit_resulting_resolution,[],[f48,f101])).
% 2.32/0.69  fof(f101,plain,(
% 2.32/0.69    ( ! [X0] : (k3_relat_1(X0) = k3_tarski(k2_tarski(k2_relat_1(X0),k1_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 2.32/0.69    inference(backward_demodulation,[],[f88,f61])).
% 2.32/0.69  fof(f61,plain,(
% 2.32/0.69    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.32/0.69    inference(cnf_transformation,[],[f15])).
% 2.32/0.69  fof(f15,axiom,(
% 2.32/0.69    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.32/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.32/0.69  fof(f88,plain,(
% 2.32/0.69    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 2.32/0.69    inference(definition_unfolding,[],[f52,f63])).
% 2.32/0.69  fof(f63,plain,(
% 2.32/0.69    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.32/0.69    inference(cnf_transformation,[],[f16])).
% 2.32/0.69  fof(f16,axiom,(
% 2.32/0.69    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.32/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.32/0.69  fof(f52,plain,(
% 2.32/0.69    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 2.32/0.69    inference(cnf_transformation,[],[f30])).
% 2.32/0.69  fof(f30,plain,(
% 2.32/0.69    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.32/0.69    inference(ennf_transformation,[],[f21])).
% 2.32/0.69  fof(f21,axiom,(
% 2.32/0.69    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 2.32/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 2.32/0.69  fof(f48,plain,(
% 2.32/0.69    v1_relat_1(sK0)),
% 2.32/0.69    inference(cnf_transformation,[],[f29])).
% 2.32/0.69  fof(f29,plain,(
% 2.32/0.69    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.32/0.69    inference(flattening,[],[f28])).
% 2.32/0.69  fof(f28,plain,(
% 2.32/0.69    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 2.32/0.69    inference(ennf_transformation,[],[f25])).
% 2.32/0.69  fof(f25,negated_conjecture,(
% 2.32/0.69    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 2.32/0.69    inference(negated_conjecture,[],[f24])).
% 2.32/0.69  fof(f24,conjecture,(
% 2.32/0.69    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 2.32/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).
% 2.32/0.69  fof(f1655,plain,(
% 2.32/0.69    r1_tarski(k3_tarski(k2_tarski(k2_relat_1(sK0),k1_relat_1(sK0))),k3_relat_1(sK1))),
% 2.32/0.69    inference(forward_demodulation,[],[f1648,f61])).
% 2.32/0.69  fof(f1648,plain,(
% 2.32/0.69    r1_tarski(k3_tarski(k2_tarski(k1_relat_1(sK0),k2_relat_1(sK0))),k3_relat_1(sK1))),
% 2.32/0.69    inference(unit_resulting_resolution,[],[f1459,f1564,f96])).
% 2.32/0.69  fof(f96,plain,(
% 2.32/0.69    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.32/0.69    inference(definition_unfolding,[],[f86,f63])).
% 2.32/0.69  fof(f86,plain,(
% 2.32/0.69    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | r1_tarski(k2_xboole_0(X0,X2),X1)) )),
% 2.32/0.69    inference(cnf_transformation,[],[f44])).
% 2.32/0.69  fof(f44,plain,(
% 2.32/0.69    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 2.32/0.69    inference(flattening,[],[f43])).
% 2.32/0.69  fof(f43,plain,(
% 2.32/0.69    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 2.32/0.69    inference(ennf_transformation,[],[f14])).
% 2.32/0.69  fof(f14,axiom,(
% 2.32/0.69    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 2.32/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 2.32/0.69  fof(f1564,plain,(
% 2.32/0.69    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 2.32/0.69    inference(unit_resulting_resolution,[],[f1419,f1562,f85])).
% 2.32/0.69  fof(f85,plain,(
% 2.32/0.69    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 2.32/0.69    inference(cnf_transformation,[],[f42])).
% 2.32/0.69  fof(f42,plain,(
% 2.32/0.69    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.32/0.69    inference(flattening,[],[f41])).
% 2.32/0.69  fof(f41,plain,(
% 2.32/0.69    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.32/0.69    inference(ennf_transformation,[],[f6])).
% 2.32/0.69  fof(f6,axiom,(
% 2.32/0.69    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.32/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.32/0.69  fof(f1562,plain,(
% 2.32/0.69    r1_tarski(k1_relat_1(sK0),k1_relat_1(sK1))),
% 2.32/0.69    inference(superposition,[],[f90,f1300])).
% 2.32/0.69  fof(f1300,plain,(
% 2.32/0.69    k1_relat_1(sK1) = k3_tarski(k2_tarski(k1_relat_1(sK0),k1_relat_1(sK1)))),
% 2.32/0.69    inference(forward_demodulation,[],[f1299,f663])).
% 2.32/0.69  fof(f663,plain,(
% 2.32/0.69    sK1 = k3_tarski(k2_tarski(sK0,sK1))),
% 2.32/0.69    inference(forward_demodulation,[],[f662,f87])).
% 2.32/0.69  fof(f87,plain,(
% 2.32/0.69    ( ! [X0] : (k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0) )),
% 2.32/0.69    inference(definition_unfolding,[],[f51,f63])).
% 2.32/0.69  fof(f51,plain,(
% 2.32/0.69    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.32/0.69    inference(cnf_transformation,[],[f5])).
% 2.32/0.69  fof(f5,axiom,(
% 2.32/0.69    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.32/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 2.32/0.69  fof(f662,plain,(
% 2.32/0.69    k3_tarski(k2_tarski(sK1,k1_xboole_0)) = k3_tarski(k2_tarski(sK0,sK1))),
% 2.32/0.69    inference(forward_demodulation,[],[f659,f61])).
% 2.32/0.69  fof(f659,plain,(
% 2.32/0.69    k3_tarski(k2_tarski(sK1,k1_xboole_0)) = k3_tarski(k2_tarski(sK1,sK0))),
% 2.32/0.69    inference(superposition,[],[f92,f602])).
% 2.32/0.69  fof(f602,plain,(
% 2.32/0.69    k1_xboole_0 = k6_subset_1(sK0,sK1)),
% 2.32/0.69    inference(unit_resulting_resolution,[],[f50,f575,f70])).
% 2.32/0.69  fof(f70,plain,(
% 2.32/0.69    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 2.32/0.69    inference(cnf_transformation,[],[f3])).
% 2.32/0.69  fof(f3,axiom,(
% 2.32/0.69    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.32/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.32/0.69  fof(f575,plain,(
% 2.32/0.69    ( ! [X0] : (r1_tarski(k6_subset_1(sK0,sK1),X0)) )),
% 2.32/0.69    inference(unit_resulting_resolution,[],[f286,f94])).
% 2.32/0.69  fof(f94,plain,(
% 2.32/0.69    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 2.32/0.69    inference(definition_unfolding,[],[f83,f63,f62])).
% 2.32/0.69  fof(f62,plain,(
% 2.32/0.69    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.32/0.69    inference(cnf_transformation,[],[f19])).
% 2.32/0.69  fof(f19,axiom,(
% 2.32/0.69    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.32/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.32/0.69  fof(f83,plain,(
% 2.32/0.69    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.32/0.69    inference(cnf_transformation,[],[f39])).
% 2.32/0.69  fof(f39,plain,(
% 2.32/0.69    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.32/0.69    inference(ennf_transformation,[],[f10])).
% 2.32/0.69  fof(f10,axiom,(
% 2.32/0.69    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.32/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 2.32/0.69  fof(f286,plain,(
% 2.32/0.69    ( ! [X0] : (r1_tarski(sK0,k3_tarski(k2_tarski(sK1,X0)))) )),
% 2.32/0.69    inference(unit_resulting_resolution,[],[f46,f90,f85])).
% 2.32/0.69  fof(f46,plain,(
% 2.32/0.69    r1_tarski(sK0,sK1)),
% 2.32/0.69    inference(cnf_transformation,[],[f29])).
% 2.32/0.69  fof(f50,plain,(
% 2.32/0.69    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.32/0.69    inference(cnf_transformation,[],[f7])).
% 2.32/0.69  fof(f7,axiom,(
% 2.32/0.69    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.32/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.32/0.69  fof(f92,plain,(
% 2.32/0.69    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X0,k6_subset_1(X1,X0)))) )),
% 2.32/0.69    inference(definition_unfolding,[],[f64,f63,f62,f63])).
% 2.32/0.69  fof(f64,plain,(
% 2.32/0.69    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 2.32/0.69    inference(cnf_transformation,[],[f9])).
% 2.32/0.69  fof(f9,axiom,(
% 2.32/0.69    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 2.32/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.32/0.69  fof(f1299,plain,(
% 2.32/0.69    k1_relat_1(k3_tarski(k2_tarski(sK0,sK1))) = k3_tarski(k2_tarski(k1_relat_1(sK0),k1_relat_1(sK1)))),
% 2.32/0.69    inference(forward_demodulation,[],[f1298,f61])).
% 2.32/0.69  fof(f1298,plain,(
% 2.32/0.69    k3_tarski(k2_tarski(k1_relat_1(sK0),k1_relat_1(sK1))) = k1_relat_1(k3_tarski(k2_tarski(sK1,sK0)))),
% 2.32/0.69    inference(forward_demodulation,[],[f1288,f61])).
% 2.32/0.69  fof(f1288,plain,(
% 2.32/0.69    k1_relat_1(k3_tarski(k2_tarski(sK1,sK0))) = k3_tarski(k2_tarski(k1_relat_1(sK1),k1_relat_1(sK0)))),
% 2.32/0.69    inference(unit_resulting_resolution,[],[f45,f48,f89])).
% 2.32/0.69  fof(f89,plain,(
% 2.32/0.69    ( ! [X0,X1] : (k1_relat_1(k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.32/0.69    inference(definition_unfolding,[],[f53,f63,f63])).
% 2.32/0.69  fof(f53,plain,(
% 2.32/0.69    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) )),
% 2.32/0.69    inference(cnf_transformation,[],[f31])).
% 2.32/0.69  fof(f31,plain,(
% 2.32/0.69    ! [X0] : (! [X1] : (k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.32/0.69    inference(ennf_transformation,[],[f22])).
% 2.32/0.69  fof(f22,axiom,(
% 2.32/0.69    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))))),
% 2.32/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).
% 2.32/0.69  fof(f45,plain,(
% 2.32/0.69    v1_relat_1(sK1)),
% 2.32/0.69    inference(cnf_transformation,[],[f29])).
% 2.32/0.69  fof(f90,plain,(
% 2.32/0.69    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X0,X1)))) )),
% 2.32/0.69    inference(definition_unfolding,[],[f59,f63])).
% 2.32/0.69  fof(f59,plain,(
% 2.32/0.69    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.32/0.69    inference(cnf_transformation,[],[f13])).
% 2.32/0.69  fof(f13,axiom,(
% 2.32/0.69    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.32/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.32/0.69  fof(f1419,plain,(
% 2.32/0.69    r1_tarski(k1_relat_1(sK1),k3_relat_1(sK1))),
% 2.32/0.69    inference(superposition,[],[f104,f716])).
% 2.32/0.69  fof(f716,plain,(
% 2.32/0.69    k3_relat_1(sK1) = k3_tarski(k2_tarski(k2_relat_1(sK1),k1_relat_1(sK1)))),
% 2.32/0.69    inference(unit_resulting_resolution,[],[f45,f101])).
% 2.32/0.69  fof(f104,plain,(
% 2.32/0.69    ( ! [X2,X1] : (r1_tarski(X1,k3_tarski(k2_tarski(X2,X1)))) )),
% 2.32/0.69    inference(superposition,[],[f90,f61])).
% 2.32/0.69  fof(f1459,plain,(
% 2.32/0.69    r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))),
% 2.32/0.69    inference(unit_resulting_resolution,[],[f1180,f1420,f85])).
% 2.32/0.69  fof(f1420,plain,(
% 2.32/0.69    r1_tarski(k2_relat_1(sK1),k3_relat_1(sK1))),
% 2.32/0.69    inference(superposition,[],[f90,f716])).
% 2.32/0.69  fof(f1180,plain,(
% 2.32/0.69    r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))),
% 2.32/0.69    inference(forward_demodulation,[],[f1134,f87])).
% 2.32/0.69  fof(f1134,plain,(
% 2.32/0.69    r1_tarski(k2_relat_1(sK0),k3_tarski(k2_tarski(k2_relat_1(sK1),k1_xboole_0)))),
% 2.32/0.69    inference(unit_resulting_resolution,[],[f1131,f95])).
% 2.32/0.69  fof(f95,plain,(
% 2.32/0.69    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_tarski(X1,X2))) | ~r1_tarski(k6_subset_1(X0,X1),X2)) )),
% 2.32/0.69    inference(definition_unfolding,[],[f84,f62,f63])).
% 2.32/0.69  fof(f84,plain,(
% 2.32/0.69    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 2.32/0.69    inference(cnf_transformation,[],[f40])).
% 2.32/0.69  fof(f40,plain,(
% 2.32/0.69    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.32/0.69    inference(ennf_transformation,[],[f11])).
% 2.32/0.69  fof(f11,axiom,(
% 2.32/0.69    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.32/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 2.32/0.69  fof(f1131,plain,(
% 2.32/0.69    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k1_xboole_0)),
% 2.32/0.69    inference(backward_demodulation,[],[f1024,f1129])).
% 2.32/0.69  fof(f1129,plain,(
% 2.32/0.69    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.32/0.69    inference(unit_resulting_resolution,[],[f162,f383,f78])).
% 2.32/0.69  fof(f78,plain,(
% 2.32/0.69    ( ! [X0,X1] : (sP6(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 2.32/0.69    inference(cnf_transformation,[],[f20])).
% 2.32/0.69  fof(f20,axiom,(
% 2.32/0.69    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 2.32/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 2.32/0.69  fof(f383,plain,(
% 2.32/0.69    ( ! [X0] : (~sP6(X0,k1_xboole_0)) )),
% 2.32/0.69    inference(unit_resulting_resolution,[],[f162,f74])).
% 2.32/0.69  fof(f74,plain,(
% 2.32/0.69    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK7(X0,X2),X2),X0) | ~sP6(X2,X0)) )),
% 2.32/0.69    inference(cnf_transformation,[],[f20])).
% 2.32/0.69  fof(f162,plain,(
% 2.32/0.69    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.32/0.69    inference(unit_resulting_resolution,[],[f131,f49,f65])).
% 2.32/0.69  fof(f65,plain,(
% 2.32/0.69    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.32/0.69    inference(cnf_transformation,[],[f35])).
% 2.32/0.69  fof(f35,plain,(
% 2.32/0.69    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.32/0.69    inference(ennf_transformation,[],[f27])).
% 2.32/0.69  fof(f27,plain,(
% 2.32/0.69    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.32/0.69    inference(rectify,[],[f2])).
% 2.32/0.69  fof(f2,axiom,(
% 2.32/0.69    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.32/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 2.32/0.69  fof(f49,plain,(
% 2.32/0.69    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.32/0.69    inference(cnf_transformation,[],[f12])).
% 2.32/0.69  fof(f12,axiom,(
% 2.32/0.69    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.32/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 2.32/0.69  fof(f131,plain,(
% 2.32/0.69    ( ! [X0,X1] : (r2_hidden(X0,k2_relat_1(sK2(k4_tarski(X1,X0))))) )),
% 2.32/0.69    inference(unit_resulting_resolution,[],[f128,f100])).
% 2.32/0.69  fof(f100,plain,(
% 2.32/0.69    ( ! [X2,X0] : (r2_hidden(X2,k2_relat_1(X0)) | ~sP6(X2,X0)) )),
% 2.32/0.69    inference(equality_resolution,[],[f76])).
% 2.32/0.69  fof(f76,plain,(
% 2.32/0.69    ( ! [X2,X0,X1] : (~sP6(X2,X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 2.32/0.69    inference(cnf_transformation,[],[f20])).
% 2.32/0.69  fof(f128,plain,(
% 2.32/0.69    ( ! [X0,X1] : (sP6(X0,sK2(k4_tarski(X1,X0)))) )),
% 2.32/0.69    inference(unit_resulting_resolution,[],[f58,f75])).
% 2.32/0.69  fof(f75,plain,(
% 2.32/0.69    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) | sP6(X2,X0)) )),
% 2.32/0.69    inference(cnf_transformation,[],[f20])).
% 2.32/0.69  fof(f58,plain,(
% 2.32/0.69    ( ! [X0] : (r2_hidden(X0,sK2(X0))) )),
% 2.32/0.69    inference(cnf_transformation,[],[f34])).
% 2.32/0.69  fof(f34,plain,(
% 2.32/0.69    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X1) | r2_tarski(X2,X1) | ~r1_tarski(X2,X1)) & ! [X3] : (r2_hidden(k1_zfmisc_1(X3),X1) | ~r2_hidden(X3,X1)) & ! [X4,X5] : (r2_hidden(X5,X1) | ~r1_tarski(X5,X4) | ~r2_hidden(X4,X1)) & r2_hidden(X0,X1))),
% 2.32/0.69    inference(flattening,[],[f33])).
% 2.32/0.69  fof(f33,plain,(
% 2.32/0.69    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X1) | r2_tarski(X2,X1) | ~r1_tarski(X2,X1)) & ! [X3] : (r2_hidden(k1_zfmisc_1(X3),X1) | ~r2_hidden(X3,X1)) & ! [X4,X5] : (r2_hidden(X5,X1) | (~r1_tarski(X5,X4) | ~r2_hidden(X4,X1))) & r2_hidden(X0,X1))),
% 2.32/0.69    inference(ennf_transformation,[],[f26])).
% 2.32/0.69  fof(f26,plain,(
% 2.32/0.69    ! [X0] : ? [X1] : (! [X2] : ~(~r2_hidden(X2,X1) & ~r2_tarski(X2,X1) & r1_tarski(X2,X1)) & ! [X3] : (r2_hidden(X3,X1) => r2_hidden(k1_zfmisc_1(X3),X1)) & ! [X4,X5] : ((r1_tarski(X5,X4) & r2_hidden(X4,X1)) => r2_hidden(X5,X1)) & r2_hidden(X0,X1))),
% 2.32/0.69    inference(rectify,[],[f17])).
% 2.32/0.69  fof(f17,axiom,(
% 2.32/0.69    ! [X0] : ? [X1] : (! [X2] : ~(~r2_hidden(X2,X1) & ~r2_tarski(X2,X1) & r1_tarski(X2,X1)) & ! [X2] : (r2_hidden(X2,X1) => r2_hidden(k1_zfmisc_1(X2),X1)) & ! [X2,X3] : ((r1_tarski(X3,X2) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)) & r2_hidden(X0,X1))),
% 2.32/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t136_zfmisc_1)).
% 2.32/0.69  fof(f1024,plain,(
% 2.32/0.69    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k1_xboole_0))),
% 2.32/0.69    inference(forward_demodulation,[],[f1018,f602])).
% 2.32/0.69  fof(f1018,plain,(
% 2.32/0.69    r1_tarski(k6_subset_1(k2_relat_1(sK0),k2_relat_1(sK1)),k2_relat_1(k6_subset_1(sK0,sK1)))),
% 2.32/0.69    inference(unit_resulting_resolution,[],[f48,f45,f54])).
% 2.32/0.69  fof(f54,plain,(
% 2.32/0.69    ( ! [X0,X1] : (r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.32/0.69    inference(cnf_transformation,[],[f32])).
% 2.32/0.69  fof(f32,plain,(
% 2.32/0.69    ! [X0] : (! [X1] : (r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.32/0.69    inference(ennf_transformation,[],[f23])).
% 2.32/0.69  fof(f23,axiom,(
% 2.32/0.69    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))))),
% 2.32/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_relat_1)).
% 2.32/0.69  fof(f47,plain,(
% 2.32/0.69    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 2.32/0.69    inference(cnf_transformation,[],[f29])).
% 2.32/0.69  % SZS output end Proof for theBenchmark
% 2.32/0.69  % (30315)------------------------------
% 2.32/0.69  % (30315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.32/0.69  % (30315)Termination reason: Refutation
% 2.32/0.69  
% 2.32/0.69  % (30315)Memory used [KB]: 7931
% 2.32/0.69  % (30315)Time elapsed: 0.291 s
% 2.32/0.69  % (30315)------------------------------
% 2.32/0.69  % (30315)------------------------------
% 2.60/0.69  % (30290)Success in time 0.334 s
%------------------------------------------------------------------------------
