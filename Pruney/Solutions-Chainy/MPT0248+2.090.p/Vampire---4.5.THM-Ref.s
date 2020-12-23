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
% DateTime   : Thu Dec  3 12:38:02 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 497 expanded)
%              Number of leaves         :   19 ( 157 expanded)
%              Depth                    :   18
%              Number of atoms          :  195 ( 855 expanded)
%              Number of equality atoms :  102 ( 662 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f462,plain,(
    $false ),
    inference(global_subsumption,[],[f76,f401,f461])).

fof(f461,plain,(
    sK2 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(forward_demodulation,[],[f402,f198])).

fof(f198,plain,(
    ! [X0] : k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(unit_resulting_resolution,[],[f148,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f71])).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f38,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f148,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f139,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f139,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f99,f124,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
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

fof(f124,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f78,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f41])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f78,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f33,f41])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f99,plain,(
    ! [X2] : r2_hidden(X2,k2_enumset1(X2,X2,X2,X2)) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k2_enumset1(X2,X2,X2,X2) != X1 ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f54,f72])).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f35,f70])).

fof(f35,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f402,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2)) ),
    inference(backward_demodulation,[],[f74,f401])).

fof(f74,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f32,f72,f71])).

fof(f32,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f401,plain,(
    k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f75,f77,f321,f397])).

fof(f397,plain,
    ( sK1 = k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f376,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f58,f72,f72])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f376,plain,(
    r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f99,f373])).

fof(f373,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,X0)
      | r1_tarski(sK1,X0) ) ),
    inference(duplicate_literal_removal,[],[f370])).

fof(f370,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK0,X0)
      | r1_tarski(sK1,X0)
      | r1_tarski(sK1,X0) ) ),
    inference(superposition,[],[f53,f316])).

fof(f316,plain,(
    ! [X2] :
      ( sK0 = sK5(sK1,X2)
      | r1_tarski(sK1,X2) ) ),
    inference(resolution,[],[f308,f52])).

fof(f308,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | sK0 = X0 ) ),
    inference(resolution,[],[f304,f97])).

fof(f97,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_enumset1(X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f55,f72])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f304,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f250,f65])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( ~ sP8(X3,X1,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f250,plain,(
    ! [X10] :
      ( sP8(X10,k2_enumset1(sK0,sK0,sK0,sK0),sK1)
      | ~ r2_hidden(X10,sK1) ) ),
    inference(forward_demodulation,[],[f240,f162])).

fof(f162,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f160,f34])).

fof(f34,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f160,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f73,f78])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f240,plain,(
    ! [X10] :
      ( ~ r2_hidden(X10,k4_xboole_0(sK1,k1_xboole_0))
      | sP8(X10,k2_enumset1(sK0,sK0,sK0,sK0),sK1) ) ),
    inference(superposition,[],[f102,f119])).

fof(f119,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f79,f74])).

fof(f79,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f37,f71])).

fof(f37,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f102,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | sP8(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] :
      ( sP8(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f67,f41])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( sP8(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f321,plain,
    ( sK2 = k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f89,f252])).

fof(f252,plain,(
    r1_tarski(sK2,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f95,f218])).

fof(f218,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_enumset1(sK0,sK0,sK0,sK0))
      | ~ r1_tarski(X0,sK2) ) ),
    inference(superposition,[],[f90,f74])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f62,f71])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f95,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f77,plain,
    ( sK1 != k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f29,f72])).

fof(f29,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f23])).

fof(f75,plain,
    ( sK2 != k2_enumset1(sK0,sK0,sK0,sK0)
    | sK1 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f31,f72,f72])).

fof(f31,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f76,plain,
    ( sK2 != k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f30,f72])).

fof(f30,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:32:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (12367)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % (12366)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.13/0.52  % (12364)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.13/0.52  % (12365)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.13/0.52  % (12374)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.13/0.52  % (12382)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.13/0.52  % (12374)Refutation not found, incomplete strategy% (12374)------------------------------
% 1.13/0.52  % (12374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.13/0.52  % (12374)Termination reason: Refutation not found, incomplete strategy
% 1.13/0.52  
% 1.13/0.52  % (12374)Memory used [KB]: 10746
% 1.13/0.52  % (12374)Time elapsed: 0.098 s
% 1.13/0.52  % (12374)------------------------------
% 1.13/0.52  % (12374)------------------------------
% 1.13/0.52  % (12387)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.31/0.53  % (12373)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.31/0.53  % (12370)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.31/0.54  % (12390)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.31/0.54  % (12369)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.31/0.54  % (12371)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.31/0.54  % (12368)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.31/0.54  % (12375)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.31/0.54  % (12381)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.31/0.54  % (12379)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.31/0.55  % (12380)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.31/0.55  % (12378)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.31/0.55  % (12393)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.31/0.55  % (12372)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.31/0.55  % (12376)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.31/0.55  % (12377)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.31/0.55  % (12385)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.31/0.56  % (12383)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.31/0.56  % (12389)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.31/0.56  % (12386)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.31/0.56  % (12384)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.31/0.57  % (12388)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.31/0.57  % (12392)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.31/0.58  % (12391)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.31/0.59  % (12384)Refutation not found, incomplete strategy% (12384)------------------------------
% 1.31/0.59  % (12384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.59  % (12384)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.59  
% 1.31/0.59  % (12384)Memory used [KB]: 10874
% 1.31/0.59  % (12384)Time elapsed: 0.156 s
% 1.31/0.59  % (12384)------------------------------
% 1.31/0.59  % (12384)------------------------------
% 1.31/0.60  % (12388)Refutation found. Thanks to Tanya!
% 1.31/0.60  % SZS status Theorem for theBenchmark
% 1.31/0.60  % SZS output start Proof for theBenchmark
% 1.31/0.60  fof(f462,plain,(
% 1.31/0.60    $false),
% 1.31/0.60    inference(global_subsumption,[],[f76,f401,f461])).
% 1.31/0.60  fof(f461,plain,(
% 1.31/0.60    sK2 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.31/0.60    inference(forward_demodulation,[],[f402,f198])).
% 1.31/0.60  fof(f198,plain,(
% 1.31/0.60    ( ! [X0] : (k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0)) = X0) )),
% 1.31/0.60    inference(unit_resulting_resolution,[],[f148,f80])).
% 1.31/0.60  fof(f80,plain,(
% 1.31/0.60    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.31/0.60    inference(definition_unfolding,[],[f45,f71])).
% 1.31/0.60  fof(f71,plain,(
% 1.31/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.31/0.60    inference(definition_unfolding,[],[f38,f70])).
% 1.31/0.60  fof(f70,plain,(
% 1.31/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.31/0.60    inference(definition_unfolding,[],[f39,f61])).
% 1.31/0.60  fof(f61,plain,(
% 1.31/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.31/0.60    inference(cnf_transformation,[],[f17])).
% 1.31/0.60  fof(f17,axiom,(
% 1.31/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.31/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.31/0.60  fof(f39,plain,(
% 1.31/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.31/0.60    inference(cnf_transformation,[],[f16])).
% 1.31/0.60  fof(f16,axiom,(
% 1.31/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.31/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.31/0.60  fof(f38,plain,(
% 1.31/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.31/0.60    inference(cnf_transformation,[],[f19])).
% 1.31/0.60  fof(f19,axiom,(
% 1.31/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.31/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.31/0.60  fof(f45,plain,(
% 1.31/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.31/0.60    inference(cnf_transformation,[],[f26])).
% 1.31/0.60  fof(f26,plain,(
% 1.31/0.60    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.31/0.60    inference(ennf_transformation,[],[f9])).
% 1.31/0.60  fof(f9,axiom,(
% 1.31/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.31/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.31/0.60  fof(f148,plain,(
% 1.31/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.31/0.60    inference(unit_resulting_resolution,[],[f139,f52])).
% 1.31/0.60  fof(f52,plain,(
% 1.31/0.60    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.31/0.60    inference(cnf_transformation,[],[f27])).
% 1.31/0.60  fof(f27,plain,(
% 1.31/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.31/0.60    inference(ennf_transformation,[],[f1])).
% 1.31/0.60  fof(f1,axiom,(
% 1.31/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.31/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.31/0.60  fof(f139,plain,(
% 1.31/0.60    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.31/0.60    inference(unit_resulting_resolution,[],[f99,f124,f42])).
% 1.31/0.60  fof(f42,plain,(
% 1.31/0.60    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.31/0.60    inference(cnf_transformation,[],[f25])).
% 1.31/0.60  fof(f25,plain,(
% 1.31/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.31/0.60    inference(ennf_transformation,[],[f22])).
% 1.31/0.60  fof(f22,plain,(
% 1.31/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.31/0.60    inference(rectify,[],[f4])).
% 1.31/0.60  fof(f4,axiom,(
% 1.31/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.31/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.31/0.60  fof(f124,plain,(
% 1.31/0.60    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.31/0.60    inference(unit_resulting_resolution,[],[f78,f82])).
% 1.31/0.60  fof(f82,plain,(
% 1.31/0.60    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.31/0.60    inference(definition_unfolding,[],[f49,f41])).
% 1.31/0.60  fof(f41,plain,(
% 1.31/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.31/0.60    inference(cnf_transformation,[],[f12])).
% 1.31/0.60  fof(f12,axiom,(
% 1.31/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.31/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.31/0.60  fof(f49,plain,(
% 1.31/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.31/0.60    inference(cnf_transformation,[],[f3])).
% 1.31/0.60  fof(f3,axiom,(
% 1.31/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.31/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.31/0.60  fof(f78,plain,(
% 1.31/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.31/0.60    inference(definition_unfolding,[],[f33,f41])).
% 1.31/0.60  fof(f33,plain,(
% 1.31/0.60    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.31/0.60    inference(cnf_transformation,[],[f10])).
% 1.31/0.60  fof(f10,axiom,(
% 1.31/0.60    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.31/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.31/0.60  fof(f99,plain,(
% 1.31/0.60    ( ! [X2] : (r2_hidden(X2,k2_enumset1(X2,X2,X2,X2))) )),
% 1.31/0.60    inference(equality_resolution,[],[f98])).
% 1.31/0.60  fof(f98,plain,(
% 1.31/0.60    ( ! [X2,X1] : (r2_hidden(X2,X1) | k2_enumset1(X2,X2,X2,X2) != X1) )),
% 1.31/0.60    inference(equality_resolution,[],[f86])).
% 1.31/0.60  fof(f86,plain,(
% 1.31/0.60    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.31/0.60    inference(definition_unfolding,[],[f54,f72])).
% 1.31/0.60  fof(f72,plain,(
% 1.31/0.60    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.31/0.60    inference(definition_unfolding,[],[f35,f70])).
% 1.31/0.60  fof(f35,plain,(
% 1.31/0.60    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.31/0.60    inference(cnf_transformation,[],[f15])).
% 1.31/0.60  fof(f15,axiom,(
% 1.31/0.60    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.31/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.31/0.60  fof(f54,plain,(
% 1.31/0.60    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.31/0.60    inference(cnf_transformation,[],[f14])).
% 1.31/0.60  fof(f14,axiom,(
% 1.31/0.60    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.31/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.31/0.60  fof(f402,plain,(
% 1.31/0.60    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,sK2))),
% 1.31/0.60    inference(backward_demodulation,[],[f74,f401])).
% 1.31/0.60  fof(f74,plain,(
% 1.31/0.60    k2_enumset1(sK0,sK0,sK0,sK0) = k3_tarski(k2_enumset1(sK1,sK1,sK1,sK2))),
% 1.31/0.60    inference(definition_unfolding,[],[f32,f72,f71])).
% 1.31/0.60  fof(f32,plain,(
% 1.31/0.60    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.31/0.60    inference(cnf_transformation,[],[f23])).
% 1.31/0.60  fof(f23,plain,(
% 1.31/0.60    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.31/0.60    inference(ennf_transformation,[],[f21])).
% 1.31/0.60  fof(f21,negated_conjecture,(
% 1.31/0.60    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.31/0.60    inference(negated_conjecture,[],[f20])).
% 1.31/0.60  fof(f20,conjecture,(
% 1.31/0.60    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.31/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.31/0.60  fof(f401,plain,(
% 1.31/0.60    k1_xboole_0 = sK1),
% 1.31/0.60    inference(global_subsumption,[],[f75,f77,f321,f397])).
% 1.31/0.60  fof(f397,plain,(
% 1.31/0.60    sK1 = k2_enumset1(sK0,sK0,sK0,sK0) | k1_xboole_0 = sK1),
% 1.31/0.60    inference(resolution,[],[f376,f89])).
% 1.31/0.60  fof(f89,plain,(
% 1.31/0.60    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 1.31/0.60    inference(definition_unfolding,[],[f58,f72,f72])).
% 1.31/0.60  fof(f58,plain,(
% 1.31/0.60    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.31/0.60    inference(cnf_transformation,[],[f18])).
% 1.31/0.60  fof(f18,axiom,(
% 1.31/0.60    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.31/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.31/0.60  fof(f376,plain,(
% 1.31/0.60    r1_tarski(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.31/0.60    inference(unit_resulting_resolution,[],[f99,f373])).
% 1.31/0.60  fof(f373,plain,(
% 1.31/0.60    ( ! [X0] : (~r2_hidden(sK0,X0) | r1_tarski(sK1,X0)) )),
% 1.31/0.60    inference(duplicate_literal_removal,[],[f370])).
% 1.31/0.60  fof(f370,plain,(
% 1.31/0.60    ( ! [X0] : (~r2_hidden(sK0,X0) | r1_tarski(sK1,X0) | r1_tarski(sK1,X0)) )),
% 1.31/0.60    inference(superposition,[],[f53,f316])).
% 1.31/0.60  fof(f316,plain,(
% 1.31/0.60    ( ! [X2] : (sK0 = sK5(sK1,X2) | r1_tarski(sK1,X2)) )),
% 1.31/0.60    inference(resolution,[],[f308,f52])).
% 1.31/0.60  fof(f308,plain,(
% 1.31/0.60    ( ! [X0] : (~r2_hidden(X0,sK1) | sK0 = X0) )),
% 1.31/0.60    inference(resolution,[],[f304,f97])).
% 1.31/0.60  fof(f97,plain,(
% 1.31/0.60    ( ! [X2,X0] : (~r2_hidden(X2,k2_enumset1(X0,X0,X0,X0)) | X0 = X2) )),
% 1.31/0.60    inference(equality_resolution,[],[f85])).
% 1.31/0.60  fof(f85,plain,(
% 1.31/0.60    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.31/0.60    inference(definition_unfolding,[],[f55,f72])).
% 1.31/0.60  fof(f55,plain,(
% 1.31/0.60    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.31/0.60    inference(cnf_transformation,[],[f14])).
% 1.31/0.60  fof(f304,plain,(
% 1.31/0.60    ( ! [X0] : (r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(X0,sK1)) )),
% 1.31/0.60    inference(resolution,[],[f250,f65])).
% 1.31/0.60  fof(f65,plain,(
% 1.31/0.60    ( ! [X0,X3,X1] : (~sP8(X3,X1,X0) | r2_hidden(X3,X1)) )),
% 1.31/0.60    inference(cnf_transformation,[],[f2])).
% 1.31/0.60  fof(f2,axiom,(
% 1.31/0.60    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.31/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.31/0.60  fof(f250,plain,(
% 1.31/0.60    ( ! [X10] : (sP8(X10,k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~r2_hidden(X10,sK1)) )),
% 1.31/0.60    inference(forward_demodulation,[],[f240,f162])).
% 1.31/0.60  fof(f162,plain,(
% 1.31/0.60    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.31/0.60    inference(forward_demodulation,[],[f160,f34])).
% 1.31/0.60  fof(f34,plain,(
% 1.31/0.60    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.31/0.60    inference(cnf_transformation,[],[f13])).
% 1.31/0.60  fof(f13,axiom,(
% 1.31/0.60    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.31/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.31/0.60  fof(f160,plain,(
% 1.31/0.60    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 1.31/0.60    inference(superposition,[],[f73,f78])).
% 1.31/0.60  fof(f73,plain,(
% 1.31/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.31/0.60    inference(definition_unfolding,[],[f40,f41])).
% 1.31/0.60  fof(f40,plain,(
% 1.31/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.31/0.60    inference(cnf_transformation,[],[f7])).
% 1.31/0.60  fof(f7,axiom,(
% 1.31/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.31/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.31/0.60  fof(f240,plain,(
% 1.31/0.60    ( ! [X10] : (~r2_hidden(X10,k4_xboole_0(sK1,k1_xboole_0)) | sP8(X10,k2_enumset1(sK0,sK0,sK0,sK0),sK1)) )),
% 1.31/0.60    inference(superposition,[],[f102,f119])).
% 1.31/0.60  fof(f119,plain,(
% 1.31/0.60    k1_xboole_0 = k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.31/0.60    inference(superposition,[],[f79,f74])).
% 1.31/0.60  fof(f79,plain,(
% 1.31/0.60    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k3_tarski(k2_enumset1(X0,X0,X0,X1)))) )),
% 1.31/0.60    inference(definition_unfolding,[],[f37,f71])).
% 1.31/0.60  fof(f37,plain,(
% 1.31/0.60    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.31/0.60    inference(cnf_transformation,[],[f11])).
% 1.31/0.60  fof(f11,axiom,(
% 1.31/0.60    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.31/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.31/0.60  fof(f102,plain,(
% 1.31/0.60    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | sP8(X3,X1,X0)) )),
% 1.31/0.60    inference(equality_resolution,[],[f93])).
% 1.31/0.60  fof(f93,plain,(
% 1.31/0.60    ( ! [X2,X0,X3,X1] : (sP8(X3,X1,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 1.31/0.60    inference(definition_unfolding,[],[f67,f41])).
% 1.31/0.60  fof(f67,plain,(
% 1.31/0.60    ( ! [X2,X0,X3,X1] : (sP8(X3,X1,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.31/0.60    inference(cnf_transformation,[],[f2])).
% 1.31/0.60  fof(f53,plain,(
% 1.31/0.60    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.31/0.60    inference(cnf_transformation,[],[f27])).
% 1.31/0.60  fof(f321,plain,(
% 1.31/0.60    sK2 = k2_enumset1(sK0,sK0,sK0,sK0) | k1_xboole_0 = sK2),
% 1.31/0.60    inference(resolution,[],[f89,f252])).
% 1.31/0.60  fof(f252,plain,(
% 1.31/0.60    r1_tarski(sK2,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.31/0.60    inference(unit_resulting_resolution,[],[f95,f218])).
% 1.31/0.60  fof(f218,plain,(
% 1.31/0.60    ( ! [X0] : (r1_tarski(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r1_tarski(X0,sK2)) )),
% 1.31/0.60    inference(superposition,[],[f90,f74])).
% 1.31/0.60  fof(f90,plain,(
% 1.31/0.60    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k2_enumset1(X2,X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 1.31/0.60    inference(definition_unfolding,[],[f62,f71])).
% 1.31/0.60  fof(f62,plain,(
% 1.31/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 1.31/0.60    inference(cnf_transformation,[],[f28])).
% 1.31/0.60  fof(f28,plain,(
% 1.31/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 1.31/0.60    inference(ennf_transformation,[],[f8])).
% 1.31/0.60  fof(f8,axiom,(
% 1.31/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 1.31/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 1.31/0.60  fof(f95,plain,(
% 1.31/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.31/0.60    inference(equality_resolution,[],[f47])).
% 1.31/0.60  fof(f47,plain,(
% 1.31/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.31/0.60    inference(cnf_transformation,[],[f6])).
% 1.31/0.60  fof(f6,axiom,(
% 1.31/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.31/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.31/0.60  fof(f77,plain,(
% 1.31/0.60    sK1 != k2_enumset1(sK0,sK0,sK0,sK0) | k1_xboole_0 != sK2),
% 1.31/0.60    inference(definition_unfolding,[],[f29,f72])).
% 1.31/0.60  fof(f29,plain,(
% 1.31/0.60    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 1.31/0.60    inference(cnf_transformation,[],[f23])).
% 1.31/0.60  fof(f75,plain,(
% 1.31/0.60    sK2 != k2_enumset1(sK0,sK0,sK0,sK0) | sK1 != k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.31/0.60    inference(definition_unfolding,[],[f31,f72,f72])).
% 1.31/0.60  fof(f31,plain,(
% 1.31/0.60    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0)),
% 1.31/0.60    inference(cnf_transformation,[],[f23])).
% 1.31/0.60  fof(f76,plain,(
% 1.31/0.60    sK2 != k2_enumset1(sK0,sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 1.31/0.60    inference(definition_unfolding,[],[f30,f72])).
% 1.31/0.60  fof(f30,plain,(
% 1.31/0.60    k1_xboole_0 != sK1 | sK2 != k1_tarski(sK0)),
% 1.31/0.60    inference(cnf_transformation,[],[f23])).
% 1.31/0.60  % SZS output end Proof for theBenchmark
% 1.31/0.60  % (12388)------------------------------
% 1.31/0.60  % (12388)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.60  % (12388)Termination reason: Refutation
% 1.31/0.60  
% 1.31/0.60  % (12388)Memory used [KB]: 6524
% 1.31/0.60  % (12388)Time elapsed: 0.191 s
% 1.31/0.60  % (12388)------------------------------
% 1.31/0.60  % (12388)------------------------------
% 1.31/0.60  % (12363)Success in time 0.237 s
%------------------------------------------------------------------------------
