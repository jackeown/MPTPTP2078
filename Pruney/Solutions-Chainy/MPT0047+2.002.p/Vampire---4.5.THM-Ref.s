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
% DateTime   : Thu Dec  3 12:29:51 EST 2020

% Result     : Theorem 21.83s
% Output     : Refutation 21.83s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 112 expanded)
%              Number of leaves         :   19 (  33 expanded)
%              Depth                    :   21
%              Number of atoms          :  188 ( 253 expanded)
%              Number of equality atoms :   53 (  76 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f68676,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f68444])).

fof(f68444,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f33,f67221])).

fof(f67221,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(backward_demodulation,[],[f64514,f66996])).

fof(f66996,plain,(
    ! [X231,X229,X230] : k4_xboole_0(X229,X230) = k3_xboole_0(k4_xboole_0(k2_xboole_0(X229,X231),X230),k4_xboole_0(X229,X230)) ),
    inference(superposition,[],[f738,f568])).

fof(f568,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X2),X1)) ),
    inference(unit_resulting_resolution,[],[f490,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f490,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X2),X1)) ),
    inference(unit_resulting_resolution,[],[f36,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f738,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k3_xboole_0(X4,k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f115,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f115,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X1) ),
    inference(unit_resulting_resolution,[],[f90,f45])).

fof(f90,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f82,f38])).

fof(f82,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f66,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f66,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f36,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f64514,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k3_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),k4_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f63016,f45])).

fof(f63016,plain,(
    ! [X2,X1] : r1_tarski(k4_xboole_0(k2_xboole_0(X2,X1),X1),k4_xboole_0(X2,X1)) ),
    inference(superposition,[],[f61558,f39])).

fof(f61558,plain,(
    ! [X62,X63] : r1_tarski(k4_xboole_0(k2_xboole_0(X62,X63),X62),k4_xboole_0(X63,X62)) ),
    inference(superposition,[],[f61419,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f61419,plain,(
    ! [X2,X1] : r1_tarski(k4_xboole_0(k2_xboole_0(X2,X1),X2),X1) ),
    inference(superposition,[],[f61290,f39])).

fof(f61290,plain,(
    ! [X8,X9] : r1_tarski(k4_xboole_0(k2_xboole_0(X8,X9),X9),X8) ),
    inference(superposition,[],[f61074,f417])).

fof(f417,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f117,f38])).

fof(f117,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(unit_resulting_resolution,[],[f37,f45])).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f61074,plain,(
    ! [X68,X69,X67] : r1_tarski(k3_xboole_0(k2_xboole_0(X69,X67),k4_xboole_0(X68,X67)),X69) ),
    inference(forward_demodulation,[],[f60970,f57])).

fof(f57,plain,(
    ! [X0] : k2_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f35,f34])).

fof(f34,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f35,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f60970,plain,(
    ! [X68,X69,X67] : r1_tarski(k3_xboole_0(k2_xboole_0(X69,X67),k4_xboole_0(X68,X67)),k2_xboole_0(X69,o_0_0_xboole_0)) ),
    inference(superposition,[],[f1696,f8239])).

fof(f8239,plain,(
    ! [X4,X3] : o_0_0_xboole_0 = k3_xboole_0(X4,k4_xboole_0(X3,X4)) ),
    inference(superposition,[],[f8212,f38])).

fof(f8212,plain,(
    ! [X0,X1] : o_0_0_xboole_0 = k3_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(unit_resulting_resolution,[],[f8211,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = o_0_0_xboole_0 ) ),
    inference(definition_unfolding,[],[f46,f34])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f8211,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(duplicate_literal_removal,[],[f8199])).

fof(f8199,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k4_xboole_0(X0,X1),X1)
      | r1_xboole_0(k4_xboole_0(X0,X1),X1) ) ),
    inference(resolution,[],[f192,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f192,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(k4_xboole_0(X0,X1),X2),X1)
      | r1_xboole_0(k4_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f61,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f61,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f1696,plain,(
    ! [X4,X2,X3] : r1_tarski(k3_xboole_0(k2_xboole_0(X2,X3),X4),k2_xboole_0(X2,k3_xboole_0(X3,X4))) ),
    inference(superposition,[],[f1164,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).

fof(f1164,plain,(
    ! [X17,X15,X16] : r1_tarski(k3_xboole_0(X15,X17),k3_xboole_0(X15,k2_xboole_0(X16,X17))) ),
    inference(superposition,[],[f66,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f33,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f23])).

fof(f23,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),X1)
   => k4_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),sK1) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:45:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.47  % (16572)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (16590)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.51  % (16575)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (16575)Refutation not found, incomplete strategy% (16575)------------------------------
% 0.20/0.51  % (16575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (16575)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (16575)Memory used [KB]: 10618
% 0.20/0.51  % (16575)Time elapsed: 0.106 s
% 0.20/0.51  % (16575)------------------------------
% 0.20/0.51  % (16575)------------------------------
% 0.20/0.51  % (16588)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (16567)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (16570)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (16567)Refutation not found, incomplete strategy% (16567)------------------------------
% 0.20/0.51  % (16567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (16567)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (16567)Memory used [KB]: 10618
% 0.20/0.51  % (16567)Time elapsed: 0.103 s
% 0.20/0.51  % (16567)------------------------------
% 0.20/0.51  % (16567)------------------------------
% 0.20/0.51  % (16569)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (16593)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.51  % (16569)Refutation not found, incomplete strategy% (16569)------------------------------
% 0.20/0.51  % (16569)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (16569)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (16569)Memory used [KB]: 6140
% 0.20/0.51  % (16569)Time elapsed: 0.119 s
% 0.20/0.51  % (16569)------------------------------
% 0.20/0.51  % (16569)------------------------------
% 0.20/0.51  % (16576)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (16585)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.51  % (16580)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (16587)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (16574)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (16594)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (16587)Refutation not found, incomplete strategy% (16587)------------------------------
% 0.20/0.52  % (16587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (16587)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (16587)Memory used [KB]: 10618
% 0.20/0.52  % (16587)Time elapsed: 0.079 s
% 0.20/0.52  % (16587)------------------------------
% 0.20/0.52  % (16587)------------------------------
% 0.20/0.52  % (16578)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (16571)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (16579)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (16585)Refutation not found, incomplete strategy% (16585)------------------------------
% 0.20/0.53  % (16585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (16585)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (16585)Memory used [KB]: 10618
% 0.20/0.53  % (16585)Time elapsed: 0.117 s
% 0.20/0.53  % (16585)------------------------------
% 0.20/0.53  % (16585)------------------------------
% 0.20/0.53  % (16582)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.53  % (16586)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (16565)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (16590)Refutation not found, incomplete strategy% (16590)------------------------------
% 0.20/0.53  % (16590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (16582)Refutation not found, incomplete strategy% (16582)------------------------------
% 0.20/0.53  % (16582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (16582)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (16582)Memory used [KB]: 10618
% 0.20/0.53  % (16582)Time elapsed: 0.131 s
% 0.20/0.53  % (16582)------------------------------
% 0.20/0.53  % (16582)------------------------------
% 0.20/0.53  % (16565)Refutation not found, incomplete strategy% (16565)------------------------------
% 0.20/0.53  % (16565)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (16565)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (16565)Memory used [KB]: 1663
% 0.20/0.53  % (16565)Time elapsed: 0.122 s
% 0.20/0.53  % (16565)------------------------------
% 0.20/0.53  % (16565)------------------------------
% 0.20/0.53  % (16586)Refutation not found, incomplete strategy% (16586)------------------------------
% 0.20/0.53  % (16586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (16586)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (16586)Memory used [KB]: 1663
% 0.20/0.53  % (16586)Time elapsed: 0.129 s
% 0.20/0.53  % (16586)------------------------------
% 0.20/0.53  % (16586)------------------------------
% 0.20/0.53  % (16568)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (16590)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (16590)Memory used [KB]: 6140
% 0.20/0.53  % (16590)Time elapsed: 0.130 s
% 0.20/0.53  % (16590)------------------------------
% 0.20/0.53  % (16590)------------------------------
% 0.20/0.53  % (16566)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (16591)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (16591)Refutation not found, incomplete strategy% (16591)------------------------------
% 0.20/0.54  % (16591)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (16591)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (16591)Memory used [KB]: 10746
% 0.20/0.54  % (16591)Time elapsed: 0.138 s
% 0.20/0.54  % (16591)------------------------------
% 0.20/0.54  % (16591)------------------------------
% 0.20/0.54  % (16576)Refutation not found, incomplete strategy% (16576)------------------------------
% 0.20/0.54  % (16576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (16576)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (16576)Memory used [KB]: 10618
% 0.20/0.54  % (16576)Time elapsed: 0.135 s
% 0.20/0.54  % (16576)------------------------------
% 0.20/0.54  % (16576)------------------------------
% 0.20/0.54  % (16574)Refutation not found, incomplete strategy% (16574)------------------------------
% 0.20/0.54  % (16574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (16574)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (16574)Memory used [KB]: 10618
% 0.20/0.54  % (16574)Time elapsed: 0.135 s
% 0.20/0.54  % (16574)------------------------------
% 0.20/0.54  % (16574)------------------------------
% 0.20/0.54  % (16589)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (16583)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (16584)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (16577)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (16573)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (16581)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (16573)Refutation not found, incomplete strategy% (16573)------------------------------
% 0.20/0.55  % (16573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (16573)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (16573)Memory used [KB]: 10618
% 0.20/0.55  % (16573)Time elapsed: 0.150 s
% 0.20/0.55  % (16573)------------------------------
% 0.20/0.55  % (16573)------------------------------
% 0.20/0.55  % (16592)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.90/0.60  % (16597)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.90/0.60  % (16597)Refutation not found, incomplete strategy% (16597)------------------------------
% 1.90/0.60  % (16597)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.61  % (16597)Termination reason: Refutation not found, incomplete strategy
% 1.90/0.61  
% 1.90/0.61  % (16597)Memory used [KB]: 6140
% 1.90/0.61  % (16597)Time elapsed: 0.064 s
% 1.90/0.61  % (16597)------------------------------
% 1.90/0.61  % (16597)------------------------------
% 2.06/0.63  % (16600)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.13/0.63  % (16601)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.13/0.64  % (16605)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.13/0.64  % (16605)Refutation not found, incomplete strategy% (16605)------------------------------
% 2.13/0.64  % (16605)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.13/0.64  % (16605)Termination reason: Refutation not found, incomplete strategy
% 2.13/0.64  
% 2.13/0.64  % (16605)Memory used [KB]: 1663
% 2.13/0.64  % (16605)Time elapsed: 0.063 s
% 2.13/0.64  % (16605)------------------------------
% 2.13/0.64  % (16605)------------------------------
% 2.13/0.65  % (16599)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.13/0.66  % (16598)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.13/0.66  % (16603)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.13/0.66  % (16602)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.13/0.67  % (16604)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.13/0.67  % (16606)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.13/0.67  % (16608)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 2.13/0.67  % (16607)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 2.13/0.68  % (16609)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 2.76/0.74  % (16610)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 2.76/0.75  % (16610)Refutation not found, incomplete strategy% (16610)------------------------------
% 2.76/0.75  % (16610)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.76/0.75  % (16610)Termination reason: Refutation not found, incomplete strategy
% 2.76/0.75  
% 2.76/0.75  % (16610)Memory used [KB]: 1663
% 2.76/0.75  % (16610)Time elapsed: 0.115 s
% 2.76/0.75  % (16610)------------------------------
% 2.76/0.75  % (16610)------------------------------
% 2.76/0.77  % (16611)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 2.76/0.77  % (16598)Refutation not found, incomplete strategy% (16598)------------------------------
% 2.76/0.77  % (16598)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.76/0.78  % (16598)Termination reason: Refutation not found, incomplete strategy
% 2.76/0.78  
% 2.76/0.78  % (16598)Memory used [KB]: 6140
% 2.76/0.78  % (16598)Time elapsed: 0.222 s
% 2.76/0.78  % (16598)------------------------------
% 2.76/0.78  % (16598)------------------------------
% 3.30/0.83  % (16570)Time limit reached!
% 3.30/0.83  % (16570)------------------------------
% 3.30/0.83  % (16570)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.30/0.83  % (16570)Termination reason: Time limit
% 3.30/0.83  
% 3.30/0.83  % (16570)Memory used [KB]: 10234
% 3.30/0.83  % (16570)Time elapsed: 0.426 s
% 3.30/0.83  % (16570)------------------------------
% 3.30/0.83  % (16570)------------------------------
% 3.96/0.88  % (16612)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 4.04/0.89  % (16613)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 4.04/0.90  % (16577)Time limit reached!
% 4.04/0.90  % (16577)------------------------------
% 4.04/0.90  % (16577)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.04/0.90  % (16577)Termination reason: Time limit
% 4.04/0.90  % (16577)Termination phase: Saturation
% 4.04/0.90  
% 4.04/0.90  % (16577)Memory used [KB]: 10362
% 4.04/0.90  % (16577)Time elapsed: 0.500 s
% 4.04/0.90  % (16577)------------------------------
% 4.04/0.90  % (16577)------------------------------
% 4.26/0.92  % (16566)Time limit reached!
% 4.26/0.92  % (16566)------------------------------
% 4.26/0.92  % (16566)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.26/0.92  % (16566)Termination reason: Time limit
% 4.26/0.92  
% 4.26/0.92  % (16566)Memory used [KB]: 9210
% 4.26/0.92  % (16566)Time elapsed: 0.517 s
% 4.26/0.92  % (16566)------------------------------
% 4.26/0.92  % (16566)------------------------------
% 4.34/0.96  % (16614)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 4.34/0.96  % (16614)Refutation not found, incomplete strategy% (16614)------------------------------
% 4.34/0.96  % (16614)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.34/0.96  % (16614)Termination reason: Refutation not found, incomplete strategy
% 4.34/0.96  
% 4.34/0.96  % (16614)Memory used [KB]: 6140
% 4.34/0.96  % (16614)Time elapsed: 0.108 s
% 4.34/0.96  % (16614)------------------------------
% 4.34/0.96  % (16614)------------------------------
% 4.34/0.96  % (16601)Time limit reached!
% 4.34/0.96  % (16601)------------------------------
% 4.34/0.96  % (16601)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.34/0.96  % (16601)Termination reason: Time limit
% 4.34/0.96  
% 4.34/0.96  % (16601)Memory used [KB]: 15991
% 4.34/0.96  % (16601)Time elapsed: 0.406 s
% 4.34/0.96  % (16601)------------------------------
% 4.34/0.96  % (16601)------------------------------
% 4.34/0.97  % (16600)Time limit reached!
% 4.34/0.97  % (16600)------------------------------
% 4.34/0.97  % (16600)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.34/0.97  % (16600)Termination reason: Time limit
% 4.34/0.97  
% 4.34/0.97  % (16600)Memory used [KB]: 9978
% 4.34/0.97  % (16600)Time elapsed: 0.427 s
% 4.34/0.97  % (16600)------------------------------
% 4.34/0.97  % (16600)------------------------------
% 4.34/0.99  % (16572)Time limit reached!
% 4.34/0.99  % (16572)------------------------------
% 4.34/0.99  % (16572)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.34/0.99  % (16572)Termination reason: Time limit
% 4.34/0.99  % (16572)Termination phase: Saturation
% 4.34/0.99  
% 4.34/0.99  % (16572)Memory used [KB]: 11385
% 4.34/0.99  % (16572)Time elapsed: 0.600 s
% 4.34/0.99  % (16572)------------------------------
% 4.34/0.99  % (16572)------------------------------
% 4.34/0.99  % (16581)Time limit reached!
% 4.34/0.99  % (16581)------------------------------
% 4.34/0.99  % (16581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.34/0.99  % (16581)Termination reason: Time limit
% 4.34/0.99  % (16581)Termination phase: Saturation
% 4.34/0.99  
% 4.34/0.99  % (16581)Memory used [KB]: 17398
% 4.34/0.99  % (16581)Time elapsed: 0.600 s
% 4.34/0.99  % (16581)------------------------------
% 4.34/0.99  % (16581)------------------------------
% 4.91/1.03  % (16615)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 4.91/1.04  % (16593)Time limit reached!
% 4.91/1.04  % (16593)------------------------------
% 4.91/1.04  % (16593)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.91/1.04  % (16593)Termination reason: Time limit
% 4.91/1.04  
% 4.91/1.04  % (16593)Memory used [KB]: 12153
% 4.91/1.04  % (16593)Time elapsed: 0.624 s
% 4.91/1.04  % (16593)------------------------------
% 4.91/1.04  % (16593)------------------------------
% 4.91/1.06  % (16618)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 4.91/1.06  % (16616)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 4.91/1.07  % (16609)Time limit reached!
% 4.91/1.07  % (16609)------------------------------
% 4.91/1.07  % (16609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.91/1.07  % (16609)Termination reason: Time limit
% 4.91/1.07  
% 4.91/1.07  % (16609)Memory used [KB]: 4477
% 4.91/1.07  % (16609)Time elapsed: 0.509 s
% 4.91/1.07  % (16609)------------------------------
% 4.91/1.07  % (16609)------------------------------
% 4.91/1.08  % (16619)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 5.28/1.09  % (16617)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 5.28/1.13  % (16620)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 5.28/1.13  % (16621)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 5.28/1.15  % (16622)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 5.28/1.15  % (16622)Refutation not found, incomplete strategy% (16622)------------------------------
% 5.28/1.15  % (16622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.28/1.15  % (16622)Termination reason: Refutation not found, incomplete strategy
% 5.28/1.15  
% 5.28/1.15  % (16622)Memory used [KB]: 6140
% 5.28/1.15  % (16622)Time elapsed: 0.045 s
% 5.28/1.15  % (16622)------------------------------
% 5.28/1.15  % (16622)------------------------------
% 6.63/1.21  % (16623)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 6.63/1.21  % (16623)Refutation not found, incomplete strategy% (16623)------------------------------
% 6.63/1.21  % (16623)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.63/1.21  % (16623)Termination reason: Refutation not found, incomplete strategy
% 6.63/1.21  
% 6.63/1.21  % (16623)Memory used [KB]: 6140
% 6.63/1.21  % (16623)Time elapsed: 0.106 s
% 6.63/1.21  % (16623)------------------------------
% 6.63/1.21  % (16623)------------------------------
% 6.87/1.24  % (16613)Time limit reached!
% 6.87/1.24  % (16613)------------------------------
% 6.87/1.24  % (16613)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.87/1.24  % (16613)Termination reason: Time limit
% 6.87/1.24  % (16613)Termination phase: Saturation
% 6.87/1.24  
% 6.87/1.24  % (16613)Memory used [KB]: 8059
% 6.87/1.24  % (16613)Time elapsed: 0.400 s
% 6.87/1.24  % (16613)------------------------------
% 6.87/1.24  % (16613)------------------------------
% 6.87/1.26  % (16624)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 6.87/1.26  % (16624)Refutation not found, incomplete strategy% (16624)------------------------------
% 6.87/1.26  % (16624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.87/1.26  % (16624)Termination reason: Refutation not found, incomplete strategy
% 6.87/1.26  
% 6.87/1.26  % (16624)Memory used [KB]: 10618
% 6.87/1.26  % (16624)Time elapsed: 0.042 s
% 6.87/1.26  % (16624)------------------------------
% 6.87/1.26  % (16624)------------------------------
% 7.45/1.36  % (16616)Time limit reached!
% 7.45/1.36  % (16616)------------------------------
% 7.45/1.36  % (16616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.45/1.36  % (16616)Termination reason: Time limit
% 7.45/1.36  % (16616)Termination phase: Saturation
% 7.45/1.36  
% 7.45/1.36  % (16616)Memory used [KB]: 3454
% 7.45/1.36  % (16616)Time elapsed: 0.400 s
% 7.45/1.36  % (16616)------------------------------
% 7.45/1.36  % (16616)------------------------------
% 8.04/1.45  % (16621)Time limit reached!
% 8.04/1.45  % (16621)------------------------------
% 8.04/1.45  % (16621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.04/1.45  % (16621)Termination reason: Time limit
% 8.04/1.45  % (16621)Termination phase: Saturation
% 8.04/1.45  
% 8.04/1.45  % (16621)Memory used [KB]: 10234
% 8.04/1.45  % (16621)Time elapsed: 0.400 s
% 8.04/1.45  % (16621)------------------------------
% 8.04/1.45  % (16621)------------------------------
% 10.62/1.70  % (16589)Time limit reached!
% 10.62/1.70  % (16589)------------------------------
% 10.62/1.70  % (16589)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.62/1.70  % (16580)Time limit reached!
% 10.62/1.70  % (16580)------------------------------
% 10.62/1.70  % (16580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.62/1.70  % (16589)Termination reason: Time limit
% 10.62/1.70  % (16580)Termination reason: Time limit
% 10.62/1.70  % (16580)Termination phase: Saturation
% 10.62/1.70  % (16589)Termination phase: Saturation
% 10.62/1.70  
% 10.62/1.70  
% 10.62/1.70  % (16580)Memory used [KB]: 9466
% 10.62/1.70  % (16589)Memory used [KB]: 17270
% 10.62/1.70  % (16580)Time elapsed: 1.300 s
% 10.62/1.70  % (16589)Time elapsed: 1.300 s
% 10.62/1.70  % (16580)------------------------------
% 10.62/1.70  % (16580)------------------------------
% 10.62/1.70  % (16589)------------------------------
% 10.62/1.70  % (16589)------------------------------
% 10.62/1.77  % (16603)Time limit reached!
% 10.62/1.77  % (16603)------------------------------
% 10.62/1.77  % (16603)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.62/1.77  % (16603)Termination reason: Time limit
% 10.62/1.77  
% 10.62/1.77  % (16603)Memory used [KB]: 14328
% 10.62/1.77  % (16603)Time elapsed: 1.214 s
% 10.62/1.77  % (16603)------------------------------
% 10.62/1.77  % (16603)------------------------------
% 12.31/1.91  % (16592)Time limit reached!
% 12.31/1.91  % (16592)------------------------------
% 12.31/1.91  % (16592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.31/1.91  % (16592)Termination reason: Time limit
% 12.31/1.91  
% 12.31/1.91  % (16592)Memory used [KB]: 17142
% 12.31/1.91  % (16592)Time elapsed: 1.508 s
% 12.31/1.91  % (16592)------------------------------
% 12.31/1.91  % (16592)------------------------------
% 12.49/1.98  % (16612)Time limit reached!
% 12.49/1.98  % (16612)------------------------------
% 12.49/1.98  % (16612)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.49/1.98  % (16612)Termination reason: Time limit
% 12.49/1.98  % (16612)Termination phase: Saturation
% 12.49/1.98  
% 12.49/1.98  % (16612)Memory used [KB]: 14839
% 12.49/1.98  % (16612)Time elapsed: 1.200 s
% 12.49/1.98  % (16612)------------------------------
% 12.49/1.98  % (16612)------------------------------
% 14.73/2.22  % (16579)Time limit reached!
% 14.73/2.22  % (16579)------------------------------
% 14.73/2.22  % (16579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.91/2.23  % (16615)Time limit reached!
% 14.91/2.23  % (16615)------------------------------
% 14.91/2.23  % (16615)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.91/2.23  % (16615)Termination reason: Time limit
% 14.91/2.23  % (16615)Termination phase: Saturation
% 14.91/2.23  
% 14.91/2.23  % (16615)Memory used [KB]: 18805
% 14.91/2.23  % (16615)Time elapsed: 1.300 s
% 14.91/2.23  % (16615)------------------------------
% 14.91/2.23  % (16615)------------------------------
% 14.91/2.24  % (16579)Termination reason: Time limit
% 14.91/2.24  % (16579)Termination phase: Saturation
% 14.91/2.24  
% 14.91/2.24  % (16579)Memory used [KB]: 14328
% 14.91/2.24  % (16579)Time elapsed: 1.800 s
% 14.91/2.24  % (16579)------------------------------
% 14.91/2.24  % (16579)------------------------------
% 14.91/2.26  % (16599)Time limit reached!
% 14.91/2.26  % (16599)------------------------------
% 14.91/2.26  % (16599)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.91/2.26  % (16599)Termination reason: Time limit
% 14.91/2.26  % (16599)Termination phase: Saturation
% 14.91/2.26  
% 14.91/2.26  % (16599)Memory used [KB]: 23283
% 14.91/2.26  % (16599)Time elapsed: 1.700 s
% 14.91/2.26  % (16599)------------------------------
% 14.91/2.26  % (16599)------------------------------
% 16.27/2.41  % (16583)Time limit reached!
% 16.27/2.41  % (16583)------------------------------
% 16.27/2.41  % (16583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.27/2.42  % (16583)Termination reason: Time limit
% 16.27/2.42  
% 16.27/2.42  % (16583)Memory used [KB]: 24434
% 16.27/2.42  % (16583)Time elapsed: 2.013 s
% 16.27/2.42  % (16583)------------------------------
% 16.27/2.42  % (16583)------------------------------
% 16.27/2.46  % (16571)Time limit reached!
% 16.27/2.46  % (16571)------------------------------
% 16.27/2.46  % (16571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.27/2.46  % (16571)Termination reason: Time limit
% 16.27/2.46  
% 16.27/2.46  % (16571)Memory used [KB]: 35180
% 16.27/2.46  % (16571)Time elapsed: 2.010 s
% 16.27/2.46  % (16571)------------------------------
% 16.27/2.46  % (16571)------------------------------
% 21.07/3.01  % (16584)Time limit reached!
% 21.07/3.01  % (16584)------------------------------
% 21.07/3.01  % (16584)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.07/3.02  % (16584)Termination reason: Time limit
% 21.07/3.02  % (16584)Termination phase: Saturation
% 21.07/3.02  
% 21.07/3.02  % (16584)Memory used [KB]: 54498
% 21.07/3.02  % (16584)Time elapsed: 2.600 s
% 21.07/3.02  % (16584)------------------------------
% 21.07/3.02  % (16584)------------------------------
% 21.83/3.14  % (16604)Refutation found. Thanks to Tanya!
% 21.83/3.14  % SZS status Theorem for theBenchmark
% 21.83/3.16  % SZS output start Proof for theBenchmark
% 21.83/3.16  fof(f68676,plain,(
% 21.83/3.16    $false),
% 21.83/3.16    inference(trivial_inequality_removal,[],[f68444])).
% 21.83/3.16  fof(f68444,plain,(
% 21.83/3.16    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1)),
% 21.83/3.16    inference(superposition,[],[f33,f67221])).
% 21.83/3.16  fof(f67221,plain,(
% 21.83/3.16    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 21.83/3.16    inference(backward_demodulation,[],[f64514,f66996])).
% 21.83/3.16  fof(f66996,plain,(
% 21.83/3.16    ( ! [X231,X229,X230] : (k4_xboole_0(X229,X230) = k3_xboole_0(k4_xboole_0(k2_xboole_0(X229,X231),X230),k4_xboole_0(X229,X230))) )),
% 21.83/3.16    inference(superposition,[],[f738,f568])).
% 21.83/3.16  fof(f568,plain,(
% 21.83/3.16    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X2),X1))) )),
% 21.83/3.16    inference(unit_resulting_resolution,[],[f490,f45])).
% 21.83/3.16  fof(f45,plain,(
% 21.83/3.16    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 21.83/3.16    inference(cnf_transformation,[],[f21])).
% 21.83/3.16  fof(f21,plain,(
% 21.83/3.16    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 21.83/3.16    inference(ennf_transformation,[],[f11])).
% 21.83/3.16  fof(f11,axiom,(
% 21.83/3.16    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 21.83/3.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 21.83/3.16  fof(f490,plain,(
% 21.83/3.16    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X2),X1))) )),
% 21.83/3.16    inference(unit_resulting_resolution,[],[f36,f50])).
% 21.83/3.16  fof(f50,plain,(
% 21.83/3.16    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 21.83/3.16    inference(cnf_transformation,[],[f22])).
% 21.83/3.16  fof(f22,plain,(
% 21.83/3.16    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 21.83/3.16    inference(ennf_transformation,[],[f12])).
% 21.83/3.16  fof(f12,axiom,(
% 21.83/3.16    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)))),
% 21.83/3.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_xboole_1)).
% 21.83/3.16  fof(f36,plain,(
% 21.83/3.16    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 21.83/3.16    inference(cnf_transformation,[],[f15])).
% 21.83/3.16  fof(f15,axiom,(
% 21.83/3.16    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 21.83/3.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 21.83/3.16  fof(f738,plain,(
% 21.83/3.16    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k3_xboole_0(X4,k3_xboole_0(X3,X4))) )),
% 21.83/3.16    inference(superposition,[],[f115,f38])).
% 21.83/3.16  fof(f38,plain,(
% 21.83/3.16    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 21.83/3.16    inference(cnf_transformation,[],[f2])).
% 21.83/3.16  fof(f2,axiom,(
% 21.83/3.16    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 21.83/3.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 21.83/3.16  fof(f115,plain,(
% 21.83/3.16    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X1)) )),
% 21.83/3.16    inference(unit_resulting_resolution,[],[f90,f45])).
% 21.83/3.16  fof(f90,plain,(
% 21.83/3.16    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 21.83/3.16    inference(superposition,[],[f82,f38])).
% 21.83/3.16  fof(f82,plain,(
% 21.83/3.16    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 21.83/3.16    inference(superposition,[],[f66,f40])).
% 21.83/3.16  fof(f40,plain,(
% 21.83/3.16    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 21.83/3.16    inference(cnf_transformation,[],[f8])).
% 21.83/3.16  fof(f8,axiom,(
% 21.83/3.16    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 21.83/3.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 21.83/3.16  fof(f66,plain,(
% 21.83/3.16    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 21.83/3.16    inference(superposition,[],[f36,f39])).
% 21.83/3.16  fof(f39,plain,(
% 21.83/3.16    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 21.83/3.16    inference(cnf_transformation,[],[f1])).
% 21.83/3.16  fof(f1,axiom,(
% 21.83/3.16    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 21.83/3.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 21.83/3.16  fof(f64514,plain,(
% 21.83/3.16    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k3_xboole_0(k4_xboole_0(k2_xboole_0(X0,X1),X1),k4_xboole_0(X0,X1))) )),
% 21.83/3.16    inference(unit_resulting_resolution,[],[f63016,f45])).
% 21.83/3.16  fof(f63016,plain,(
% 21.83/3.16    ( ! [X2,X1] : (r1_tarski(k4_xboole_0(k2_xboole_0(X2,X1),X1),k4_xboole_0(X2,X1))) )),
% 21.83/3.16    inference(superposition,[],[f61558,f39])).
% 21.83/3.16  fof(f61558,plain,(
% 21.83/3.16    ( ! [X62,X63] : (r1_tarski(k4_xboole_0(k2_xboole_0(X62,X63),X62),k4_xboole_0(X63,X62))) )),
% 21.83/3.16    inference(superposition,[],[f61419,f41])).
% 21.83/3.16  fof(f41,plain,(
% 21.83/3.16    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 21.83/3.16    inference(cnf_transformation,[],[f14])).
% 21.83/3.16  fof(f14,axiom,(
% 21.83/3.16    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 21.83/3.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 21.83/3.16  fof(f61419,plain,(
% 21.83/3.16    ( ! [X2,X1] : (r1_tarski(k4_xboole_0(k2_xboole_0(X2,X1),X2),X1)) )),
% 21.83/3.16    inference(superposition,[],[f61290,f39])).
% 21.83/3.16  fof(f61290,plain,(
% 21.83/3.16    ( ! [X8,X9] : (r1_tarski(k4_xboole_0(k2_xboole_0(X8,X9),X9),X8)) )),
% 21.83/3.16    inference(superposition,[],[f61074,f417])).
% 21.83/3.16  fof(f417,plain,(
% 21.83/3.16    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 21.83/3.16    inference(superposition,[],[f117,f38])).
% 21.83/3.16  fof(f117,plain,(
% 21.83/3.16    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 21.83/3.16    inference(unit_resulting_resolution,[],[f37,f45])).
% 21.83/3.16  fof(f37,plain,(
% 21.83/3.16    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 21.83/3.16    inference(cnf_transformation,[],[f13])).
% 21.83/3.16  fof(f13,axiom,(
% 21.83/3.16    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 21.83/3.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 21.83/3.16  fof(f61074,plain,(
% 21.83/3.16    ( ! [X68,X69,X67] : (r1_tarski(k3_xboole_0(k2_xboole_0(X69,X67),k4_xboole_0(X68,X67)),X69)) )),
% 21.83/3.16    inference(forward_demodulation,[],[f60970,f57])).
% 21.83/3.16  fof(f57,plain,(
% 21.83/3.16    ( ! [X0] : (k2_xboole_0(X0,o_0_0_xboole_0) = X0) )),
% 21.83/3.16    inference(definition_unfolding,[],[f35,f34])).
% 21.83/3.16  fof(f34,plain,(
% 21.83/3.16    k1_xboole_0 = o_0_0_xboole_0),
% 21.83/3.16    inference(cnf_transformation,[],[f3])).
% 21.83/3.16  fof(f3,axiom,(
% 21.83/3.16    k1_xboole_0 = o_0_0_xboole_0),
% 21.83/3.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).
% 21.83/3.16  fof(f35,plain,(
% 21.83/3.16    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 21.83/3.16    inference(cnf_transformation,[],[f7])).
% 21.83/3.16  fof(f7,axiom,(
% 21.83/3.16    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 21.83/3.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 21.83/3.16  fof(f60970,plain,(
% 21.83/3.16    ( ! [X68,X69,X67] : (r1_tarski(k3_xboole_0(k2_xboole_0(X69,X67),k4_xboole_0(X68,X67)),k2_xboole_0(X69,o_0_0_xboole_0))) )),
% 21.83/3.16    inference(superposition,[],[f1696,f8239])).
% 21.83/3.16  fof(f8239,plain,(
% 21.83/3.16    ( ! [X4,X3] : (o_0_0_xboole_0 = k3_xboole_0(X4,k4_xboole_0(X3,X4))) )),
% 21.83/3.16    inference(superposition,[],[f8212,f38])).
% 21.83/3.16  fof(f8212,plain,(
% 21.83/3.16    ( ! [X0,X1] : (o_0_0_xboole_0 = k3_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 21.83/3.16    inference(unit_resulting_resolution,[],[f8211,f59])).
% 21.83/3.16  fof(f59,plain,(
% 21.83/3.16    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = o_0_0_xboole_0) )),
% 21.83/3.16    inference(definition_unfolding,[],[f46,f34])).
% 21.83/3.16  fof(f46,plain,(
% 21.83/3.16    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 21.83/3.16    inference(cnf_transformation,[],[f27])).
% 21.83/3.16  fof(f27,plain,(
% 21.83/3.16    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 21.83/3.16    inference(nnf_transformation,[],[f5])).
% 21.83/3.16  fof(f5,axiom,(
% 21.83/3.16    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 21.83/3.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 21.83/3.16  fof(f8211,plain,(
% 21.83/3.16    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 21.83/3.16    inference(duplicate_literal_removal,[],[f8199])).
% 21.83/3.16  fof(f8199,plain,(
% 21.83/3.16    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1) | r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 21.83/3.16    inference(resolution,[],[f192,f43])).
% 21.83/3.16  fof(f43,plain,(
% 21.83/3.16    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 21.83/3.16    inference(cnf_transformation,[],[f26])).
% 21.83/3.16  fof(f26,plain,(
% 21.83/3.16    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 21.83/3.16    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f25])).
% 21.83/3.16  fof(f25,plain,(
% 21.83/3.16    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 21.83/3.16    introduced(choice_axiom,[])).
% 21.83/3.16  fof(f20,plain,(
% 21.83/3.16    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 21.83/3.16    inference(ennf_transformation,[],[f18])).
% 21.83/3.16  fof(f18,plain,(
% 21.83/3.16    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 21.83/3.16    inference(rectify,[],[f6])).
% 21.83/3.16  fof(f6,axiom,(
% 21.83/3.16    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 21.83/3.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 21.83/3.16  fof(f192,plain,(
% 21.83/3.16    ( ! [X2,X0,X1] : (~r2_hidden(sK2(k4_xboole_0(X0,X1),X2),X1) | r1_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 21.83/3.16    inference(resolution,[],[f61,f42])).
% 21.83/3.16  fof(f42,plain,(
% 21.83/3.16    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 21.83/3.16    inference(cnf_transformation,[],[f26])).
% 21.83/3.16  fof(f61,plain,(
% 21.83/3.16    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 21.83/3.16    inference(equality_resolution,[],[f52])).
% 21.83/3.16  fof(f52,plain,(
% 21.83/3.16    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 21.83/3.16    inference(cnf_transformation,[],[f32])).
% 21.83/3.16  fof(f32,plain,(
% 21.83/3.16    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 21.83/3.16    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).
% 21.83/3.16  fof(f31,plain,(
% 21.83/3.16    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 21.83/3.16    introduced(choice_axiom,[])).
% 21.83/3.16  fof(f30,plain,(
% 21.83/3.16    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 21.83/3.16    inference(rectify,[],[f29])).
% 21.83/3.16  fof(f29,plain,(
% 21.83/3.16    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 21.83/3.16    inference(flattening,[],[f28])).
% 21.83/3.16  fof(f28,plain,(
% 21.83/3.16    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 21.83/3.16    inference(nnf_transformation,[],[f4])).
% 21.83/3.16  fof(f4,axiom,(
% 21.83/3.16    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 21.83/3.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 21.83/3.16  fof(f1696,plain,(
% 21.83/3.16    ( ! [X4,X2,X3] : (r1_tarski(k3_xboole_0(k2_xboole_0(X2,X3),X4),k2_xboole_0(X2,k3_xboole_0(X3,X4)))) )),
% 21.83/3.16    inference(superposition,[],[f1164,f49])).
% 21.83/3.16  fof(f49,plain,(
% 21.83/3.16    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 21.83/3.16    inference(cnf_transformation,[],[f10])).
% 21.83/3.16  fof(f10,axiom,(
% 21.83/3.16    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 21.83/3.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_xboole_1)).
% 21.83/3.16  fof(f1164,plain,(
% 21.83/3.16    ( ! [X17,X15,X16] : (r1_tarski(k3_xboole_0(X15,X17),k3_xboole_0(X15,k2_xboole_0(X16,X17)))) )),
% 21.83/3.16    inference(superposition,[],[f66,f48])).
% 21.83/3.16  fof(f48,plain,(
% 21.83/3.16    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 21.83/3.16    inference(cnf_transformation,[],[f9])).
% 21.83/3.16  fof(f9,axiom,(
% 21.83/3.16    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 21.83/3.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).
% 21.83/3.16  fof(f33,plain,(
% 21.83/3.16    k4_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),
% 21.83/3.16    inference(cnf_transformation,[],[f24])).
% 21.83/3.16  fof(f24,plain,(
% 21.83/3.16    k4_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),
% 21.83/3.16    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f23])).
% 21.83/3.16  fof(f23,plain,(
% 21.83/3.16    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),X1) => k4_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),sK1)),
% 21.83/3.16    introduced(choice_axiom,[])).
% 21.83/3.16  fof(f19,plain,(
% 21.83/3.16    ? [X0,X1] : k4_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 21.83/3.16    inference(ennf_transformation,[],[f17])).
% 21.83/3.16  fof(f17,negated_conjecture,(
% 21.83/3.16    ~! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 21.83/3.16    inference(negated_conjecture,[],[f16])).
% 21.83/3.16  fof(f16,conjecture,(
% 21.83/3.16    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 21.83/3.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 21.83/3.16  % SZS output end Proof for theBenchmark
% 21.83/3.16  % (16604)------------------------------
% 21.83/3.16  % (16604)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.83/3.16  % (16604)Termination reason: Refutation
% 21.83/3.16  
% 21.83/3.16  % (16604)Memory used [KB]: 41321
% 21.83/3.16  % (16604)Time elapsed: 2.566 s
% 21.83/3.16  % (16604)------------------------------
% 21.83/3.16  % (16604)------------------------------
% 21.83/3.16  % (16564)Success in time 2.814 s
%------------------------------------------------------------------------------
