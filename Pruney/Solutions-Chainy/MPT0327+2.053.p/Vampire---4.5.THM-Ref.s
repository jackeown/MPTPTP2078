%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:56 EST 2020

% Result     : Theorem 2.59s
% Output     : Refutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 735 expanded)
%              Number of leaves         :   18 ( 180 expanded)
%              Depth                    :   19
%              Number of atoms          :  164 (1701 expanded)
%              Number of equality atoms :   73 ( 729 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f912,plain,(
    $false ),
    inference(subsumption_resolution,[],[f911,f408])).

fof(f408,plain,(
    sK1 != k2_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(backward_demodulation,[],[f46,f407])).

fof(f407,plain,(
    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f385,f301])).

fof(f301,plain,(
    ! [X2,X1] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1) ),
    inference(superposition,[],[f241,f284])).

fof(f284,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f273,f119])).

fof(f119,plain,(
    ! [X2] : k5_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f115,f50])).

fof(f50,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f115,plain,(
    ! [X2] : k2_xboole_0(X2,X2) = k5_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f53,f94])).

fof(f94,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f68,f79])).

fof(f79,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f273,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f241,f233])).

fof(f233,plain,(
    ! [X4,X3] : k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4))) ),
    inference(superposition,[],[f70,f153])).

fof(f153,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f150,f94])).

fof(f150,plain,(
    ! [X1] : k5_xboole_0(X1,X1) = k4_xboole_0(X1,X1) ),
    inference(superposition,[],[f54,f145])).

fof(f145,plain,(
    ! [X2] : k3_xboole_0(X2,X2) = X2 ),
    inference(superposition,[],[f136,f47])).

fof(f47,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f136,plain,(
    ! [X2] : k2_xboole_0(k3_xboole_0(X2,X2),k1_xboole_0) = X2 ),
    inference(superposition,[],[f55,f94])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f70,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f241,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f227,f117])).

fof(f117,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(forward_demodulation,[],[f114,f103])).

fof(f103,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(resolution,[],[f101,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f101,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f98,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
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

fof(f98,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(superposition,[],[f81,f94])).

fof(f81,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f114,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f53,f48])).

fof(f48,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f227,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f70,f153])).

fof(f385,plain,(
    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK0),sK1) ),
    inference(superposition,[],[f245,f173])).

fof(f173,plain,(
    sK1 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f87,f45])).

fof(f45,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f32])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(f87,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,X2)
      | k2_xboole_0(k1_tarski(X1),X2) = X2 ) ),
    inference(resolution,[],[f57,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f245,plain,(
    ! [X4,X3] : k4_xboole_0(X4,X3) = k5_xboole_0(X3,k2_xboole_0(X3,X4)) ),
    inference(superposition,[],[f241,f53])).

fof(f46,plain,(
    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f911,plain,(
    sK1 = k2_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f901,f292])).

fof(f292,plain,(
    ! [X2,X1] : k5_xboole_0(k5_xboole_0(X1,X2),X2) = X1 ),
    inference(superposition,[],[f284,f241])).

fof(f901,plain,(
    k2_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(superposition,[],[f53,f557])).

fof(f557,plain,(
    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,k1_tarski(sK0))) ),
    inference(superposition,[],[f199,f407])).

fof(f199,plain,(
    ! [X0,X1] : k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X0))) ),
    inference(resolution,[],[f90,f81])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(resolution,[],[f64,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:23:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (13416)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.49  % (13420)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (13419)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (13411)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (13409)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.55  % (13413)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (13406)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.57  % (13417)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.57  % (13431)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.57  % (13432)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.57  % (13423)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.58  % (13430)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.58  % (13426)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.58  % (13424)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.58  % (13410)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.58  % (13414)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.59  % (13407)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.59  % (13427)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.59  % (13412)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.60  % (13408)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.61  % (13427)Refutation not found, incomplete strategy% (13427)------------------------------
% 0.21/0.61  % (13427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.61  % (13427)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.61  
% 0.21/0.61  % (13427)Memory used [KB]: 10746
% 0.21/0.61  % (13427)Time elapsed: 0.166 s
% 0.21/0.61  % (13427)------------------------------
% 0.21/0.61  % (13427)------------------------------
% 0.21/0.61  % (13434)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.61  % (13421)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.62  % (13418)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.62  % (13425)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.62  % (13415)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.62  % (13405)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.63  % (13429)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.63  % (13433)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.91/0.65  % (13428)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 2.23/0.66  % (13422)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 2.59/0.71  % (13412)Refutation found. Thanks to Tanya!
% 2.59/0.71  % SZS status Theorem for theBenchmark
% 2.59/0.71  % SZS output start Proof for theBenchmark
% 2.59/0.71  fof(f912,plain,(
% 2.59/0.71    $false),
% 2.59/0.71    inference(subsumption_resolution,[],[f911,f408])).
% 2.59/0.71  fof(f408,plain,(
% 2.59/0.71    sK1 != k2_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 2.59/0.71    inference(backward_demodulation,[],[f46,f407])).
% 2.59/0.71  fof(f407,plain,(
% 2.59/0.71    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_tarski(sK0))),
% 2.59/0.71    inference(forward_demodulation,[],[f385,f301])).
% 2.59/0.71  fof(f301,plain,(
% 2.59/0.71    ( ! [X2,X1] : (k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)) )),
% 2.59/0.71    inference(superposition,[],[f241,f284])).
% 2.59/0.71  fof(f284,plain,(
% 2.59/0.71    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) )),
% 2.59/0.71    inference(forward_demodulation,[],[f273,f119])).
% 2.59/0.71  fof(f119,plain,(
% 2.59/0.71    ( ! [X2] : (k5_xboole_0(X2,k1_xboole_0) = X2) )),
% 2.59/0.71    inference(forward_demodulation,[],[f115,f50])).
% 2.59/0.71  fof(f50,plain,(
% 2.59/0.71    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.59/0.71    inference(cnf_transformation,[],[f24])).
% 2.59/0.71  fof(f24,plain,(
% 2.59/0.71    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.59/0.71    inference(rectify,[],[f2])).
% 2.59/0.71  fof(f2,axiom,(
% 2.59/0.71    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.59/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.59/0.71  fof(f115,plain,(
% 2.59/0.71    ( ! [X2] : (k2_xboole_0(X2,X2) = k5_xboole_0(X2,k1_xboole_0)) )),
% 2.59/0.71    inference(superposition,[],[f53,f94])).
% 2.59/0.71  fof(f94,plain,(
% 2.59/0.71    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.59/0.71    inference(resolution,[],[f68,f79])).
% 2.59/0.71  fof(f79,plain,(
% 2.59/0.71    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.59/0.71    inference(equality_resolution,[],[f59])).
% 2.59/0.71  fof(f59,plain,(
% 2.59/0.71    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.59/0.71    inference(cnf_transformation,[],[f35])).
% 2.59/0.71  fof(f35,plain,(
% 2.59/0.71    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.59/0.71    inference(flattening,[],[f34])).
% 2.59/0.71  fof(f34,plain,(
% 2.59/0.71    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.59/0.71    inference(nnf_transformation,[],[f4])).
% 2.59/0.71  fof(f4,axiom,(
% 2.59/0.71    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.59/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.59/0.71  fof(f68,plain,(
% 2.59/0.71    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 2.59/0.71    inference(cnf_transformation,[],[f41])).
% 2.59/0.71  fof(f41,plain,(
% 2.59/0.71    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.59/0.71    inference(nnf_transformation,[],[f5])).
% 2.59/0.71  fof(f5,axiom,(
% 2.59/0.71    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.59/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.59/0.71  fof(f53,plain,(
% 2.59/0.71    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.59/0.71    inference(cnf_transformation,[],[f13])).
% 2.59/0.71  fof(f13,axiom,(
% 2.59/0.71    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.59/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.59/0.71  fof(f273,plain,(
% 2.59/0.71    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2))) )),
% 2.59/0.71    inference(superposition,[],[f241,f233])).
% 2.59/0.71  fof(f233,plain,(
% 2.59/0.71    ( ! [X4,X3] : (k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4)))) )),
% 2.59/0.71    inference(superposition,[],[f70,f153])).
% 2.59/0.71  fof(f153,plain,(
% 2.59/0.71    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) )),
% 2.59/0.71    inference(forward_demodulation,[],[f150,f94])).
% 2.59/0.71  fof(f150,plain,(
% 2.59/0.71    ( ! [X1] : (k5_xboole_0(X1,X1) = k4_xboole_0(X1,X1)) )),
% 2.59/0.71    inference(superposition,[],[f54,f145])).
% 2.59/0.71  fof(f145,plain,(
% 2.59/0.71    ( ! [X2] : (k3_xboole_0(X2,X2) = X2) )),
% 2.59/0.71    inference(superposition,[],[f136,f47])).
% 2.59/0.71  fof(f47,plain,(
% 2.59/0.71    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.59/0.71    inference(cnf_transformation,[],[f8])).
% 2.59/0.71  fof(f8,axiom,(
% 2.59/0.71    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.59/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 2.59/0.71  fof(f136,plain,(
% 2.59/0.71    ( ! [X2] : (k2_xboole_0(k3_xboole_0(X2,X2),k1_xboole_0) = X2) )),
% 2.59/0.71    inference(superposition,[],[f55,f94])).
% 2.59/0.71  fof(f55,plain,(
% 2.59/0.71    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 2.59/0.71    inference(cnf_transformation,[],[f10])).
% 2.59/0.71  fof(f10,axiom,(
% 2.59/0.71    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 2.59/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 2.59/0.71  fof(f54,plain,(
% 2.59/0.71    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.59/0.71    inference(cnf_transformation,[],[f6])).
% 2.59/0.71  fof(f6,axiom,(
% 2.59/0.71    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.59/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.59/0.71  fof(f70,plain,(
% 2.59/0.71    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.59/0.71    inference(cnf_transformation,[],[f12])).
% 2.59/0.71  fof(f12,axiom,(
% 2.59/0.71    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.59/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.59/0.71  fof(f241,plain,(
% 2.59/0.71    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.59/0.71    inference(forward_demodulation,[],[f227,f117])).
% 2.59/0.71  fof(f117,plain,(
% 2.59/0.71    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 2.59/0.71    inference(forward_demodulation,[],[f114,f103])).
% 2.59/0.71  fof(f103,plain,(
% 2.59/0.71    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) )),
% 2.59/0.71    inference(resolution,[],[f101,f57])).
% 2.59/0.71  fof(f57,plain,(
% 2.59/0.71    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.59/0.71    inference(cnf_transformation,[],[f28])).
% 2.59/0.71  fof(f28,plain,(
% 2.59/0.71    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.59/0.71    inference(ennf_transformation,[],[f7])).
% 2.59/0.71  fof(f7,axiom,(
% 2.59/0.71    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.59/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.59/0.71  fof(f101,plain,(
% 2.59/0.71    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.59/0.71    inference(resolution,[],[f98,f62])).
% 2.59/0.71  fof(f62,plain,(
% 2.59/0.71    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.59/0.71    inference(cnf_transformation,[],[f39])).
% 2.59/0.71  fof(f39,plain,(
% 2.59/0.71    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.59/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f37,f38])).
% 2.59/0.71  fof(f38,plain,(
% 2.59/0.71    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 2.59/0.71    introduced(choice_axiom,[])).
% 2.59/0.71  fof(f37,plain,(
% 2.59/0.71    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.59/0.71    inference(rectify,[],[f36])).
% 2.59/0.71  fof(f36,plain,(
% 2.59/0.71    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.59/0.71    inference(nnf_transformation,[],[f29])).
% 2.59/0.71  fof(f29,plain,(
% 2.59/0.71    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.59/0.71    inference(ennf_transformation,[],[f1])).
% 2.59/0.71  fof(f1,axiom,(
% 2.59/0.71    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.59/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.59/0.71  fof(f98,plain,(
% 2.59/0.71    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 2.59/0.71    inference(superposition,[],[f81,f94])).
% 2.59/0.71  fof(f81,plain,(
% 2.59/0.71    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 2.59/0.71    inference(equality_resolution,[],[f76])).
% 2.59/0.71  fof(f76,plain,(
% 2.59/0.71    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 2.59/0.71    inference(cnf_transformation,[],[f44])).
% 2.59/0.71  fof(f44,plain,(
% 2.59/0.71    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 2.59/0.71    inference(flattening,[],[f43])).
% 2.59/0.71  fof(f43,plain,(
% 2.59/0.71    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 2.59/0.71    inference(nnf_transformation,[],[f21])).
% 2.59/0.71  fof(f21,axiom,(
% 2.59/0.71    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 2.59/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 2.59/0.71  fof(f114,plain,(
% 2.59/0.71    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,X1)) )),
% 2.59/0.71    inference(superposition,[],[f53,f48])).
% 2.59/0.71  fof(f48,plain,(
% 2.59/0.71    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.59/0.71    inference(cnf_transformation,[],[f9])).
% 2.59/0.71  fof(f9,axiom,(
% 2.59/0.71    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.59/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 2.59/0.71  fof(f227,plain,(
% 2.59/0.71    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.59/0.71    inference(superposition,[],[f70,f153])).
% 2.59/0.71  fof(f385,plain,(
% 2.59/0.71    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k1_tarski(sK0),sK1)),
% 2.59/0.71    inference(superposition,[],[f245,f173])).
% 2.59/0.71  fof(f173,plain,(
% 2.59/0.71    sK1 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 2.59/0.71    inference(resolution,[],[f87,f45])).
% 2.59/0.71  fof(f45,plain,(
% 2.59/0.71    r2_hidden(sK0,sK1)),
% 2.59/0.71    inference(cnf_transformation,[],[f33])).
% 2.59/0.71  fof(f33,plain,(
% 2.59/0.71    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1)),
% 2.59/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f32])).
% 2.59/0.71  fof(f32,plain,(
% 2.59/0.71    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1))),
% 2.59/0.71    introduced(choice_axiom,[])).
% 2.59/0.71  fof(f26,plain,(
% 2.59/0.71    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 2.59/0.71    inference(ennf_transformation,[],[f23])).
% 2.59/0.71  fof(f23,negated_conjecture,(
% 2.59/0.71    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 2.59/0.71    inference(negated_conjecture,[],[f22])).
% 2.59/0.71  fof(f22,conjecture,(
% 2.59/0.71    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 2.59/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).
% 2.59/0.71  fof(f87,plain,(
% 2.59/0.71    ( ! [X2,X1] : (~r2_hidden(X1,X2) | k2_xboole_0(k1_tarski(X1),X2) = X2) )),
% 2.59/0.71    inference(resolution,[],[f57,f66])).
% 2.59/0.71  fof(f66,plain,(
% 2.59/0.71    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.59/0.71    inference(cnf_transformation,[],[f40])).
% 2.59/0.71  fof(f40,plain,(
% 2.59/0.71    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.59/0.71    inference(nnf_transformation,[],[f18])).
% 2.59/0.71  fof(f18,axiom,(
% 2.59/0.71    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.59/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 2.59/0.71  fof(f245,plain,(
% 2.59/0.71    ( ! [X4,X3] : (k4_xboole_0(X4,X3) = k5_xboole_0(X3,k2_xboole_0(X3,X4))) )),
% 2.59/0.71    inference(superposition,[],[f241,f53])).
% 2.59/0.71  fof(f46,plain,(
% 2.59/0.71    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 2.59/0.71    inference(cnf_transformation,[],[f33])).
% 2.59/0.71  fof(f911,plain,(
% 2.59/0.71    sK1 = k2_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 2.59/0.71    inference(forward_demodulation,[],[f901,f292])).
% 2.59/0.71  fof(f292,plain,(
% 2.59/0.71    ( ! [X2,X1] : (k5_xboole_0(k5_xboole_0(X1,X2),X2) = X1) )),
% 2.59/0.71    inference(superposition,[],[f284,f241])).
% 2.59/0.71  fof(f901,plain,(
% 2.59/0.71    k2_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(k5_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 2.59/0.71    inference(superposition,[],[f53,f557])).
% 2.59/0.71  fof(f557,plain,(
% 2.59/0.71    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,k1_tarski(sK0)))),
% 2.59/0.71    inference(superposition,[],[f199,f407])).
% 2.59/0.71  fof(f199,plain,(
% 2.59/0.71    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X0)))) )),
% 2.59/0.71    inference(resolution,[],[f90,f81])).
% 2.59/0.71  fof(f90,plain,(
% 2.59/0.71    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)) )),
% 2.59/0.71    inference(resolution,[],[f64,f56])).
% 2.59/0.71  fof(f56,plain,(
% 2.59/0.71    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.59/0.71    inference(cnf_transformation,[],[f27])).
% 2.59/0.71  fof(f27,plain,(
% 2.59/0.71    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 2.59/0.71    inference(ennf_transformation,[],[f19])).
% 2.59/0.71  fof(f19,axiom,(
% 2.59/0.71    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 2.59/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 2.59/0.71  fof(f64,plain,(
% 2.59/0.71    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 2.59/0.71    inference(cnf_transformation,[],[f30])).
% 2.59/0.71  fof(f30,plain,(
% 2.59/0.71    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 2.59/0.71    inference(ennf_transformation,[],[f25])).
% 2.59/0.71  fof(f25,plain,(
% 2.59/0.71    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 2.59/0.71    inference(unused_predicate_definition_removal,[],[f11])).
% 2.59/0.71  fof(f11,axiom,(
% 2.59/0.71    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.59/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 2.59/0.71  % SZS output end Proof for theBenchmark
% 2.59/0.71  % (13412)------------------------------
% 2.59/0.71  % (13412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.59/0.71  % (13412)Termination reason: Refutation
% 2.59/0.71  
% 2.59/0.71  % (13412)Memory used [KB]: 6652
% 2.59/0.71  % (13412)Time elapsed: 0.271 s
% 2.59/0.71  % (13412)------------------------------
% 2.59/0.71  % (13412)------------------------------
% 2.59/0.72  % (13404)Success in time 0.344 s
%------------------------------------------------------------------------------
