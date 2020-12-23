%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:35 EST 2020

% Result     : Theorem 1.92s
% Output     : Refutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 163 expanded)
%              Number of leaves         :   18 (  48 expanded)
%              Depth                    :   18
%              Number of atoms          :  169 ( 366 expanded)
%              Number of equality atoms :   36 (  79 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3674,plain,(
    $false ),
    inference(resolution,[],[f3661,f66])).

fof(f66,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f47,f34])).

fof(f34,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
      & r1_xboole_0(sK2,sK1)
      & r2_hidden(sK3,sK2)
      & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f3661,plain,(
    ~ r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f3630,f1621])).

fof(f1621,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | ~ r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f254,f35])).

fof(f35,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f254,plain,(
    ! [X10,X11,X9] :
      ( r1_xboole_0(k2_xboole_0(X10,X11),X9)
      | ~ r1_xboole_0(X9,X11)
      | ~ r1_xboole_0(X9,X10) ) ),
    inference(resolution,[],[f53,f47])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f3630,plain,(
    r1_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f3582,f70])).

fof(f70,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(resolution,[],[f48,f36])).

fof(f36,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f3582,plain,(
    r1_xboole_0(k4_xboole_0(sK1,k1_xboole_0),sK0) ),
    inference(superposition,[],[f336,f3546])).

fof(f3546,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f3529,f404])).

fof(f404,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f328,f71])).

fof(f71,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1) ),
    inference(resolution,[],[f48,f67])).

fof(f67,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f47,f36])).

fof(f328,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f61,f70])).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f39,f42,f42])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f3529,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f218,f3511])).

fof(f3511,plain,(
    ! [X8] : k4_xboole_0(X8,k4_xboole_0(X8,sK1)) = k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(resolution,[],[f499,f358])).

fof(f358,plain,(
    ! [X53] : r1_xboole_0(sK2,k4_xboole_0(X53,k4_xboole_0(X53,sK1))) ),
    inference(superposition,[],[f140,f61])).

fof(f140,plain,(
    ! [X1] : r1_xboole_0(sK2,k4_xboole_0(sK1,X1)) ),
    inference(resolution,[],[f124,f47])).

fof(f124,plain,(
    ! [X0] : r1_xboole_0(k4_xboole_0(sK1,X0),sK2) ),
    inference(resolution,[],[f105,f38])).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f105,plain,(
    ! [X4] :
      ( ~ r1_tarski(X4,sK1)
      | r1_xboole_0(X4,sK2) ) ),
    inference(superposition,[],[f57,f72])).

fof(f72,plain,(
    sK1 = k4_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f48,f66])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f499,plain,(
    ! [X3] :
      ( ~ r1_xboole_0(sK2,X3)
      | k4_xboole_0(X3,k2_enumset1(sK3,sK3,sK3,sK3)) = X3 ) ),
    inference(resolution,[],[f64,f111])).

fof(f111,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,X0)
      | ~ r1_xboole_0(sK2,X0) ) ),
    inference(resolution,[],[f45,f33])).

fof(f33,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(rectify,[],[f3])).

fof(f3,axiom,(
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

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f51,f59])).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f37,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f218,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))) ),
    inference(resolution,[],[f63,f60])).

fof(f60,plain,(
    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f32,f42,f59])).

fof(f32,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f27])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f46,f42])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f336,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X1) ),
    inference(superposition,[],[f62,f61])).

fof(f62,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X1) ),
    inference(definition_unfolding,[],[f40,f42])).

fof(f40,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:40:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (4204)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.46  % (4212)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (4202)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (4214)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.47  % (4198)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (4197)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (4207)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (4201)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (4199)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (4210)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (4203)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (4208)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (4209)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (4205)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (4206)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (4200)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.50  % (4211)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.52  % (4213)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.92/0.60  % (4198)Refutation found. Thanks to Tanya!
% 1.92/0.60  % SZS status Theorem for theBenchmark
% 1.92/0.60  % SZS output start Proof for theBenchmark
% 1.92/0.60  fof(f3674,plain,(
% 1.92/0.60    $false),
% 1.92/0.60    inference(resolution,[],[f3661,f66])).
% 1.92/0.60  fof(f66,plain,(
% 1.92/0.60    r1_xboole_0(sK1,sK2)),
% 1.92/0.60    inference(resolution,[],[f47,f34])).
% 1.92/0.60  fof(f34,plain,(
% 1.92/0.60    r1_xboole_0(sK2,sK1)),
% 1.92/0.60    inference(cnf_transformation,[],[f27])).
% 1.92/0.60  fof(f27,plain,(
% 1.92/0.60    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.92/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f26])).
% 1.92/0.60  fof(f26,plain,(
% 1.92/0.60    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 1.92/0.60    introduced(choice_axiom,[])).
% 1.92/0.60  fof(f20,plain,(
% 1.92/0.60    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 1.92/0.60    inference(flattening,[],[f19])).
% 1.92/0.60  fof(f19,plain,(
% 1.92/0.60    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 1.92/0.60    inference(ennf_transformation,[],[f17])).
% 1.92/0.60  fof(f17,negated_conjecture,(
% 1.92/0.60    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.92/0.60    inference(negated_conjecture,[],[f16])).
% 1.92/0.60  fof(f16,conjecture,(
% 1.92/0.60    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.92/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 1.92/0.60  fof(f47,plain,(
% 1.92/0.60    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.92/0.60    inference(cnf_transformation,[],[f23])).
% 1.92/0.60  fof(f23,plain,(
% 1.92/0.60    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.92/0.60    inference(ennf_transformation,[],[f2])).
% 1.92/0.60  fof(f2,axiom,(
% 1.92/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.92/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.92/0.60  fof(f3661,plain,(
% 1.92/0.60    ~r1_xboole_0(sK1,sK2)),
% 1.92/0.60    inference(resolution,[],[f3630,f1621])).
% 1.92/0.60  fof(f1621,plain,(
% 1.92/0.60    ~r1_xboole_0(sK1,sK0) | ~r1_xboole_0(sK1,sK2)),
% 1.92/0.60    inference(resolution,[],[f254,f35])).
% 1.92/0.60  fof(f35,plain,(
% 1.92/0.60    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 1.92/0.60    inference(cnf_transformation,[],[f27])).
% 1.92/0.60  fof(f254,plain,(
% 1.92/0.60    ( ! [X10,X11,X9] : (r1_xboole_0(k2_xboole_0(X10,X11),X9) | ~r1_xboole_0(X9,X11) | ~r1_xboole_0(X9,X10)) )),
% 1.92/0.60    inference(resolution,[],[f53,f47])).
% 1.92/0.60  fof(f53,plain,(
% 1.92/0.60    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 1.92/0.60    inference(cnf_transformation,[],[f24])).
% 1.92/0.60  fof(f24,plain,(
% 1.92/0.60    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.92/0.60    inference(ennf_transformation,[],[f9])).
% 1.92/0.60  fof(f9,axiom,(
% 1.92/0.60    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.92/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.92/0.60  fof(f3630,plain,(
% 1.92/0.60    r1_xboole_0(sK1,sK0)),
% 1.92/0.60    inference(forward_demodulation,[],[f3582,f70])).
% 1.92/0.60  fof(f70,plain,(
% 1.92/0.60    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.92/0.60    inference(resolution,[],[f48,f36])).
% 1.92/0.60  fof(f36,plain,(
% 1.92/0.60    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.92/0.60    inference(cnf_transformation,[],[f8])).
% 1.92/0.60  fof(f8,axiom,(
% 1.92/0.60    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.92/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.92/0.60  fof(f48,plain,(
% 1.92/0.60    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.92/0.60    inference(cnf_transformation,[],[f30])).
% 1.92/0.60  fof(f30,plain,(
% 1.92/0.60    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.92/0.60    inference(nnf_transformation,[],[f10])).
% 1.92/0.60  fof(f10,axiom,(
% 1.92/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.92/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.92/0.60  fof(f3582,plain,(
% 1.92/0.60    r1_xboole_0(k4_xboole_0(sK1,k1_xboole_0),sK0)),
% 1.92/0.60    inference(superposition,[],[f336,f3546])).
% 1.92/0.60  fof(f3546,plain,(
% 1.92/0.60    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.92/0.60    inference(forward_demodulation,[],[f3529,f404])).
% 1.92/0.60  fof(f404,plain,(
% 1.92/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.92/0.60    inference(forward_demodulation,[],[f328,f71])).
% 1.92/0.60  fof(f71,plain,(
% 1.92/0.60    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)) )),
% 1.92/0.60    inference(resolution,[],[f48,f67])).
% 1.92/0.60  fof(f67,plain,(
% 1.92/0.60    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.92/0.60    inference(resolution,[],[f47,f36])).
% 1.92/0.60  fof(f328,plain,(
% 1.92/0.60    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 1.92/0.60    inference(superposition,[],[f61,f70])).
% 1.92/0.60  fof(f61,plain,(
% 1.92/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.92/0.60    inference(definition_unfolding,[],[f39,f42,f42])).
% 1.92/0.60  fof(f42,plain,(
% 1.92/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.92/0.60    inference(cnf_transformation,[],[f7])).
% 1.92/0.60  fof(f7,axiom,(
% 1.92/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.92/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.92/0.60  fof(f39,plain,(
% 1.92/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.92/0.60    inference(cnf_transformation,[],[f1])).
% 1.92/0.60  fof(f1,axiom,(
% 1.92/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.92/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.92/0.60  fof(f3529,plain,(
% 1.92/0.60    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 1.92/0.60    inference(backward_demodulation,[],[f218,f3511])).
% 1.92/0.60  fof(f3511,plain,(
% 1.92/0.60    ( ! [X8] : (k4_xboole_0(X8,k4_xboole_0(X8,sK1)) = k4_xboole_0(k4_xboole_0(X8,k4_xboole_0(X8,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))) )),
% 1.92/0.60    inference(resolution,[],[f499,f358])).
% 1.92/0.60  fof(f358,plain,(
% 1.92/0.60    ( ! [X53] : (r1_xboole_0(sK2,k4_xboole_0(X53,k4_xboole_0(X53,sK1)))) )),
% 1.92/0.60    inference(superposition,[],[f140,f61])).
% 1.92/0.60  fof(f140,plain,(
% 1.92/0.60    ( ! [X1] : (r1_xboole_0(sK2,k4_xboole_0(sK1,X1))) )),
% 1.92/0.60    inference(resolution,[],[f124,f47])).
% 1.92/0.60  fof(f124,plain,(
% 1.92/0.60    ( ! [X0] : (r1_xboole_0(k4_xboole_0(sK1,X0),sK2)) )),
% 1.92/0.60    inference(resolution,[],[f105,f38])).
% 1.92/0.60  fof(f38,plain,(
% 1.92/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.92/0.60    inference(cnf_transformation,[],[f6])).
% 1.92/0.60  fof(f6,axiom,(
% 1.92/0.60    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.92/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.92/0.60  fof(f105,plain,(
% 1.92/0.60    ( ! [X4] : (~r1_tarski(X4,sK1) | r1_xboole_0(X4,sK2)) )),
% 1.92/0.60    inference(superposition,[],[f57,f72])).
% 1.92/0.60  fof(f72,plain,(
% 1.92/0.60    sK1 = k4_xboole_0(sK1,sK2)),
% 1.92/0.60    inference(resolution,[],[f48,f66])).
% 1.92/0.60  fof(f57,plain,(
% 1.92/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 1.92/0.60    inference(cnf_transformation,[],[f25])).
% 1.92/0.60  fof(f25,plain,(
% 1.92/0.60    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.92/0.60    inference(ennf_transformation,[],[f4])).
% 1.92/0.61  fof(f4,axiom,(
% 1.92/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.92/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.92/0.61  fof(f499,plain,(
% 1.92/0.61    ( ! [X3] : (~r1_xboole_0(sK2,X3) | k4_xboole_0(X3,k2_enumset1(sK3,sK3,sK3,sK3)) = X3) )),
% 1.92/0.61    inference(resolution,[],[f64,f111])).
% 1.92/0.61  fof(f111,plain,(
% 1.92/0.61    ( ! [X0] : (~r2_hidden(sK3,X0) | ~r1_xboole_0(sK2,X0)) )),
% 1.92/0.61    inference(resolution,[],[f45,f33])).
% 1.92/0.61  fof(f33,plain,(
% 1.92/0.61    r2_hidden(sK3,sK2)),
% 1.92/0.61    inference(cnf_transformation,[],[f27])).
% 1.92/0.61  fof(f45,plain,(
% 1.92/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 1.92/0.61    inference(cnf_transformation,[],[f29])).
% 1.92/0.61  fof(f29,plain,(
% 1.92/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.92/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f28])).
% 1.92/0.61  fof(f28,plain,(
% 1.92/0.61    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.92/0.61    introduced(choice_axiom,[])).
% 1.92/0.61  fof(f21,plain,(
% 1.92/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.92/0.61    inference(ennf_transformation,[],[f18])).
% 1.92/0.61  fof(f18,plain,(
% 1.92/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.92/0.61    inference(rectify,[],[f3])).
% 1.92/0.61  fof(f3,axiom,(
% 1.92/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.92/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.92/0.61  fof(f64,plain,(
% 1.92/0.61    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) = X0) )),
% 1.92/0.61    inference(definition_unfolding,[],[f51,f59])).
% 1.92/0.61  fof(f59,plain,(
% 1.92/0.61    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.92/0.61    inference(definition_unfolding,[],[f37,f58])).
% 1.92/0.61  fof(f58,plain,(
% 1.92/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.92/0.61    inference(definition_unfolding,[],[f41,f52])).
% 1.92/0.61  fof(f52,plain,(
% 1.92/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.92/0.61    inference(cnf_transformation,[],[f14])).
% 1.92/0.61  fof(f14,axiom,(
% 1.92/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.92/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.92/0.61  fof(f41,plain,(
% 1.92/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.92/0.61    inference(cnf_transformation,[],[f13])).
% 1.92/0.61  fof(f13,axiom,(
% 1.92/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.92/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.92/0.61  fof(f37,plain,(
% 1.92/0.61    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.92/0.61    inference(cnf_transformation,[],[f12])).
% 1.92/0.61  fof(f12,axiom,(
% 1.92/0.61    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.92/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.92/0.61  fof(f51,plain,(
% 1.92/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) )),
% 1.92/0.61    inference(cnf_transformation,[],[f31])).
% 1.92/0.61  fof(f31,plain,(
% 1.92/0.61    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.92/0.61    inference(nnf_transformation,[],[f15])).
% 1.92/0.61  fof(f15,axiom,(
% 1.92/0.61    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.92/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.92/0.61  fof(f218,plain,(
% 1.92/0.61    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)))),
% 1.92/0.61    inference(resolution,[],[f63,f60])).
% 1.92/0.61  fof(f60,plain,(
% 1.92/0.61    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))),
% 1.92/0.61    inference(definition_unfolding,[],[f32,f42,f59])).
% 1.92/0.61  fof(f32,plain,(
% 1.92/0.61    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.92/0.61    inference(cnf_transformation,[],[f27])).
% 1.92/0.61  fof(f63,plain,(
% 1.92/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 1.92/0.61    inference(definition_unfolding,[],[f46,f42])).
% 1.92/0.61  fof(f46,plain,(
% 1.92/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.92/0.61    inference(cnf_transformation,[],[f22])).
% 1.92/0.61  fof(f22,plain,(
% 1.92/0.61    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.92/0.61    inference(ennf_transformation,[],[f5])).
% 1.92/0.61  fof(f5,axiom,(
% 1.92/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.92/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.92/0.61  fof(f336,plain,(
% 1.92/0.61    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))),X1)) )),
% 1.92/0.61    inference(superposition,[],[f62,f61])).
% 1.92/0.61  fof(f62,plain,(
% 1.92/0.61    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X1)) )),
% 1.92/0.61    inference(definition_unfolding,[],[f40,f42])).
% 1.92/0.61  fof(f40,plain,(
% 1.92/0.61    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 1.92/0.61    inference(cnf_transformation,[],[f11])).
% 1.92/0.61  fof(f11,axiom,(
% 1.92/0.61    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)),
% 1.92/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_xboole_1)).
% 1.92/0.61  % SZS output end Proof for theBenchmark
% 1.92/0.61  % (4198)------------------------------
% 1.92/0.61  % (4198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.92/0.61  % (4198)Termination reason: Refutation
% 1.92/0.61  
% 1.92/0.61  % (4198)Memory used [KB]: 3198
% 1.92/0.61  % (4198)Time elapsed: 0.167 s
% 1.92/0.61  % (4198)------------------------------
% 1.92/0.61  % (4198)------------------------------
% 1.92/0.61  % (4196)Success in time 0.247 s
%------------------------------------------------------------------------------
