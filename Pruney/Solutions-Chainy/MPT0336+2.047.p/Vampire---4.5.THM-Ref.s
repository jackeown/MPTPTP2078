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
% DateTime   : Thu Dec  3 12:43:29 EST 2020

% Result     : Theorem 2.98s
% Output     : Refutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 215 expanded)
%              Number of leaves         :   19 (  66 expanded)
%              Depth                    :   21
%              Number of atoms          :  173 ( 422 expanded)
%              Number of equality atoms :   54 ( 152 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7098,plain,(
    $false ),
    inference(subsumption_resolution,[],[f7097,f92])).

fof(f92,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f85,f39])).

fof(f39,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f85,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(resolution,[],[f67,f38])).

fof(f38,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f52,f46])).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f7097,plain,(
    k1_xboole_0 != k4_xboole_0(sK1,sK1) ),
    inference(forward_demodulation,[],[f7046,f294])).

fof(f294,plain,(
    sK1 = k4_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f274,f277])).

fof(f277,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f261,f92])).

fof(f261,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[],[f61,f39])).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f274,plain,(
    k4_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f61,f90])).

fof(f90,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f67,f71])).

fof(f71,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(resolution,[],[f51,f36])).

fof(f36,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f29])).

fof(f29,plain,
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

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f7046,plain,(
    k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f566,f2470])).

fof(f2470,plain,(
    ! [X72] : k4_xboole_0(sK1,k4_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,X72)))) = k4_xboole_0(sK1,k4_xboole_0(sK1,X72)) ),
    inference(resolution,[],[f69,f213])).

fof(f213,plain,(
    r1_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f209,f51])).

fof(f209,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f204])).

fof(f204,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f66,f181])).

fof(f181,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f180,f39])).

fof(f180,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f174,f92])).

fof(f174,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)))) ),
    inference(resolution,[],[f170,f36])).

fof(f170,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(sK2,X0)
      | k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) ) ),
    inference(resolution,[],[f160,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,X0)
      | ~ r1_xboole_0(sK2,X0) ) ),
    inference(resolution,[],[f49,f35])).

fof(f35,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f160,plain,(
    ! [X0] :
      ( r2_hidden(sK3,X0)
      | k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0)))) ) ),
    inference(forward_demodulation,[],[f158,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(definition_unfolding,[],[f55,f46,f46,f46,f46])).

fof(f55,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f158,plain,(
    ! [X0] :
      ( r2_hidden(sK3,X0)
      | k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X0)) ) ),
    inference(resolution,[],[f153,f67])).

fof(f153,plain,(
    ! [X0] :
      ( r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X0)
      | r2_hidden(sK3,X0) ) ),
    inference(resolution,[],[f82,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f50,f60])).

fof(f60,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f82,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),X0)
      | r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X0) ) ),
    inference(resolution,[],[f57,f63])).

fof(f63,plain,(
    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3)) ),
    inference(definition_unfolding,[],[f34,f46,f60])).

fof(f34,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f30])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f46])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))) = k4_xboole_0(X0,k4_xboole_0(X0,X2)) ) ),
    inference(definition_unfolding,[],[f56,f46,f59,f46])).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f43,f58])).

fof(f43,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

fof(f566,plain,(
    k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)))) ),
    inference(resolution,[],[f403,f62])).

fof(f62,plain,(
    ~ r1_xboole_0(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1) ),
    inference(definition_unfolding,[],[f37,f59])).

fof(f37,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f403,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(X2,X3)
      | k1_xboole_0 != k4_xboole_0(X3,k4_xboole_0(X3,X2)) ) ),
    inference(superposition,[],[f66,f64])).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f42,f46,f46])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:23:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.46  % (12168)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (12177)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.47  % (12173)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.47  % (12175)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.47  % (12169)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (12167)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (12170)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (12165)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (12181)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.48  % (12166)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (12172)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.50  % (12163)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.50  % (12164)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.50  % (12174)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.51  % (12178)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.51  % (12180)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.51  % (12179)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.52  % (12171)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 2.98/0.75  % (12178)Refutation found. Thanks to Tanya!
% 2.98/0.75  % SZS status Theorem for theBenchmark
% 2.98/0.75  % SZS output start Proof for theBenchmark
% 2.98/0.75  fof(f7098,plain,(
% 2.98/0.75    $false),
% 2.98/0.75    inference(subsumption_resolution,[],[f7097,f92])).
% 2.98/0.75  fof(f92,plain,(
% 2.98/0.75    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.98/0.75    inference(forward_demodulation,[],[f85,f39])).
% 2.98/0.75  fof(f39,plain,(
% 2.98/0.75    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.98/0.75    inference(cnf_transformation,[],[f7])).
% 2.98/0.75  fof(f7,axiom,(
% 2.98/0.75    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.98/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 2.98/0.75  fof(f85,plain,(
% 2.98/0.75    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 2.98/0.75    inference(resolution,[],[f67,f38])).
% 2.98/0.75  fof(f38,plain,(
% 2.98/0.75    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.98/0.75    inference(cnf_transformation,[],[f10])).
% 2.98/0.75  fof(f10,axiom,(
% 2.98/0.75    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.98/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 2.98/0.75  fof(f67,plain,(
% 2.98/0.75    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.98/0.75    inference(definition_unfolding,[],[f52,f46])).
% 2.98/0.75  fof(f46,plain,(
% 2.98/0.75    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.98/0.75    inference(cnf_transformation,[],[f8])).
% 2.98/0.75  fof(f8,axiom,(
% 2.98/0.75    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.98/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.98/0.75  fof(f52,plain,(
% 2.98/0.75    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.98/0.75    inference(cnf_transformation,[],[f33])).
% 2.98/0.75  fof(f33,plain,(
% 2.98/0.75    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.98/0.75    inference(nnf_transformation,[],[f2])).
% 2.98/0.75  fof(f2,axiom,(
% 2.98/0.75    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.98/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.98/0.75  fof(f7097,plain,(
% 2.98/0.75    k1_xboole_0 != k4_xboole_0(sK1,sK1)),
% 2.98/0.75    inference(forward_demodulation,[],[f7046,f294])).
% 2.98/0.75  fof(f294,plain,(
% 2.98/0.75    sK1 = k4_xboole_0(sK1,sK2)),
% 2.98/0.75    inference(forward_demodulation,[],[f274,f277])).
% 2.98/0.75  fof(f277,plain,(
% 2.98/0.75    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.98/0.75    inference(forward_demodulation,[],[f261,f92])).
% 2.98/0.75  fof(f261,plain,(
% 2.98/0.75    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 2.98/0.75    inference(superposition,[],[f61,f39])).
% 2.98/0.75  fof(f61,plain,(
% 2.98/0.75    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 2.98/0.75    inference(definition_unfolding,[],[f45,f46])).
% 2.98/0.75  fof(f45,plain,(
% 2.98/0.75    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.98/0.75    inference(cnf_transformation,[],[f5])).
% 2.98/0.75  fof(f5,axiom,(
% 2.98/0.75    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.98/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.98/0.75  fof(f274,plain,(
% 2.98/0.75    k4_xboole_0(sK1,sK2) = k5_xboole_0(sK1,k1_xboole_0)),
% 2.98/0.75    inference(superposition,[],[f61,f90])).
% 2.98/0.75  fof(f90,plain,(
% 2.98/0.75    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 2.98/0.75    inference(resolution,[],[f67,f71])).
% 2.98/0.75  fof(f71,plain,(
% 2.98/0.75    r1_xboole_0(sK1,sK2)),
% 2.98/0.75    inference(resolution,[],[f51,f36])).
% 2.98/0.75  fof(f36,plain,(
% 2.98/0.75    r1_xboole_0(sK2,sK1)),
% 2.98/0.75    inference(cnf_transformation,[],[f30])).
% 2.98/0.75  fof(f30,plain,(
% 2.98/0.75    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 2.98/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f29])).
% 2.98/0.75  fof(f29,plain,(
% 2.98/0.75    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 2.98/0.75    introduced(choice_axiom,[])).
% 2.98/0.75  fof(f22,plain,(
% 2.98/0.75    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 2.98/0.75    inference(flattening,[],[f21])).
% 2.98/0.75  fof(f21,plain,(
% 2.98/0.75    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 2.98/0.75    inference(ennf_transformation,[],[f19])).
% 2.98/0.75  fof(f19,negated_conjecture,(
% 2.98/0.75    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 2.98/0.75    inference(negated_conjecture,[],[f18])).
% 2.98/0.75  fof(f18,conjecture,(
% 2.98/0.75    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 2.98/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 2.98/0.75  fof(f51,plain,(
% 2.98/0.75    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 2.98/0.75    inference(cnf_transformation,[],[f25])).
% 2.98/0.75  fof(f25,plain,(
% 2.98/0.75    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.98/0.75    inference(ennf_transformation,[],[f3])).
% 2.98/0.75  fof(f3,axiom,(
% 2.98/0.75    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.98/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 2.98/0.75  fof(f7046,plain,(
% 2.98/0.75    k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 2.98/0.75    inference(superposition,[],[f566,f2470])).
% 2.98/0.75  fof(f2470,plain,(
% 2.98/0.75    ( ! [X72] : (k4_xboole_0(sK1,k4_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,X72)))) = k4_xboole_0(sK1,k4_xboole_0(sK1,X72))) )),
% 2.98/0.75    inference(resolution,[],[f69,f213])).
% 2.98/0.75  fof(f213,plain,(
% 2.98/0.75    r1_xboole_0(sK1,sK0)),
% 2.98/0.75    inference(resolution,[],[f209,f51])).
% 2.98/0.75  fof(f209,plain,(
% 2.98/0.75    r1_xboole_0(sK0,sK1)),
% 2.98/0.75    inference(trivial_inequality_removal,[],[f204])).
% 2.98/0.75  fof(f204,plain,(
% 2.98/0.75    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,sK1)),
% 2.98/0.75    inference(superposition,[],[f66,f181])).
% 2.98/0.75  fof(f181,plain,(
% 2.98/0.75    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.98/0.75    inference(forward_demodulation,[],[f180,f39])).
% 2.98/0.75  fof(f180,plain,(
% 2.98/0.75    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k1_xboole_0)))),
% 2.98/0.75    inference(forward_demodulation,[],[f174,f92])).
% 2.98/0.75  fof(f174,plain,(
% 2.98/0.75    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))))),
% 2.98/0.75    inference(resolution,[],[f170,f36])).
% 2.98/0.75  fof(f170,plain,(
% 2.98/0.75    ( ! [X0] : (~r1_xboole_0(sK2,X0) | k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))))) )),
% 2.98/0.75    inference(resolution,[],[f160,f78])).
% 2.98/0.75  fof(f78,plain,(
% 2.98/0.75    ( ! [X0] : (~r2_hidden(sK3,X0) | ~r1_xboole_0(sK2,X0)) )),
% 2.98/0.75    inference(resolution,[],[f49,f35])).
% 2.98/0.75  fof(f35,plain,(
% 2.98/0.75    r2_hidden(sK3,sK2)),
% 2.98/0.75    inference(cnf_transformation,[],[f30])).
% 2.98/0.75  fof(f49,plain,(
% 2.98/0.75    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 2.98/0.75    inference(cnf_transformation,[],[f32])).
% 2.98/0.75  fof(f32,plain,(
% 2.98/0.75    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.98/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f31])).
% 2.98/0.75  fof(f31,plain,(
% 2.98/0.75    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 2.98/0.75    introduced(choice_axiom,[])).
% 2.98/0.75  fof(f23,plain,(
% 2.98/0.75    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.98/0.75    inference(ennf_transformation,[],[f20])).
% 2.98/0.75  fof(f20,plain,(
% 2.98/0.75    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.98/0.75    inference(rectify,[],[f4])).
% 2.98/0.75  fof(f4,axiom,(
% 2.98/0.75    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.98/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 2.98/0.75  fof(f160,plain,(
% 2.98/0.75    ( ! [X0] : (r2_hidden(sK3,X0) | k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,X0))))) )),
% 2.98/0.75    inference(forward_demodulation,[],[f158,f68])).
% 2.98/0.75  fof(f68,plain,(
% 2.98/0.75    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) )),
% 2.98/0.75    inference(definition_unfolding,[],[f55,f46,f46,f46,f46])).
% 2.98/0.75  fof(f55,plain,(
% 2.98/0.75    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 2.98/0.75    inference(cnf_transformation,[],[f6])).
% 2.98/0.75  fof(f6,axiom,(
% 2.98/0.75    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 2.98/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 2.98/0.75  fof(f158,plain,(
% 2.98/0.75    ( ! [X0] : (r2_hidden(sK3,X0) | k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X0))) )),
% 2.98/0.75    inference(resolution,[],[f153,f67])).
% 2.98/0.75  fof(f153,plain,(
% 2.98/0.75    ( ! [X0] : (r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X0) | r2_hidden(sK3,X0)) )),
% 2.98/0.75    inference(resolution,[],[f82,f65])).
% 2.98/0.75  fof(f65,plain,(
% 2.98/0.75    ( ! [X0,X1] : (r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 2.98/0.75    inference(definition_unfolding,[],[f50,f60])).
% 2.98/0.75  fof(f60,plain,(
% 2.98/0.75    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.98/0.75    inference(definition_unfolding,[],[f40,f58])).
% 2.98/0.75  fof(f58,plain,(
% 2.98/0.75    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.98/0.75    inference(definition_unfolding,[],[f44,f54])).
% 2.98/0.75  fof(f54,plain,(
% 2.98/0.75    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.98/0.75    inference(cnf_transformation,[],[f15])).
% 2.98/0.75  fof(f15,axiom,(
% 2.98/0.75    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.98/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.98/0.75  fof(f44,plain,(
% 2.98/0.75    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.98/0.75    inference(cnf_transformation,[],[f14])).
% 2.98/0.75  fof(f14,axiom,(
% 2.98/0.75    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.98/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.98/0.75  fof(f40,plain,(
% 2.98/0.75    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.98/0.75    inference(cnf_transformation,[],[f13])).
% 2.98/0.75  fof(f13,axiom,(
% 2.98/0.75    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.98/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.98/0.75  fof(f50,plain,(
% 2.98/0.75    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.98/0.75    inference(cnf_transformation,[],[f24])).
% 2.98/0.75  fof(f24,plain,(
% 2.98/0.75    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 2.98/0.75    inference(ennf_transformation,[],[f16])).
% 2.98/0.75  fof(f16,axiom,(
% 2.98/0.75    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 2.98/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 2.98/0.75  fof(f82,plain,(
% 2.98/0.75    ( ! [X0] : (~r1_xboole_0(k2_enumset1(sK3,sK3,sK3,sK3),X0) | r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),X0)) )),
% 2.98/0.75    inference(resolution,[],[f57,f63])).
% 2.98/0.75  fof(f63,plain,(
% 2.98/0.75    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_enumset1(sK3,sK3,sK3,sK3))),
% 2.98/0.75    inference(definition_unfolding,[],[f34,f46,f60])).
% 2.98/0.75  fof(f34,plain,(
% 2.98/0.75    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 2.98/0.75    inference(cnf_transformation,[],[f30])).
% 2.98/0.75  fof(f57,plain,(
% 2.98/0.75    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 2.98/0.75    inference(cnf_transformation,[],[f28])).
% 2.98/0.75  fof(f28,plain,(
% 2.98/0.75    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 2.98/0.75    inference(flattening,[],[f27])).
% 2.98/0.75  fof(f27,plain,(
% 2.98/0.75    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.98/0.75    inference(ennf_transformation,[],[f9])).
% 2.98/0.75  fof(f9,axiom,(
% 2.98/0.75    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 2.98/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 2.98/0.75  fof(f66,plain,(
% 2.98/0.75    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 2.98/0.75    inference(definition_unfolding,[],[f53,f46])).
% 2.98/0.75  fof(f53,plain,(
% 2.98/0.75    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.98/0.75    inference(cnf_transformation,[],[f33])).
% 2.98/0.75  fof(f69,plain,(
% 2.98/0.75    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,k3_tarski(k2_enumset1(X1,X1,X1,X2)))) = k4_xboole_0(X0,k4_xboole_0(X0,X2))) )),
% 2.98/0.75    inference(definition_unfolding,[],[f56,f46,f59,f46])).
% 2.98/0.75  fof(f59,plain,(
% 2.98/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 2.98/0.75    inference(definition_unfolding,[],[f43,f58])).
% 2.98/0.75  fof(f43,plain,(
% 2.98/0.75    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 2.98/0.75    inference(cnf_transformation,[],[f17])).
% 2.98/0.75  fof(f17,axiom,(
% 2.98/0.75    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 2.98/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.98/0.75  fof(f56,plain,(
% 2.98/0.75    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1)) )),
% 2.98/0.75    inference(cnf_transformation,[],[f26])).
% 2.98/0.75  fof(f26,plain,(
% 2.98/0.75    ! [X0,X1,X2] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))),
% 2.98/0.75    inference(ennf_transformation,[],[f11])).
% 2.98/0.75  fof(f11,axiom,(
% 2.98/0.75    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(X0,X2))),
% 2.98/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).
% 2.98/0.75  fof(f566,plain,(
% 2.98/0.75    k1_xboole_0 != k4_xboole_0(sK1,k4_xboole_0(sK1,k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2))))),
% 2.98/0.75    inference(resolution,[],[f403,f62])).
% 2.98/0.75  fof(f62,plain,(
% 2.98/0.75    ~r1_xboole_0(k3_tarski(k2_enumset1(sK0,sK0,sK0,sK2)),sK1)),
% 2.98/0.75    inference(definition_unfolding,[],[f37,f59])).
% 2.98/0.75  fof(f37,plain,(
% 2.98/0.75    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 2.98/0.75    inference(cnf_transformation,[],[f30])).
% 2.98/0.75  fof(f403,plain,(
% 2.98/0.75    ( ! [X2,X3] : (r1_xboole_0(X2,X3) | k1_xboole_0 != k4_xboole_0(X3,k4_xboole_0(X3,X2))) )),
% 2.98/0.75    inference(superposition,[],[f66,f64])).
% 2.98/0.75  fof(f64,plain,(
% 2.98/0.75    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.98/0.75    inference(definition_unfolding,[],[f42,f46,f46])).
% 2.98/0.75  fof(f42,plain,(
% 2.98/0.75    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.98/0.75    inference(cnf_transformation,[],[f1])).
% 2.98/0.75  fof(f1,axiom,(
% 2.98/0.75    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.98/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.98/0.75  % SZS output end Proof for theBenchmark
% 2.98/0.75  % (12178)------------------------------
% 2.98/0.75  % (12178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.98/0.75  % (12178)Termination reason: Refutation
% 2.98/0.75  
% 2.98/0.75  % (12178)Memory used [KB]: 8955
% 2.98/0.75  % (12178)Time elapsed: 0.336 s
% 2.98/0.75  % (12178)------------------------------
% 2.98/0.75  % (12178)------------------------------
% 2.98/0.78  % (12161)Success in time 0.423 s
%------------------------------------------------------------------------------
