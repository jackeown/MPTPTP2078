%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:07 EST 2020

% Result     : Theorem 11.48s
% Output     : Refutation 11.48s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 439 expanded)
%              Number of leaves         :   11 ( 130 expanded)
%              Depth                    :   19
%              Number of atoms          :  220 (1795 expanded)
%              Number of equality atoms :   49 ( 380 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2255,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2254,f2252])).

fof(f2252,plain,(
    ~ r2_hidden(sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2)),k2_zfmisc_1(sK0,sK2)) ),
    inference(forward_demodulation,[],[f2251,f31])).

fof(f31,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f2251,plain,(
    ~ r2_hidden(sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,k4_xboole_0(sK2,k1_xboole_0))),k2_zfmisc_1(sK0,k4_xboole_0(sK2,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f2237,f2140])).

fof(f2140,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f28,f59,f476])).

fof(f476,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2
      | ~ r1_tarski(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f456])).

fof(f456,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2
      | ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(resolution,[],[f99,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X1)
      | k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK5(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK5(X0,X1,X2),X1)
            | ~ r2_hidden(sK5(X0,X1,X2),X0)
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
              & r2_hidden(sK5(X0,X1,X2),X0) )
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK5(X0,X1,X2),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X0)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK5(X0,X1,X2),X1)
            & r2_hidden(sK5(X0,X1,X2),X0) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f99,plain,(
    ! [X12,X10,X13,X11] :
      ( r2_hidden(sK5(X10,X11,X12),X13)
      | r2_hidden(sK5(X10,X11,X12),X12)
      | k4_xboole_0(X10,X11) = X12
      | ~ r1_tarski(X10,X13) ) ),
    inference(resolution,[],[f43,f37])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X2)
      | r2_hidden(sK5(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f59,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(condensation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f53,f31])).

fof(f53,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f28,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_zfmisc_1)).

fof(f2237,plain,(
    ~ r2_hidden(sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))),k2_zfmisc_1(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))) ),
    inference(backward_demodulation,[],[f854,f2236])).

fof(f2236,plain,(
    ! [X0,X1] : k4_xboole_0(k2_zfmisc_1(sK0,X0),k4_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X1))) = k2_zfmisc_1(sK0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f2196,f31])).

fof(f2196,plain,(
    ! [X0,X1] : k4_xboole_0(k2_zfmisc_1(sK0,X0),k4_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X1))) = k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(superposition,[],[f49,f2139])).

fof(f2139,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f27,f59,f476])).

fof(f27,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(definition_unfolding,[],[f46,f33,f33,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f854,plain,(
    ~ r2_hidden(sK4(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))) ),
    inference(backward_demodulation,[],[f758,f798])).

fof(f798,plain,(
    ! [X10,X8,X11,X9] : k4_xboole_0(k2_zfmisc_1(X8,X10),k4_xboole_0(k2_zfmisc_1(X8,X10),k2_zfmisc_1(X9,X11))) = k4_xboole_0(k2_zfmisc_1(X8,X11),k4_xboole_0(k2_zfmisc_1(X8,X11),k2_zfmisc_1(X9,X10))) ),
    inference(superposition,[],[f124,f49])).

fof(f124,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k2_zfmisc_1(X2,X0),k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1))) = k2_zfmisc_1(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f49,f48])).

fof(f48,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f32,f33,f33])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f758,plain,(
    ~ r2_hidden(sK4(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)))),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)))) ),
    inference(unit_resulting_resolution,[],[f716,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f716,plain,(
    ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)))) ),
    inference(subsumption_resolution,[],[f65,f715])).

fof(f715,plain,(
    ! [X43,X41,X44,X42] : r1_tarski(k4_xboole_0(k2_zfmisc_1(X43,X42),k4_xboole_0(k2_zfmisc_1(X43,X42),k2_zfmisc_1(X41,X44))),k2_zfmisc_1(X43,X44)) ),
    inference(forward_demodulation,[],[f672,f49])).

fof(f672,plain,(
    ! [X43,X41,X44,X42] : r1_tarski(k2_zfmisc_1(k4_xboole_0(X43,k4_xboole_0(X43,X41)),k4_xboole_0(X42,k4_xboole_0(X42,X44))),k2_zfmisc_1(X43,X44)) ),
    inference(superposition,[],[f269,f119])).

fof(f119,plain,(
    ! [X2,X0,X3,X1] : k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) = k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(superposition,[],[f49,f48])).

fof(f269,plain,(
    ! [X2,X1] : r1_tarski(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1) ),
    inference(superposition,[],[f235,f48])).

fof(f235,plain,(
    ! [X2,X3] : r1_tarski(k4_xboole_0(X2,X3),X2) ),
    inference(duplicate_literal_removal,[],[f224])).

fof(f224,plain,(
    ! [X2,X3] :
      ( r1_tarski(k4_xboole_0(X2,X3),X2)
      | r1_tarski(k4_xboole_0(X2,X3),X2) ) ),
    inference(resolution,[],[f63,f39])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(k4_xboole_0(X0,X1),X2),X0)
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f54,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f54,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f65,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))))
    | ~ r1_tarski(k4_xboole_0(k2_zfmisc_1(sK0,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))),k2_zfmisc_1(sK0,sK2)) ),
    inference(extensionality_resolution,[],[f36,f47])).

fof(f47,plain,(
    k2_zfmisc_1(sK0,sK2) != k4_xboole_0(k2_zfmisc_1(sK0,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))) ),
    inference(definition_unfolding,[],[f29,f33])).

fof(f29,plain,(
    k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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

fof(f2254,plain,(
    r2_hidden(sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2)),k2_zfmisc_1(sK0,sK2)) ),
    inference(forward_demodulation,[],[f2253,f31])).

fof(f2253,plain,(
    r2_hidden(sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,k4_xboole_0(sK2,k1_xboole_0))),k2_zfmisc_1(sK0,sK2)) ),
    inference(forward_demodulation,[],[f2238,f2140])).

fof(f2238,plain,(
    r2_hidden(sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))),k2_zfmisc_1(sK0,sK2)) ),
    inference(backward_demodulation,[],[f855,f2236])).

fof(f855,plain,(
    r2_hidden(sK4(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k2_zfmisc_1(sK0,sK2)) ),
    inference(backward_demodulation,[],[f759,f798])).

fof(f759,plain,(
    r2_hidden(sK4(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)))),k2_zfmisc_1(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f716,f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:08:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.52  % (13622)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (13639)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.31/0.53  % (13623)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.31/0.53  % (13616)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.31/0.53  % (13616)Refutation not found, incomplete strategy% (13616)------------------------------
% 1.31/0.53  % (13616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.53  % (13616)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.53  
% 1.31/0.53  % (13616)Memory used [KB]: 1663
% 1.31/0.53  % (13616)Time elapsed: 0.113 s
% 1.31/0.53  % (13616)------------------------------
% 1.31/0.53  % (13616)------------------------------
% 1.31/0.53  % (13618)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.31/0.54  % (13630)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.31/0.54  % (13620)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.31/0.54  % (13628)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.31/0.54  % (13632)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.31/0.54  % (13627)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.31/0.54  % (13638)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.31/0.54  % (13621)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.31/0.54  % (13638)Refutation not found, incomplete strategy% (13638)------------------------------
% 1.31/0.54  % (13638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (13638)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (13638)Memory used [KB]: 10746
% 1.31/0.54  % (13638)Time elapsed: 0.130 s
% 1.31/0.54  % (13638)------------------------------
% 1.31/0.54  % (13638)------------------------------
% 1.50/0.55  % (13631)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.50/0.55  % (13624)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.50/0.55  % (13644)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.50/0.55  % (13624)Refutation not found, incomplete strategy% (13624)------------------------------
% 1.50/0.55  % (13624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (13624)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.55  
% 1.50/0.55  % (13624)Memory used [KB]: 10618
% 1.50/0.55  % (13624)Time elapsed: 0.137 s
% 1.50/0.55  % (13624)------------------------------
% 1.50/0.55  % (13624)------------------------------
% 1.50/0.55  % (13634)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.50/0.55  % (13643)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.50/0.55  % (13625)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.50/0.55  % (13637)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.50/0.55  % (13618)Refutation not found, incomplete strategy% (13618)------------------------------
% 1.50/0.55  % (13618)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (13618)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.55  
% 1.50/0.55  % (13618)Memory used [KB]: 10618
% 1.50/0.55  % (13618)Time elapsed: 0.141 s
% 1.50/0.55  % (13618)------------------------------
% 1.50/0.55  % (13618)------------------------------
% 1.50/0.55  % (13637)Refutation not found, incomplete strategy% (13637)------------------------------
% 1.50/0.55  % (13637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (13637)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.55  
% 1.50/0.55  % (13637)Memory used [KB]: 1663
% 1.50/0.55  % (13637)Time elapsed: 0.145 s
% 1.50/0.55  % (13637)------------------------------
% 1.50/0.55  % (13637)------------------------------
% 1.50/0.55  % (13617)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.50/0.56  % (13645)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.50/0.56  % (13636)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.50/0.56  % (13635)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.50/0.56  % (13641)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.50/0.56  % (13636)Refutation not found, incomplete strategy% (13636)------------------------------
% 1.50/0.56  % (13636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (13636)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (13636)Memory used [KB]: 10746
% 1.50/0.56  % (13636)Time elapsed: 0.147 s
% 1.50/0.56  % (13636)------------------------------
% 1.50/0.56  % (13636)------------------------------
% 1.50/0.56  % (13642)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.50/0.56  % (13641)Refutation not found, incomplete strategy% (13641)------------------------------
% 1.50/0.56  % (13641)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (13641)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (13641)Memory used [KB]: 6268
% 1.50/0.56  % (13641)Time elapsed: 0.147 s
% 1.50/0.56  % (13641)------------------------------
% 1.50/0.56  % (13641)------------------------------
% 1.50/0.56  % (13619)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.50/0.56  % (13629)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.50/0.56  % (13626)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.50/0.56  % (13626)Refutation not found, incomplete strategy% (13626)------------------------------
% 1.50/0.56  % (13626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (13626)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (13626)Memory used [KB]: 10618
% 1.50/0.56  % (13626)Time elapsed: 0.155 s
% 1.50/0.56  % (13626)------------------------------
% 1.50/0.56  % (13626)------------------------------
% 1.50/0.57  % (13640)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.50/0.57  % (13633)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.50/0.57  % (13633)Refutation not found, incomplete strategy% (13633)------------------------------
% 1.50/0.57  % (13633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (13633)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.57  
% 1.50/0.57  % (13633)Memory used [KB]: 10618
% 1.50/0.57  % (13633)Time elapsed: 0.154 s
% 1.50/0.57  % (13633)------------------------------
% 1.50/0.57  % (13633)------------------------------
% 1.50/0.57  % (13625)Refutation not found, incomplete strategy% (13625)------------------------------
% 1.50/0.57  % (13625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.57  % (13625)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.57  
% 1.50/0.57  % (13625)Memory used [KB]: 10618
% 1.50/0.57  % (13625)Time elapsed: 0.158 s
% 1.50/0.57  % (13625)------------------------------
% 1.50/0.57  % (13625)------------------------------
% 1.50/0.61  % (13620)Refutation not found, incomplete strategy% (13620)------------------------------
% 1.50/0.61  % (13620)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.61  % (13620)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.61  
% 1.50/0.61  % (13620)Memory used [KB]: 6780
% 1.50/0.61  % (13620)Time elapsed: 0.181 s
% 1.50/0.61  % (13620)------------------------------
% 1.50/0.61  % (13620)------------------------------
% 2.00/0.66  % (13651)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.00/0.67  % (13652)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.00/0.68  % (13658)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.26/0.68  % (13653)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.26/0.69  % (13654)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.26/0.69  % (13655)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.26/0.70  % (13656)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.26/0.71  % (13665)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.26/0.71  % (13664)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.26/0.71  % (13666)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.26/0.73  % (13665)Refutation not found, incomplete strategy% (13665)------------------------------
% 2.26/0.73  % (13665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.26/0.73  % (13665)Termination reason: Refutation not found, incomplete strategy
% 2.26/0.73  
% 2.26/0.73  % (13665)Memory used [KB]: 1663
% 2.26/0.73  % (13665)Time elapsed: 0.104 s
% 2.26/0.73  % (13665)------------------------------
% 2.26/0.73  % (13665)------------------------------
% 2.67/0.75  % (13667)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 2.97/0.83  % (13621)Time limit reached!
% 2.97/0.83  % (13621)------------------------------
% 2.97/0.83  % (13621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.97/0.83  % (13621)Termination reason: Time limit
% 2.97/0.83  
% 2.97/0.83  % (13621)Memory used [KB]: 9466
% 2.97/0.83  % (13621)Time elapsed: 0.423 s
% 2.97/0.83  % (13621)------------------------------
% 2.97/0.83  % (13621)------------------------------
% 3.16/0.88  % (13675)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 3.16/0.92  % (13628)Time limit reached!
% 3.16/0.92  % (13628)------------------------------
% 3.16/0.92  % (13628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.16/0.92  % (13628)Termination reason: Time limit
% 3.16/0.92  
% 3.16/0.92  % (13628)Memory used [KB]: 9722
% 3.16/0.92  % (13628)Time elapsed: 0.503 s
% 3.16/0.92  % (13628)------------------------------
% 3.16/0.92  % (13628)------------------------------
% 3.16/0.92  % (13617)Time limit reached!
% 3.16/0.92  % (13617)------------------------------
% 3.16/0.92  % (13617)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.16/0.92  % (13617)Termination reason: Time limit
% 3.16/0.92  % (13617)Termination phase: Saturation
% 3.16/0.92  
% 3.16/0.92  % (13617)Memory used [KB]: 8315
% 3.16/0.92  % (13617)Time elapsed: 0.500 s
% 3.16/0.92  % (13617)------------------------------
% 3.16/0.92  % (13617)------------------------------
% 3.55/0.95  % (13720)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 3.74/1.00  % (13655)Time limit reached!
% 3.74/1.00  % (13655)------------------------------
% 3.74/1.00  % (13655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.74/1.00  % (13655)Termination reason: Time limit
% 3.74/1.00  
% 3.74/1.00  % (13655)Memory used [KB]: 13560
% 3.74/1.00  % (13655)Time elapsed: 0.410 s
% 3.74/1.00  % (13655)------------------------------
% 3.74/1.00  % (13655)------------------------------
% 3.74/1.02  % (13654)Time limit reached!
% 3.74/1.02  % (13654)------------------------------
% 3.74/1.02  % (13654)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.74/1.03  % (13644)Time limit reached!
% 3.74/1.03  % (13644)------------------------------
% 3.74/1.03  % (13644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.74/1.03  % (13644)Termination reason: Time limit
% 3.74/1.03  % (13644)Termination phase: Saturation
% 3.74/1.03  
% 3.74/1.03  % (13644)Memory used [KB]: 9850
% 3.74/1.03  % (13644)Time elapsed: 0.600 s
% 3.74/1.03  % (13644)------------------------------
% 3.74/1.03  % (13644)------------------------------
% 3.74/1.03  % (13654)Termination reason: Time limit
% 3.74/1.03  
% 3.74/1.03  % (13654)Memory used [KB]: 7931
% 3.74/1.03  % (13654)Time elapsed: 0.418 s
% 3.74/1.03  % (13654)------------------------------
% 3.74/1.03  % (13654)------------------------------
% 3.74/1.03  % (13632)Time limit reached!
% 3.74/1.03  % (13632)------------------------------
% 3.74/1.03  % (13632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.74/1.03  % (13632)Termination reason: Time limit
% 3.74/1.03  % (13632)Termination phase: Saturation
% 3.74/1.03  
% 3.74/1.03  % (13632)Memory used [KB]: 15095
% 3.74/1.03  % (13632)Time elapsed: 0.618 s
% 3.74/1.03  % (13632)------------------------------
% 3.74/1.03  % (13632)------------------------------
% 3.74/1.04  % (13770)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 3.74/1.04  % (13771)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 3.74/1.04  % (13770)Refutation not found, incomplete strategy% (13770)------------------------------
% 3.74/1.04  % (13770)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.74/1.04  % (13770)Termination reason: Refutation not found, incomplete strategy
% 3.74/1.04  
% 3.74/1.04  % (13770)Memory used [KB]: 1663
% 3.74/1.04  % (13770)Time elapsed: 0.094 s
% 3.74/1.04  % (13770)------------------------------
% 3.74/1.04  % (13770)------------------------------
% 5.60/1.12  % (13623)Time limit reached!
% 5.60/1.12  % (13623)------------------------------
% 5.60/1.12  % (13623)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.60/1.12  % (13623)Termination reason: Time limit
% 5.60/1.12  
% 5.60/1.12  % (13623)Memory used [KB]: 12665
% 5.60/1.12  % (13623)Time elapsed: 0.637 s
% 5.60/1.12  % (13623)------------------------------
% 5.60/1.12  % (13623)------------------------------
% 6.04/1.13  % (13813)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 6.04/1.16  % (13825)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 6.26/1.16  % (13826)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 6.26/1.18  % (13832)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 6.26/1.18  % (13831)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 6.82/1.25  % (13847)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 7.63/1.36  % (13720)Time limit reached!
% 7.63/1.36  % (13720)------------------------------
% 7.63/1.36  % (13720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.83/1.36  % (13720)Termination reason: Time limit
% 7.83/1.36  % (13720)Termination phase: Saturation
% 7.83/1.36  
% 7.83/1.36  % (13720)Memory used [KB]: 4093
% 7.83/1.36  % (13720)Time elapsed: 0.500 s
% 7.83/1.36  % (13720)------------------------------
% 7.83/1.36  % (13720)------------------------------
% 8.57/1.48  % (13907)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 8.57/1.49  % (13825)Time limit reached!
% 8.57/1.49  % (13825)------------------------------
% 8.57/1.49  % (13825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.57/1.49  % (13825)Termination reason: Time limit
% 8.57/1.49  
% 8.57/1.49  % (13825)Memory used [KB]: 4349
% 8.57/1.49  % (13825)Time elapsed: 0.423 s
% 8.57/1.49  % (13825)------------------------------
% 8.57/1.49  % (13825)------------------------------
% 8.57/1.50  % (13832)Time limit reached!
% 8.57/1.50  % (13832)------------------------------
% 8.57/1.50  % (13832)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.57/1.50  % (13832)Termination reason: Time limit
% 8.57/1.50  
% 8.57/1.50  % (13832)Memory used [KB]: 2942
% 8.57/1.50  % (13832)Time elapsed: 0.420 s
% 8.57/1.50  % (13832)------------------------------
% 8.57/1.50  % (13832)------------------------------
% 9.36/1.61  % (13908)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 9.36/1.63  % (13642)Time limit reached!
% 9.36/1.63  % (13642)------------------------------
% 9.36/1.63  % (13642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.36/1.63  % (13642)Termination reason: Time limit
% 9.36/1.63  
% 9.36/1.63  % (13642)Memory used [KB]: 16502
% 9.36/1.63  % (13642)Time elapsed: 1.220 s
% 9.36/1.63  % (13642)------------------------------
% 9.36/1.63  % (13642)------------------------------
% 9.36/1.63  % (13909)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 10.85/1.74  % (13640)Time limit reached!
% 10.85/1.74  % (13640)------------------------------
% 10.85/1.74  % (13640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.85/1.74  % (13640)Termination reason: Time limit
% 10.85/1.74  
% 10.85/1.74  % (13640)Memory used [KB]: 18805
% 10.85/1.74  % (13640)Time elapsed: 1.310 s
% 10.85/1.74  % (13640)------------------------------
% 10.85/1.74  % (13640)------------------------------
% 11.03/1.76  % (13910)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 11.03/1.76  % (13631)Time limit reached!
% 11.03/1.76  % (13631)------------------------------
% 11.03/1.76  % (13631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.03/1.76  % (13631)Termination reason: Time limit
% 11.03/1.76  
% 11.03/1.76  % (13631)Memory used [KB]: 12537
% 11.03/1.76  % (13631)Time elapsed: 1.316 s
% 11.03/1.76  % (13631)------------------------------
% 11.03/1.76  % (13631)------------------------------
% 11.48/1.82  % (13907)Refutation found. Thanks to Tanya!
% 11.48/1.82  % SZS status Theorem for theBenchmark
% 11.48/1.82  % SZS output start Proof for theBenchmark
% 11.48/1.82  fof(f2255,plain,(
% 11.48/1.82    $false),
% 11.48/1.82    inference(subsumption_resolution,[],[f2254,f2252])).
% 11.48/1.82  fof(f2252,plain,(
% 11.48/1.82    ~r2_hidden(sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2)),k2_zfmisc_1(sK0,sK2))),
% 11.48/1.82    inference(forward_demodulation,[],[f2251,f31])).
% 11.48/1.82  fof(f31,plain,(
% 11.48/1.82    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.48/1.82    inference(cnf_transformation,[],[f6])).
% 11.48/1.82  fof(f6,axiom,(
% 11.48/1.82    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 11.48/1.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 11.48/1.82  fof(f2251,plain,(
% 11.48/1.82    ~r2_hidden(sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,k4_xboole_0(sK2,k1_xboole_0))),k2_zfmisc_1(sK0,k4_xboole_0(sK2,k1_xboole_0)))),
% 11.48/1.82    inference(forward_demodulation,[],[f2237,f2140])).
% 11.48/1.82  fof(f2140,plain,(
% 11.48/1.82    k1_xboole_0 = k4_xboole_0(sK2,sK3)),
% 11.48/1.82    inference(unit_resulting_resolution,[],[f28,f59,f476])).
% 11.48/1.82  fof(f476,plain,(
% 11.48/1.82    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2 | ~r1_tarski(X0,X1)) )),
% 11.48/1.82    inference(duplicate_literal_removal,[],[f456])).
% 11.48/1.82  fof(f456,plain,(
% 11.48/1.82    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2 | ~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = X2 | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 11.48/1.82    inference(resolution,[],[f99,f44])).
% 11.48/1.82  fof(f44,plain,(
% 11.48/1.82    ( ! [X2,X0,X1] : (~r2_hidden(sK5(X0,X1,X2),X1) | k4_xboole_0(X0,X1) = X2 | r2_hidden(sK5(X0,X1,X2),X2)) )),
% 11.48/1.82    inference(cnf_transformation,[],[f26])).
% 11.48/1.82  fof(f26,plain,(
% 11.48/1.82    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.48/1.82    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f25])).
% 11.48/1.82  fof(f25,plain,(
% 11.48/1.82    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK5(X0,X1,X2),X1) | ~r2_hidden(sK5(X0,X1,X2),X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((~r2_hidden(sK5(X0,X1,X2),X1) & r2_hidden(sK5(X0,X1,X2),X0)) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 11.48/1.82    introduced(choice_axiom,[])).
% 11.48/1.82  fof(f24,plain,(
% 11.48/1.82    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.48/1.82    inference(rectify,[],[f23])).
% 11.48/1.82  fof(f23,plain,(
% 11.48/1.82    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.48/1.82    inference(flattening,[],[f22])).
% 11.48/1.82  fof(f22,plain,(
% 11.48/1.82    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 11.48/1.82    inference(nnf_transformation,[],[f3])).
% 11.48/1.82  fof(f3,axiom,(
% 11.48/1.82    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 11.48/1.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 11.48/1.82  fof(f99,plain,(
% 11.48/1.82    ( ! [X12,X10,X13,X11] : (r2_hidden(sK5(X10,X11,X12),X13) | r2_hidden(sK5(X10,X11,X12),X12) | k4_xboole_0(X10,X11) = X12 | ~r1_tarski(X10,X13)) )),
% 11.48/1.82    inference(resolution,[],[f43,f37])).
% 11.48/1.82  fof(f37,plain,(
% 11.48/1.82    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 11.48/1.82    inference(cnf_transformation,[],[f21])).
% 11.48/1.82  fof(f21,plain,(
% 11.48/1.82    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.48/1.82    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f19,f20])).
% 11.48/1.82  fof(f20,plain,(
% 11.48/1.82    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 11.48/1.82    introduced(choice_axiom,[])).
% 11.48/1.82  fof(f19,plain,(
% 11.48/1.82    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 11.48/1.82    inference(rectify,[],[f18])).
% 11.48/1.82  fof(f18,plain,(
% 11.48/1.82    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 11.48/1.82    inference(nnf_transformation,[],[f13])).
% 11.48/1.82  fof(f13,plain,(
% 11.48/1.82    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 11.48/1.82    inference(ennf_transformation,[],[f2])).
% 11.48/1.82  fof(f2,axiom,(
% 11.48/1.82    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 11.48/1.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 11.48/1.82  fof(f43,plain,(
% 11.48/1.82    ( ! [X2,X0,X1] : (r2_hidden(sK5(X0,X1,X2),X2) | r2_hidden(sK5(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 11.48/1.82    inference(cnf_transformation,[],[f26])).
% 11.48/1.82  fof(f59,plain,(
% 11.48/1.82    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 11.48/1.82    inference(condensation,[],[f58])).
% 11.48/1.82  fof(f58,plain,(
% 11.48/1.82    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 11.48/1.82    inference(superposition,[],[f53,f31])).
% 11.48/1.82  fof(f53,plain,(
% 11.48/1.82    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 11.48/1.82    inference(equality_resolution,[],[f41])).
% 11.48/1.82  fof(f41,plain,(
% 11.48/1.82    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 11.48/1.82    inference(cnf_transformation,[],[f26])).
% 11.48/1.82  fof(f28,plain,(
% 11.48/1.82    r1_tarski(sK2,sK3)),
% 11.48/1.82    inference(cnf_transformation,[],[f15])).
% 11.48/1.82  fof(f15,plain,(
% 11.48/1.82    k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1)),
% 11.48/1.82    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f14])).
% 11.48/1.82  fof(f14,plain,(
% 11.48/1.82    ? [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => (k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1))),
% 11.48/1.82    introduced(choice_axiom,[])).
% 11.48/1.82  fof(f12,plain,(
% 11.48/1.82    ? [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 11.48/1.82    inference(flattening,[],[f11])).
% 11.48/1.82  fof(f11,plain,(
% 11.48/1.82    ? [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) & (r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 11.48/1.82    inference(ennf_transformation,[],[f10])).
% 11.48/1.82  fof(f10,negated_conjecture,(
% 11.48/1.82    ~! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)))),
% 11.48/1.82    inference(negated_conjecture,[],[f9])).
% 11.48/1.82  fof(f9,conjecture,(
% 11.48/1.82    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)))),
% 11.48/1.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_zfmisc_1)).
% 11.48/1.82  fof(f2237,plain,(
% 11.48/1.82    ~r2_hidden(sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))),k2_zfmisc_1(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3))))),
% 11.48/1.82    inference(backward_demodulation,[],[f854,f2236])).
% 11.48/1.82  fof(f2236,plain,(
% 11.48/1.82    ( ! [X0,X1] : (k4_xboole_0(k2_zfmisc_1(sK0,X0),k4_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X1))) = k2_zfmisc_1(sK0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 11.48/1.82    inference(forward_demodulation,[],[f2196,f31])).
% 11.48/1.82  fof(f2196,plain,(
% 11.48/1.82    ( ! [X0,X1] : (k4_xboole_0(k2_zfmisc_1(sK0,X0),k4_xboole_0(k2_zfmisc_1(sK0,X0),k2_zfmisc_1(sK1,X1))) = k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 11.48/1.82    inference(superposition,[],[f49,f2139])).
% 11.48/1.82  fof(f2139,plain,(
% 11.48/1.82    k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 11.48/1.82    inference(unit_resulting_resolution,[],[f27,f59,f476])).
% 11.48/1.82  fof(f27,plain,(
% 11.48/1.82    r1_tarski(sK0,sK1)),
% 11.48/1.82    inference(cnf_transformation,[],[f15])).
% 11.48/1.82  fof(f49,plain,(
% 11.48/1.82    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) )),
% 11.48/1.82    inference(definition_unfolding,[],[f46,f33,f33,f33])).
% 11.48/1.82  fof(f33,plain,(
% 11.48/1.82    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 11.48/1.82    inference(cnf_transformation,[],[f7])).
% 11.48/1.82  fof(f7,axiom,(
% 11.48/1.82    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 11.48/1.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 11.48/1.82  fof(f46,plain,(
% 11.48/1.82    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 11.48/1.82    inference(cnf_transformation,[],[f8])).
% 11.48/1.82  fof(f8,axiom,(
% 11.48/1.82    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 11.48/1.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 11.48/1.82  fof(f854,plain,(
% 11.48/1.82    ~r2_hidden(sK4(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3))))),
% 11.48/1.82    inference(backward_demodulation,[],[f758,f798])).
% 11.48/1.82  fof(f798,plain,(
% 11.48/1.82    ( ! [X10,X8,X11,X9] : (k4_xboole_0(k2_zfmisc_1(X8,X10),k4_xboole_0(k2_zfmisc_1(X8,X10),k2_zfmisc_1(X9,X11))) = k4_xboole_0(k2_zfmisc_1(X8,X11),k4_xboole_0(k2_zfmisc_1(X8,X11),k2_zfmisc_1(X9,X10)))) )),
% 11.48/1.82    inference(superposition,[],[f124,f49])).
% 11.48/1.82  fof(f124,plain,(
% 11.48/1.82    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k2_zfmisc_1(X2,X0),k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X3,X1))) = k2_zfmisc_1(k4_xboole_0(X2,k4_xboole_0(X2,X3)),k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 11.48/1.82    inference(superposition,[],[f49,f48])).
% 11.48/1.82  fof(f48,plain,(
% 11.48/1.82    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 11.48/1.82    inference(definition_unfolding,[],[f32,f33,f33])).
% 11.48/1.82  fof(f32,plain,(
% 11.48/1.82    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.48/1.82    inference(cnf_transformation,[],[f1])).
% 11.48/1.82  fof(f1,axiom,(
% 11.48/1.82    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.48/1.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 11.48/1.82  fof(f758,plain,(
% 11.48/1.82    ~r2_hidden(sK4(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)))),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))))),
% 11.48/1.82    inference(unit_resulting_resolution,[],[f716,f39])).
% 11.48/1.82  fof(f39,plain,(
% 11.48/1.82    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 11.48/1.82    inference(cnf_transformation,[],[f21])).
% 11.48/1.82  fof(f716,plain,(
% 11.48/1.82    ~r1_tarski(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))))),
% 11.48/1.82    inference(subsumption_resolution,[],[f65,f715])).
% 11.48/1.82  fof(f715,plain,(
% 11.48/1.82    ( ! [X43,X41,X44,X42] : (r1_tarski(k4_xboole_0(k2_zfmisc_1(X43,X42),k4_xboole_0(k2_zfmisc_1(X43,X42),k2_zfmisc_1(X41,X44))),k2_zfmisc_1(X43,X44))) )),
% 11.48/1.82    inference(forward_demodulation,[],[f672,f49])).
% 11.48/1.82  fof(f672,plain,(
% 11.48/1.82    ( ! [X43,X41,X44,X42] : (r1_tarski(k2_zfmisc_1(k4_xboole_0(X43,k4_xboole_0(X43,X41)),k4_xboole_0(X42,k4_xboole_0(X42,X44))),k2_zfmisc_1(X43,X44))) )),
% 11.48/1.82    inference(superposition,[],[f269,f119])).
% 11.48/1.82  fof(f119,plain,(
% 11.48/1.82    ( ! [X2,X0,X3,X1] : (k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) = k2_zfmisc_1(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X2,k4_xboole_0(X2,X3)))) )),
% 11.48/1.82    inference(superposition,[],[f49,f48])).
% 11.48/1.82  fof(f269,plain,(
% 11.48/1.82    ( ! [X2,X1] : (r1_tarski(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1)) )),
% 11.48/1.82    inference(superposition,[],[f235,f48])).
% 11.48/1.82  fof(f235,plain,(
% 11.48/1.82    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X2,X3),X2)) )),
% 11.48/1.82    inference(duplicate_literal_removal,[],[f224])).
% 11.48/1.82  fof(f224,plain,(
% 11.48/1.82    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X2,X3),X2) | r1_tarski(k4_xboole_0(X2,X3),X2)) )),
% 11.48/1.82    inference(resolution,[],[f63,f39])).
% 11.48/1.82  fof(f63,plain,(
% 11.48/1.82    ( ! [X2,X0,X1] : (r2_hidden(sK4(k4_xboole_0(X0,X1),X2),X0) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 11.48/1.82    inference(resolution,[],[f54,f38])).
% 11.48/1.82  fof(f38,plain,(
% 11.48/1.82    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 11.48/1.82    inference(cnf_transformation,[],[f21])).
% 11.48/1.83  fof(f54,plain,(
% 11.48/1.83    ( ! [X4,X0,X1] : (~r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 11.48/1.83    inference(equality_resolution,[],[f40])).
% 11.48/1.83  fof(f40,plain,(
% 11.48/1.83    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 11.48/1.83    inference(cnf_transformation,[],[f26])).
% 11.48/1.83  fof(f65,plain,(
% 11.48/1.83    ~r1_tarski(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)))) | ~r1_tarski(k4_xboole_0(k2_zfmisc_1(sK0,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))),k2_zfmisc_1(sK0,sK2))),
% 11.48/1.83    inference(extensionality_resolution,[],[f36,f47])).
% 11.48/1.83  fof(f47,plain,(
% 11.48/1.83    k2_zfmisc_1(sK0,sK2) != k4_xboole_0(k2_zfmisc_1(sK0,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)))),
% 11.48/1.83    inference(definition_unfolding,[],[f29,f33])).
% 11.48/1.83  fof(f29,plain,(
% 11.48/1.83    k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))),
% 11.48/1.83    inference(cnf_transformation,[],[f15])).
% 11.48/1.83  fof(f36,plain,(
% 11.48/1.83    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 11.48/1.83    inference(cnf_transformation,[],[f17])).
% 11.48/1.83  fof(f17,plain,(
% 11.48/1.83    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.48/1.83    inference(flattening,[],[f16])).
% 11.48/1.83  fof(f16,plain,(
% 11.48/1.83    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.48/1.83    inference(nnf_transformation,[],[f4])).
% 11.48/1.83  fof(f4,axiom,(
% 11.48/1.83    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.48/1.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 11.48/1.83  fof(f2254,plain,(
% 11.48/1.83    r2_hidden(sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,sK2)),k2_zfmisc_1(sK0,sK2))),
% 11.48/1.83    inference(forward_demodulation,[],[f2253,f31])).
% 11.48/1.83  fof(f2253,plain,(
% 11.48/1.83    r2_hidden(sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,k4_xboole_0(sK2,k1_xboole_0))),k2_zfmisc_1(sK0,sK2))),
% 11.48/1.83    inference(forward_demodulation,[],[f2238,f2140])).
% 11.48/1.83  fof(f2238,plain,(
% 11.48/1.83    r2_hidden(sK4(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK3)))),k2_zfmisc_1(sK0,sK2))),
% 11.48/1.83    inference(backward_demodulation,[],[f855,f2236])).
% 11.48/1.83  fof(f855,plain,(
% 11.48/1.83    r2_hidden(sK4(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK2),k2_zfmisc_1(sK1,sK3)))),k2_zfmisc_1(sK0,sK2))),
% 11.48/1.83    inference(backward_demodulation,[],[f759,f798])).
% 11.48/1.83  fof(f759,plain,(
% 11.48/1.83    r2_hidden(sK4(k2_zfmisc_1(sK0,sK2),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k4_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)))),k2_zfmisc_1(sK0,sK2))),
% 11.48/1.83    inference(unit_resulting_resolution,[],[f716,f38])).
% 11.48/1.83  % SZS output end Proof for theBenchmark
% 11.48/1.83  % (13907)------------------------------
% 11.48/1.83  % (13907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.48/1.83  % (13907)Termination reason: Refutation
% 11.48/1.83  
% 11.48/1.83  % (13907)Memory used [KB]: 10362
% 11.48/1.83  % (13907)Time elapsed: 0.406 s
% 11.48/1.83  % (13907)------------------------------
% 11.48/1.83  % (13907)------------------------------
% 11.48/1.83  % (13615)Success in time 1.473 s
%------------------------------------------------------------------------------
