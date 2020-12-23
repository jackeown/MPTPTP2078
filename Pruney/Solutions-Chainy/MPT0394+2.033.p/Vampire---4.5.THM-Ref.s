%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:00 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 484 expanded)
%              Number of leaves         :   12 ( 118 expanded)
%              Depth                    :   22
%              Number of atoms          :  208 (3170 expanded)
%              Number of equality atoms :   53 ( 144 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1314,plain,(
    $false ),
    inference(subsumption_resolution,[],[f32,f1313])).

fof(f1313,plain,(
    ! [X12,X13] : k3_xboole_0(X13,X12) = k1_setfam_1(k2_tarski(X13,X12)) ),
    inference(subsumption_resolution,[],[f1300,f1290])).

fof(f1290,plain,(
    ! [X21] : k1_xboole_0 != k1_tarski(X21) ),
    inference(subsumption_resolution,[],[f1286,f970])).

fof(f970,plain,(
    ! [X12] : ~ r2_hidden(X12,k1_xboole_0) ),
    inference(resolution,[],[f960,f908])).

fof(f908,plain,(
    ! [X2,X1] :
      ( ~ r1_xboole_0(X1,X1)
      | ~ r2_hidden(X2,X1) ) ),
    inference(superposition,[],[f39,f832])).

fof(f832,plain,(
    ! [X8] : k3_xboole_0(X8,X8) = X8 ),
    inference(resolution,[],[f823,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X1,X0,X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f19])).

fof(f19,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f823,plain,(
    ! [X5] : sP0(X5,X5,X5) ),
    inference(duplicate_literal_removal,[],[f820])).

fof(f820,plain,(
    ! [X5] :
      ( sP0(X5,X5,X5)
      | sP0(X5,X5,X5) ) ),
    inference(resolution,[],[f814,f163])).

fof(f163,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1,X1),X1)
      | sP0(X0,X1,X1) ) ),
    inference(factoring,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X0)
              & r2_hidden(sK4(X0,X1,X2),X1) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X0)
            & r2_hidden(sK4(X0,X1,X2),X1) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f814,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(sK4(X10,X11,X11),X10)
      | sP0(X10,X11,X11) ) ),
    inference(subsumption_resolution,[],[f809,f163])).

fof(f809,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(sK4(X10,X11,X11),X10)
      | ~ r2_hidden(sK4(X10,X11,X11),X11)
      | sP0(X10,X11,X11) ) ),
    inference(duplicate_literal_removal,[],[f806])).

fof(f806,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(sK4(X10,X11,X11),X10)
      | ~ r2_hidden(sK4(X10,X11,X11),X11)
      | sP0(X10,X11,X11)
      | sP0(X10,X11,X11) ) ),
    inference(resolution,[],[f50,f163])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f960,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f909])).

fof(f909,plain,(
    ! [X3] :
      ( k1_xboole_0 != X3
      | r1_xboole_0(X3,X3) ) ),
    inference(superposition,[],[f42,f832])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f1286,plain,(
    ! [X21] :
      ( k1_xboole_0 != k1_tarski(X21)
      | r2_hidden(X21,k1_xboole_0) ) ),
    inference(superposition,[],[f40,f992])).

fof(f992,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f972,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f972,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f962,f832])).

fof(f962,plain,(
    ! [X0] : r1_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X0) ),
    inference(resolution,[],[f960,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(k3_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f67,f39])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f57,f53])).

fof(f53,plain,(
    ! [X0,X1] : sP0(X1,X0,k3_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X3,X2,k3_xboole_0(X0,X1))
      | r2_hidden(sK3(X0,X1),X2)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f45,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1))
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).

fof(f1300,plain,(
    ! [X12,X13] :
      ( k1_xboole_0 = k1_tarski(X13)
      | k3_xboole_0(X13,X12) = k1_setfam_1(k2_tarski(X13,X12)) ) ),
    inference(subsumption_resolution,[],[f124,f1290])).

fof(f124,plain,(
    ! [X12,X13] :
      ( k1_xboole_0 = k1_tarski(X12)
      | k1_xboole_0 = k1_tarski(X13)
      | k3_xboole_0(X13,X12) = k1_setfam_1(k2_tarski(X13,X12)) ) ),
    inference(resolution,[],[f119,f52])).

fof(f119,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0,k1_setfam_1(k2_tarski(X0,X1)))
      | k1_xboole_0 = k1_tarski(X1)
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(forward_demodulation,[],[f118,f33])).

fof(f33,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f118,plain,(
    ! [X0,X1] :
      ( sP0(k1_setfam_1(k1_tarski(X1)),X0,k1_setfam_1(k2_tarski(X0,X1)))
      | k1_xboole_0 = k1_tarski(X1)
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(forward_demodulation,[],[f117,f33])).

fof(f117,plain,(
    ! [X0,X1] :
      ( sP0(k1_setfam_1(k1_tarski(X1)),k1_setfam_1(k1_tarski(X0)),k1_setfam_1(k2_tarski(X0,X1)))
      | k1_xboole_0 = k1_tarski(X1)
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(superposition,[],[f79,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f79,plain,(
    ! [X14,X13] :
      ( sP0(k1_setfam_1(X14),k1_setfam_1(X13),k1_setfam_1(k2_xboole_0(X13,X14)))
      | k1_xboole_0 = X14
      | k1_xboole_0 = X13 ) ),
    inference(superposition,[],[f53,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

fof(f32,plain,(
    k3_xboole_0(sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    k3_xboole_0(sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f15,f21])).

fof(f21,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))
   => k3_xboole_0(sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:01:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (2229)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.51  % (2226)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.20/0.51  % (2222)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.20/0.52  % (2242)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.20/0.52  % (2229)Refutation not found, incomplete strategy% (2229)------------------------------
% 1.20/0.52  % (2229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % (2229)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.52  
% 1.20/0.52  % (2229)Memory used [KB]: 10618
% 1.20/0.52  % (2229)Time elapsed: 0.107 s
% 1.20/0.52  % (2229)------------------------------
% 1.20/0.52  % (2229)------------------------------
% 1.20/0.52  % (2223)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.20/0.52  % (2228)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.20/0.52  % (2224)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.20/0.52  % (2243)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.20/0.53  % (2235)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.20/0.53  % (2221)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.20/0.53  % (2227)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.20/0.53  % (2238)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.20/0.53  % (2234)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.35/0.53  % (2243)Refutation not found, incomplete strategy% (2243)------------------------------
% 1.35/0.53  % (2243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.53  % (2243)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.53  
% 1.35/0.53  % (2243)Memory used [KB]: 10618
% 1.35/0.53  % (2243)Time elapsed: 0.075 s
% 1.35/0.53  % (2243)------------------------------
% 1.35/0.53  % (2243)------------------------------
% 1.35/0.53  % (2225)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.35/0.53  % (2238)Refutation not found, incomplete strategy% (2238)------------------------------
% 1.35/0.53  % (2238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.53  % (2238)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.53  
% 1.35/0.53  % (2238)Memory used [KB]: 10618
% 1.35/0.53  % (2238)Time elapsed: 0.130 s
% 1.35/0.53  % (2238)------------------------------
% 1.35/0.53  % (2238)------------------------------
% 1.35/0.54  % (2225)Refutation not found, incomplete strategy% (2225)------------------------------
% 1.35/0.54  % (2225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (2225)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (2225)Memory used [KB]: 6140
% 1.35/0.54  % (2225)Time elapsed: 0.124 s
% 1.35/0.54  % (2225)------------------------------
% 1.35/0.54  % (2225)------------------------------
% 1.35/0.54  % (2242)Refutation not found, incomplete strategy% (2242)------------------------------
% 1.35/0.54  % (2242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (2242)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (2242)Memory used [KB]: 1663
% 1.35/0.54  % (2242)Time elapsed: 0.130 s
% 1.35/0.54  % (2242)------------------------------
% 1.35/0.54  % (2242)------------------------------
% 1.35/0.54  % (2232)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.35/0.54  % (2239)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.35/0.54  % (2233)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.35/0.54  % (2244)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.35/0.54  % (2223)Refutation not found, incomplete strategy% (2223)------------------------------
% 1.35/0.54  % (2223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (2223)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (2223)Memory used [KB]: 10618
% 1.35/0.54  % (2223)Time elapsed: 0.122 s
% 1.35/0.54  % (2223)------------------------------
% 1.35/0.54  % (2223)------------------------------
% 1.35/0.54  % (2237)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.35/0.54  % (2236)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.35/0.54  % (2221)Refutation not found, incomplete strategy% (2221)------------------------------
% 1.35/0.54  % (2221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (2221)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (2221)Memory used [KB]: 1663
% 1.35/0.54  % (2221)Time elapsed: 0.135 s
% 1.35/0.54  % (2221)------------------------------
% 1.35/0.54  % (2221)------------------------------
% 1.35/0.55  % (2232)Refutation not found, incomplete strategy% (2232)------------------------------
% 1.35/0.55  % (2232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (2232)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (2232)Memory used [KB]: 10618
% 1.35/0.55  % (2232)Time elapsed: 0.113 s
% 1.35/0.55  % (2232)------------------------------
% 1.35/0.55  % (2232)------------------------------
% 1.35/0.55  % (2250)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.35/0.55  % (2240)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.35/0.55  % (2230)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.35/0.55  % (2230)Refutation not found, incomplete strategy% (2230)------------------------------
% 1.35/0.55  % (2230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (2230)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (2230)Memory used [KB]: 10618
% 1.35/0.55  % (2230)Time elapsed: 0.139 s
% 1.35/0.55  % (2230)------------------------------
% 1.35/0.55  % (2230)------------------------------
% 1.35/0.55  % (2241)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.35/0.55  % (2246)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.35/0.55  % (2241)Refutation not found, incomplete strategy% (2241)------------------------------
% 1.35/0.55  % (2241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (2241)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (2241)Memory used [KB]: 10618
% 1.35/0.55  % (2241)Time elapsed: 0.137 s
% 1.35/0.55  % (2241)------------------------------
% 1.35/0.55  % (2241)------------------------------
% 1.35/0.55  % (2248)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.35/0.55  % (2246)Refutation not found, incomplete strategy% (2246)------------------------------
% 1.35/0.55  % (2246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (2231)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.35/0.55  % (2244)Refutation not found, incomplete strategy% (2244)------------------------------
% 1.35/0.55  % (2244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (2244)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (2244)Memory used [KB]: 1663
% 1.35/0.55  % (2244)Time elapsed: 0.147 s
% 1.35/0.55  % (2244)------------------------------
% 1.35/0.55  % (2244)------------------------------
% 1.35/0.56  % (2231)Refutation not found, incomplete strategy% (2231)------------------------------
% 1.35/0.56  % (2231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.56  % (2231)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.56  
% 1.35/0.56  % (2231)Memory used [KB]: 10618
% 1.35/0.56  % (2231)Time elapsed: 0.149 s
% 1.35/0.56  % (2231)------------------------------
% 1.35/0.56  % (2231)------------------------------
% 1.35/0.56  % (2245)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.35/0.56  % (2247)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.35/0.56  % (2246)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.56  
% 1.35/0.56  % (2246)Memory used [KB]: 6140
% 1.35/0.56  % (2246)Time elapsed: 0.134 s
% 1.35/0.56  % (2246)------------------------------
% 1.35/0.56  % (2246)------------------------------
% 1.35/0.56  % (2247)Refutation not found, incomplete strategy% (2247)------------------------------
% 1.35/0.56  % (2247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.56  % (2247)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.56  
% 1.35/0.56  % (2247)Memory used [KB]: 10618
% 1.35/0.56  % (2247)Time elapsed: 0.149 s
% 1.35/0.56  % (2247)------------------------------
% 1.35/0.56  % (2247)------------------------------
% 1.35/0.57  % (2249)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.35/0.59  % (2228)Refutation found. Thanks to Tanya!
% 1.35/0.59  % SZS status Theorem for theBenchmark
% 1.35/0.61  % SZS output start Proof for theBenchmark
% 1.35/0.61  fof(f1314,plain,(
% 1.35/0.61    $false),
% 1.35/0.61    inference(subsumption_resolution,[],[f32,f1313])).
% 1.35/0.61  fof(f1313,plain,(
% 1.35/0.61    ( ! [X12,X13] : (k3_xboole_0(X13,X12) = k1_setfam_1(k2_tarski(X13,X12))) )),
% 1.35/0.61    inference(subsumption_resolution,[],[f1300,f1290])).
% 1.35/0.61  fof(f1290,plain,(
% 1.35/0.61    ( ! [X21] : (k1_xboole_0 != k1_tarski(X21)) )),
% 1.35/0.61    inference(subsumption_resolution,[],[f1286,f970])).
% 1.35/0.61  fof(f970,plain,(
% 1.35/0.61    ( ! [X12] : (~r2_hidden(X12,k1_xboole_0)) )),
% 1.35/0.61    inference(resolution,[],[f960,f908])).
% 1.35/0.61  fof(f908,plain,(
% 1.35/0.61    ( ! [X2,X1] : (~r1_xboole_0(X1,X1) | ~r2_hidden(X2,X1)) )),
% 1.35/0.61    inference(superposition,[],[f39,f832])).
% 1.35/0.61  fof(f832,plain,(
% 1.35/0.61    ( ! [X8] : (k3_xboole_0(X8,X8) = X8) )),
% 1.35/0.61    inference(resolution,[],[f823,f52])).
% 1.35/0.61  fof(f52,plain,(
% 1.35/0.61    ( ! [X2,X0,X1] : (~sP0(X1,X0,X2) | k3_xboole_0(X0,X1) = X2) )),
% 1.35/0.61    inference(cnf_transformation,[],[f31])).
% 1.35/0.61  fof(f31,plain,(
% 1.35/0.61    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2))),
% 1.35/0.61    inference(nnf_transformation,[],[f20])).
% 1.35/0.61  fof(f20,plain,(
% 1.35/0.61    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.35/0.61    inference(definition_folding,[],[f1,f19])).
% 1.35/0.61  fof(f19,plain,(
% 1.35/0.61    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.35/0.61    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.35/0.61  fof(f1,axiom,(
% 1.35/0.61    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.35/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.35/0.61  fof(f823,plain,(
% 1.35/0.61    ( ! [X5] : (sP0(X5,X5,X5)) )),
% 1.35/0.61    inference(duplicate_literal_removal,[],[f820])).
% 1.35/0.61  fof(f820,plain,(
% 1.35/0.61    ( ! [X5] : (sP0(X5,X5,X5) | sP0(X5,X5,X5)) )),
% 1.35/0.61    inference(resolution,[],[f814,f163])).
% 1.35/0.61  fof(f163,plain,(
% 1.35/0.61    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,X1),X1) | sP0(X0,X1,X1)) )),
% 1.35/0.61    inference(factoring,[],[f48])).
% 1.35/0.61  fof(f48,plain,(
% 1.35/0.61    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2) | sP0(X0,X1,X2)) )),
% 1.35/0.61    inference(cnf_transformation,[],[f30])).
% 1.35/0.61  fof(f30,plain,(
% 1.35/0.61    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.35/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f28,f29])).
% 1.35/0.61  fof(f29,plain,(
% 1.35/0.61    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.35/0.61    introduced(choice_axiom,[])).
% 1.35/0.61  fof(f28,plain,(
% 1.35/0.61    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.35/0.61    inference(rectify,[],[f27])).
% 1.35/0.61  fof(f27,plain,(
% 1.35/0.61    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.35/0.61    inference(flattening,[],[f26])).
% 1.35/0.61  fof(f26,plain,(
% 1.35/0.61    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.35/0.61    inference(nnf_transformation,[],[f19])).
% 1.35/0.61  fof(f814,plain,(
% 1.35/0.61    ( ! [X10,X11] : (~r2_hidden(sK4(X10,X11,X11),X10) | sP0(X10,X11,X11)) )),
% 1.35/0.61    inference(subsumption_resolution,[],[f809,f163])).
% 1.35/0.61  fof(f809,plain,(
% 1.35/0.61    ( ! [X10,X11] : (~r2_hidden(sK4(X10,X11,X11),X10) | ~r2_hidden(sK4(X10,X11,X11),X11) | sP0(X10,X11,X11)) )),
% 1.35/0.61    inference(duplicate_literal_removal,[],[f806])).
% 1.35/0.61  fof(f806,plain,(
% 1.35/0.61    ( ! [X10,X11] : (~r2_hidden(sK4(X10,X11,X11),X10) | ~r2_hidden(sK4(X10,X11,X11),X11) | sP0(X10,X11,X11) | sP0(X10,X11,X11)) )),
% 1.35/0.61    inference(resolution,[],[f50,f163])).
% 1.35/0.61  fof(f50,plain,(
% 1.35/0.61    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | sP0(X0,X1,X2)) )),
% 1.35/0.61    inference(cnf_transformation,[],[f30])).
% 1.35/0.61  fof(f39,plain,(
% 1.35/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.35/0.61    inference(cnf_transformation,[],[f24])).
% 1.35/0.61  fof(f24,plain,(
% 1.35/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.35/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f23])).
% 1.35/0.61  fof(f23,plain,(
% 1.35/0.61    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 1.35/0.61    introduced(choice_axiom,[])).
% 1.35/0.61  fof(f16,plain,(
% 1.35/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.35/0.61    inference(ennf_transformation,[],[f14])).
% 1.35/0.61  fof(f14,plain,(
% 1.35/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.35/0.61    inference(rectify,[],[f3])).
% 1.35/0.61  fof(f3,axiom,(
% 1.35/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.35/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.35/0.62  fof(f960,plain,(
% 1.35/0.62    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.35/0.62    inference(equality_resolution,[],[f909])).
% 1.35/0.62  fof(f909,plain,(
% 1.35/0.62    ( ! [X3] : (k1_xboole_0 != X3 | r1_xboole_0(X3,X3)) )),
% 1.35/0.62    inference(superposition,[],[f42,f832])).
% 1.35/0.62  fof(f42,plain,(
% 1.35/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.35/0.62    inference(cnf_transformation,[],[f25])).
% 1.35/0.62  fof(f25,plain,(
% 1.35/0.62    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.35/0.62    inference(nnf_transformation,[],[f2])).
% 1.35/0.62  fof(f2,axiom,(
% 1.35/0.62    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.35/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.35/0.62  fof(f1286,plain,(
% 1.35/0.62    ( ! [X21] : (k1_xboole_0 != k1_tarski(X21) | r2_hidden(X21,k1_xboole_0)) )),
% 1.35/0.62    inference(superposition,[],[f40,f992])).
% 1.35/0.62  fof(f992,plain,(
% 1.35/0.62    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.35/0.62    inference(resolution,[],[f972,f41])).
% 1.35/0.62  fof(f41,plain,(
% 1.35/0.62    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.35/0.62    inference(cnf_transformation,[],[f25])).
% 1.35/0.62  fof(f972,plain,(
% 1.35/0.62    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.35/0.62    inference(forward_demodulation,[],[f962,f832])).
% 1.35/0.62  fof(f962,plain,(
% 1.35/0.62    ( ! [X0] : (r1_xboole_0(k3_xboole_0(k1_xboole_0,k1_xboole_0),X0)) )),
% 1.35/0.62    inference(resolution,[],[f960,f68])).
% 1.35/0.62  fof(f68,plain,(
% 1.35/0.62    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.35/0.62    inference(resolution,[],[f67,f39])).
% 1.35/0.62  fof(f67,plain,(
% 1.35/0.62    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.35/0.62    inference(resolution,[],[f57,f53])).
% 1.35/0.62  fof(f53,plain,(
% 1.35/0.62    ( ! [X0,X1] : (sP0(X1,X0,k3_xboole_0(X0,X1))) )),
% 1.35/0.62    inference(equality_resolution,[],[f51])).
% 1.35/0.62  fof(f51,plain,(
% 1.35/0.62    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.35/0.62    inference(cnf_transformation,[],[f31])).
% 1.35/0.62  fof(f57,plain,(
% 1.35/0.62    ( ! [X2,X0,X3,X1] : (~sP0(X3,X2,k3_xboole_0(X0,X1)) | r2_hidden(sK3(X0,X1),X2) | r1_xboole_0(X0,X1)) )),
% 1.35/0.62    inference(resolution,[],[f45,f38])).
% 1.35/0.62  fof(f38,plain,(
% 1.35/0.62    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.35/0.62    inference(cnf_transformation,[],[f24])).
% 1.35/0.62  fof(f45,plain,(
% 1.35/0.62    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~sP0(X0,X1,X2)) )),
% 1.35/0.62    inference(cnf_transformation,[],[f30])).
% 1.35/0.62  fof(f40,plain,(
% 1.35/0.62    ( ! [X0,X1] : (k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) | r2_hidden(X1,X0)) )),
% 1.35/0.62    inference(cnf_transformation,[],[f17])).
% 1.35/0.62  fof(f17,plain,(
% 1.35/0.62    ! [X0,X1] : (r2_hidden(X1,X0) | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)))),
% 1.35/0.62    inference(ennf_transformation,[],[f9])).
% 1.35/0.62  fof(f9,axiom,(
% 1.35/0.62    ! [X0,X1] : (k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) => r2_hidden(X1,X0))),
% 1.35/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).
% 1.35/0.62  fof(f1300,plain,(
% 1.35/0.62    ( ! [X12,X13] : (k1_xboole_0 = k1_tarski(X13) | k3_xboole_0(X13,X12) = k1_setfam_1(k2_tarski(X13,X12))) )),
% 1.35/0.62    inference(subsumption_resolution,[],[f124,f1290])).
% 1.35/0.62  fof(f124,plain,(
% 1.35/0.62    ( ! [X12,X13] : (k1_xboole_0 = k1_tarski(X12) | k1_xboole_0 = k1_tarski(X13) | k3_xboole_0(X13,X12) = k1_setfam_1(k2_tarski(X13,X12))) )),
% 1.35/0.62    inference(resolution,[],[f119,f52])).
% 1.35/0.62  fof(f119,plain,(
% 1.35/0.62    ( ! [X0,X1] : (sP0(X1,X0,k1_setfam_1(k2_tarski(X0,X1))) | k1_xboole_0 = k1_tarski(X1) | k1_xboole_0 = k1_tarski(X0)) )),
% 1.35/0.62    inference(forward_demodulation,[],[f118,f33])).
% 1.35/0.62  fof(f33,plain,(
% 1.35/0.62    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 1.35/0.62    inference(cnf_transformation,[],[f11])).
% 1.35/0.62  fof(f11,axiom,(
% 1.35/0.62    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 1.35/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
% 1.35/0.62  fof(f118,plain,(
% 1.35/0.62    ( ! [X0,X1] : (sP0(k1_setfam_1(k1_tarski(X1)),X0,k1_setfam_1(k2_tarski(X0,X1))) | k1_xboole_0 = k1_tarski(X1) | k1_xboole_0 = k1_tarski(X0)) )),
% 1.35/0.62    inference(forward_demodulation,[],[f117,f33])).
% 1.35/0.62  fof(f117,plain,(
% 1.35/0.62    ( ! [X0,X1] : (sP0(k1_setfam_1(k1_tarski(X1)),k1_setfam_1(k1_tarski(X0)),k1_setfam_1(k2_tarski(X0,X1))) | k1_xboole_0 = k1_tarski(X1) | k1_xboole_0 = k1_tarski(X0)) )),
% 1.35/0.62    inference(superposition,[],[f79,f36])).
% 1.35/0.62  fof(f36,plain,(
% 1.35/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.35/0.62    inference(cnf_transformation,[],[f5])).
% 1.35/0.62  fof(f5,axiom,(
% 1.35/0.62    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 1.35/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 1.35/0.62  fof(f79,plain,(
% 1.35/0.62    ( ! [X14,X13] : (sP0(k1_setfam_1(X14),k1_setfam_1(X13),k1_setfam_1(k2_xboole_0(X13,X14))) | k1_xboole_0 = X14 | k1_xboole_0 = X13) )),
% 1.35/0.62    inference(superposition,[],[f53,f43])).
% 1.35/0.62  fof(f43,plain,(
% 1.35/0.62    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 1.35/0.62    inference(cnf_transformation,[],[f18])).
% 1.35/0.62  fof(f18,plain,(
% 1.35/0.62    ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 1.35/0.62    inference(ennf_transformation,[],[f10])).
% 1.35/0.62  fof(f10,axiom,(
% 1.35/0.62    ! [X0,X1] : ~(k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 1.35/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).
% 1.35/0.62  fof(f32,plain,(
% 1.35/0.62    k3_xboole_0(sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2))),
% 1.35/0.62    inference(cnf_transformation,[],[f22])).
% 1.35/0.62  fof(f22,plain,(
% 1.35/0.62    k3_xboole_0(sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2))),
% 1.35/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f15,f21])).
% 1.35/0.62  fof(f21,plain,(
% 1.35/0.62    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) => k3_xboole_0(sK1,sK2) != k1_setfam_1(k2_tarski(sK1,sK2))),
% 1.35/0.62    introduced(choice_axiom,[])).
% 1.35/0.62  fof(f15,plain,(
% 1.35/0.62    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))),
% 1.35/0.62    inference(ennf_transformation,[],[f13])).
% 1.35/0.62  fof(f13,negated_conjecture,(
% 1.35/0.62    ~! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.35/0.62    inference(negated_conjecture,[],[f12])).
% 1.35/0.62  fof(f12,conjecture,(
% 1.35/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.35/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.35/0.62  % SZS output end Proof for theBenchmark
% 1.35/0.62  % (2228)------------------------------
% 1.35/0.62  % (2228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.62  % (2228)Termination reason: Refutation
% 1.35/0.62  
% 1.35/0.62  % (2228)Memory used [KB]: 7036
% 1.35/0.62  % (2228)Time elapsed: 0.167 s
% 1.35/0.62  % (2228)------------------------------
% 1.35/0.62  % (2228)------------------------------
% 1.35/0.62  % (2220)Success in time 0.255 s
%------------------------------------------------------------------------------
