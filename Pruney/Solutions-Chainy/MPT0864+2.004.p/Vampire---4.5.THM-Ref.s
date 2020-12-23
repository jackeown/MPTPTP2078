%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:31 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 227 expanded)
%              Number of leaves         :   17 (  74 expanded)
%              Depth                    :   15
%              Number of atoms          :  189 ( 454 expanded)
%              Number of equality atoms :  134 ( 386 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f211,plain,(
    $false ),
    inference(subsumption_resolution,[],[f210,f79])).

fof(f79,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f210,plain,(
    ~ r1_tarski(sK0,sK0) ),
    inference(forward_demodulation,[],[f198,f65])).

fof(f65,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f32,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f35,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

% (3492)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
fof(f7,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f32,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f198,plain,(
    ~ r1_tarski(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k1_xboole_0)),sK0) ),
    inference(superposition,[],[f110,f176])).

fof(f176,plain,(
    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(subsumption_resolution,[],[f175,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_enumset1(X0,X0,X0,X0,X2),k3_enumset1(X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X3,k3_enumset1(X0,X0,X0,X1,X2))
      | k3_enumset1(X0,X0,X0,X0,X2) != X3 ) ),
    inference(definition_unfolding,[],[f58,f60,f61])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
      | k2_tarski(X0,X2) != X3 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3 ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ~ ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).

fof(f175,plain,
    ( ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(duplicate_literal_removal,[],[f173])).

fof(f173,plain,
    ( ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[],[f141,f155])).

fof(f155,plain,
    ( sK0 = sK1
    | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(subsumption_resolution,[],[f153,f83])).

fof(f153,plain,
    ( ~ r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)
    | sK0 = sK1 ),
    inference(superposition,[],[f140,f93])).

fof(f93,plain,
    ( sK0 = sK2
    | sK0 = sK1 ),
    inference(superposition,[],[f92,f91])).

fof(f91,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = sK1 ),
    inference(backward_demodulation,[],[f31,f90])).

fof(f90,plain,(
    k1_mcart_1(sK0) = sK1 ),
    inference(superposition,[],[f38,f30])).

fof(f30,plain,(
    sK0 = k4_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( sK0 = k2_mcart_1(sK0)
      | sK0 = k1_mcart_1(sK0) )
    & sK0 = k4_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( sK0 = k2_mcart_1(sK0)
        | sK0 = k1_mcart_1(sK0) )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK0 ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2,X1] : k4_tarski(X1,X2) = sK0
   => sK0 = k4_tarski(sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f38,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f31,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f92,plain,(
    k2_mcart_1(sK0) = sK2 ),
    inference(superposition,[],[f39,f30])).

fof(f39,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f14])).

fof(f140,plain,
    ( ~ r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2) ),
    inference(superposition,[],[f41,f116])).

fof(f116,plain,(
    k2_zfmisc_1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k3_enumset1(sK0,sK0,sK0,sK0,sK0) ),
    inference(superposition,[],[f66,f30])).

fof(f66,plain,(
    ! [X0,X1] : k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)) = k3_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f37,f63,f63,f63])).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f61])).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

% (3492)Refutation not found, incomplete strategy% (3492)------------------------------
% (3492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3492)Termination reason: Refutation not found, incomplete strategy

% (3492)Memory used [KB]: 10618
% (3492)Time elapsed: 0.116 s
% (3492)------------------------------
% (3492)------------------------------
fof(f37,plain,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
        & ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k2_zfmisc_1(X1,X0))
        | r1_tarski(X0,k2_zfmisc_1(X0,X1)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(f141,plain,
    ( ~ r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1) ),
    inference(superposition,[],[f40,f116])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f110,plain,(
    ! [X0] : ~ r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0))),X0) ),
    inference(resolution,[],[f81,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f81,plain,(
    ! [X1] : r2_hidden(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,k3_enumset1(X1,X1,X1,X1,X1)))) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,k3_enumset1(X1,X1,X1,X1,X1))))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f47,f64])).

fof(f64,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f34,f62,f63])).

fof(f34,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:20:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.50  % (3502)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (3486)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (3497)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.51  % (3502)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f211,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f210,f79])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(flattening,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.51  fof(f210,plain,(
% 0.21/0.51    ~r1_tarski(sK0,sK0)),
% 0.21/0.51    inference(forward_demodulation,[],[f198,f65])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 0.21/0.51    inference(definition_unfolding,[],[f32,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f35,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f36,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f49,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  % (3492)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.51  fof(f198,plain,(
% 0.21/0.51    ~r1_tarski(k3_tarski(k3_enumset1(sK0,sK0,sK0,sK0,k1_xboole_0)),sK0)),
% 0.21/0.51    inference(superposition,[],[f110,f176])).
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f175,f83])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r1_tarski(k3_enumset1(X0,X0,X0,X0,X2),k3_enumset1(X0,X0,X0,X1,X2))) )),
% 0.21/0.51    inference(equality_resolution,[],[f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (r1_tarski(X3,k3_enumset1(X0,X0,X0,X1,X2)) | k3_enumset1(X0,X0,X0,X0,X2) != X3) )),
% 0.21/0.51    inference(definition_unfolding,[],[f58,f60,f61])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) | k2_tarski(X0,X2) != X3) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 0.21/0.51    inference(flattening,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 0.21/0.51    inference(nnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_zfmisc_1)).
% 0.21/0.51  fof(f175,plain,(
% 0.21/0.51    ~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f173])).
% 0.21/0.51  fof(f173,plain,(
% 0.21/0.51    ~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.21/0.51    inference(superposition,[],[f141,f155])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    sK0 = sK1 | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f153,f83])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    ~r1_tarski(k3_enumset1(sK0,sK0,sK0,sK0,sK0),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | k1_xboole_0 = k3_enumset1(sK0,sK0,sK0,sK0,sK0) | sK0 = sK1),
% 0.21/0.51    inference(superposition,[],[f140,f93])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    sK0 = sK2 | sK0 = sK1),
% 0.21/0.51    inference(superposition,[],[f92,f91])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    sK0 = k2_mcart_1(sK0) | sK0 = sK1),
% 0.21/0.51    inference(backward_demodulation,[],[f31,f90])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    k1_mcart_1(sK0) = sK1),
% 0.21/0.51    inference(superposition,[],[f38,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    sK0 = k4_tarski(sK1,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    (sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & sK0 = k4_tarski(sK1,sK2)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f22,f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & ? [X2,X1] : k4_tarski(X1,X2) = sK0)),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ? [X2,X1] : k4_tarski(X1,X2) = sK0 => sK0 = k4_tarski(sK1,sK2)),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.52    inference(negated_conjecture,[],[f15])).
% 0.21/0.52  fof(f15,conjecture,(
% 0.21/0.52    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,axiom,(
% 0.21/0.52    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    k2_mcart_1(sK0) = sK2),
% 0.21/0.52    inference(superposition,[],[f39,f30])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    ~r1_tarski(k3_enumset1(sK2,sK2,sK2,sK2,sK2),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | k1_xboole_0 = k3_enumset1(sK2,sK2,sK2,sK2,sK2)),
% 0.21/0.52    inference(superposition,[],[f41,f116])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    k2_zfmisc_1(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK2,sK2,sK2,sK2,sK2)) = k3_enumset1(sK0,sK0,sK0,sK0,sK0)),
% 0.21/0.52    inference(superposition,[],[f66,f30])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_zfmisc_1(k3_enumset1(X0,X0,X0,X0,X0),k3_enumset1(X1,X1,X1,X1,X1)) = k3_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1),k4_tarski(X0,X1))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f37,f63,f63,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f33,f61])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.52  % (3492)Refutation not found, incomplete strategy% (3492)------------------------------
% 0.21/0.52  % (3492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (3492)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (3492)Memory used [KB]: 10618
% 0.21/0.52  % (3492)Time elapsed: 0.116 s
% 0.21/0.52  % (3492)------------------------------
% 0.21/0.52  % (3492)------------------------------
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(k4_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_zfmisc_1)).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k2_zfmisc_1(X1,X0)) & ~r1_tarski(X0,k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(X0,k2_zfmisc_1(X1,X0)) | r1_tarski(X0,k2_zfmisc_1(X0,X1))) => k1_xboole_0 = X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    ~r1_tarski(k3_enumset1(sK1,sK1,sK1,sK1,sK1),k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | k1_xboole_0 = k3_enumset1(sK1,sK1,sK1,sK1,sK1)),
% 0.21/0.52    inference(superposition,[],[f40,f116])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X0,X1)) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0))),X0)) )),
% 0.21/0.52    inference(resolution,[],[f81,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,axiom,(
% 0.21/0.52    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ( ! [X1] : (r2_hidden(X1,k3_tarski(k3_enumset1(X1,X1,X1,X1,k3_enumset1(X1,X1,X1,X1,X1))))) )),
% 0.21/0.52    inference(equality_resolution,[],[f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(X0,k3_tarski(k3_enumset1(X1,X1,X1,X1,k3_enumset1(X1,X1,X1,X1,X1)))) | X0 != X1) )),
% 0.21/0.52    inference(definition_unfolding,[],[f47,f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X0] : (k1_ordinal1(X0) = k3_tarski(k3_enumset1(X0,X0,X0,X0,k3_enumset1(X0,X0,X0,X0,X0)))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f34,f62,f63])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.21/0.52    inference(flattening,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (3502)------------------------------
% 0.21/0.52  % (3502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (3502)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (3502)Memory used [KB]: 6396
% 0.21/0.52  % (3502)Time elapsed: 0.016 s
% 0.21/0.52  % (3502)------------------------------
% 0.21/0.52  % (3502)------------------------------
% 0.21/0.52  % (3489)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (3474)Success in time 0.163 s
%------------------------------------------------------------------------------
