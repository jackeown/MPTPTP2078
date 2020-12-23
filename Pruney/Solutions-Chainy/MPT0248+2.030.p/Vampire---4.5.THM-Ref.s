%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:53 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   70 (1163 expanded)
%              Number of leaves         :   10 ( 354 expanded)
%              Depth                    :   19
%              Number of atoms          :  190 (3101 expanded)
%              Number of equality atoms :  152 (2772 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f172,plain,(
    $false ),
    inference(subsumption_resolution,[],[f171,f157])).

fof(f157,plain,(
    sK2 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(subsumption_resolution,[],[f42,f156])).

fof(f156,plain,(
    k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f41,f104,f155])).

fof(f155,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f154,f101])).

fof(f101,plain,
    ( sK1 != sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f97])).

fof(f97,plain,
    ( sK1 != sK2
    | sK1 != sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f75,f87])).

fof(f87,plain,
    ( sK1 = k2_xboole_0(sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f84,f68])).

fof(f68,plain,(
    r1_tarski(k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f53,f44])).

fof(f44,plain,(
    k2_xboole_0(sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f21,f40])).

fof(f40,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f35,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f21,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f53,plain,(
    ! [X2,X1] : r1_tarski(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
      | k2_enumset1(X1,X1,X1,X2) != X0 ) ),
    inference(definition_unfolding,[],[f29,f39,f39])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k2_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_xboole_0(sK1,sK2))
      | k2_xboole_0(sK1,sK2) = X0
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f83,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f83,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_xboole_0(sK1,sK2))
      | k1_xboole_0 = X0
      | k2_xboole_0(sK1,sK2) = X0 ) ),
    inference(superposition,[],[f52,f44])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f30,f40,f40])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f75,plain,
    ( sK2 != k2_xboole_0(sK1,sK2)
    | sK1 != k2_xboole_0(sK1,sK2) ),
    inference(superposition,[],[f43,f44])).

fof(f43,plain,
    ( sK2 != k2_enumset1(sK0,sK0,sK0,sK0)
    | sK1 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f22,f40,f40])).

fof(f22,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f154,plain,
    ( sK1 = sK2
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f146])).

fof(f146,plain,
    ( sK1 = sK2
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f141,f116])).

fof(f116,plain,
    ( r1_tarski(k2_xboole_0(sK1,sK2),sK1)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f72,f104])).

fof(f72,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(sK1,sK2),k2_enumset1(sK0,sK0,sK0,X0)) ),
    inference(superposition,[],[f55,f44])).

fof(f55,plain,(
    ! [X2,X1] : r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
      | k2_enumset1(X1,X1,X1,X1) != X0 ) ),
    inference(definition_unfolding,[],[f27,f39,f40])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f141,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k2_xboole_0(X2,X1),sK1)
      | sK1 = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f99,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f99,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(k2_xboole_0(X3,X4),sK1)
      | sK1 = X3
      | k1_xboole_0 = X3
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f84,f87])).

fof(f104,plain,
    ( sK1 = k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK1
    | sK1 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f95,f52])).

fof(f95,plain,(
    ! [X0] :
      ( r1_tarski(sK1,k2_enumset1(X0,X0,X0,sK0))
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f69,f87])).

fof(f69,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(sK1,sK2),k2_enumset1(X0,X0,X0,sK0)) ),
    inference(superposition,[],[f54,f44])).

fof(f54,plain,(
    ! [X2,X1] : r1_tarski(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
      | k2_enumset1(X2,X2,X2,X2) != X0 ) ),
    inference(definition_unfolding,[],[f28,f39,f40])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f41,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f24,f40])).

fof(f24,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f42,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f23,f40])).

fof(f23,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f171,plain,(
    sK2 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(forward_demodulation,[],[f160,f59])).

fof(f59,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f34,f33])).

fof(f33,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f160,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k2_xboole_0(k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f44,f156])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.11/0.32  % Computer   : n005.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 15:49:17 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.18/0.43  % (15574)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.18/0.46  % (15574)Refutation found. Thanks to Tanya!
% 0.18/0.46  % SZS status Theorem for theBenchmark
% 0.18/0.46  % SZS output start Proof for theBenchmark
% 0.18/0.46  fof(f172,plain,(
% 0.18/0.46    $false),
% 0.18/0.46    inference(subsumption_resolution,[],[f171,f157])).
% 0.18/0.46  fof(f157,plain,(
% 0.18/0.46    sK2 != k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.18/0.46    inference(subsumption_resolution,[],[f42,f156])).
% 0.18/0.46  fof(f156,plain,(
% 0.18/0.46    k1_xboole_0 = sK1),
% 0.18/0.46    inference(global_subsumption,[],[f41,f104,f155])).
% 0.18/0.46  fof(f155,plain,(
% 0.18/0.46    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 0.18/0.46    inference(subsumption_resolution,[],[f154,f101])).
% 0.18/0.46  fof(f101,plain,(
% 0.18/0.46    sK1 != sK2 | k1_xboole_0 = sK1),
% 0.18/0.46    inference(trivial_inequality_removal,[],[f97])).
% 0.18/0.46  fof(f97,plain,(
% 0.18/0.46    sK1 != sK2 | sK1 != sK1 | k1_xboole_0 = sK1),
% 0.18/0.46    inference(superposition,[],[f75,f87])).
% 0.18/0.46  fof(f87,plain,(
% 0.18/0.46    sK1 = k2_xboole_0(sK1,sK2) | k1_xboole_0 = sK1),
% 0.18/0.46    inference(resolution,[],[f84,f68])).
% 0.18/0.46  fof(f68,plain,(
% 0.18/0.46    r1_tarski(k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,sK2))),
% 0.18/0.46    inference(superposition,[],[f53,f44])).
% 0.18/0.46  fof(f44,plain,(
% 0.18/0.46    k2_xboole_0(sK1,sK2) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.18/0.46    inference(definition_unfolding,[],[f21,f40])).
% 0.18/0.46  fof(f40,plain,(
% 0.18/0.46    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.18/0.46    inference(definition_unfolding,[],[f35,f39])).
% 0.18/0.46  fof(f39,plain,(
% 0.18/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.18/0.46    inference(definition_unfolding,[],[f37,f38])).
% 0.18/0.46  fof(f38,plain,(
% 0.18/0.46    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f6])).
% 0.18/0.46  fof(f6,axiom,(
% 0.18/0.46    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.18/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.18/0.46  fof(f37,plain,(
% 0.18/0.46    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f5])).
% 0.18/0.46  fof(f5,axiom,(
% 0.18/0.46    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.18/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.18/0.46  fof(f35,plain,(
% 0.18/0.46    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f4])).
% 0.18/0.46  fof(f4,axiom,(
% 0.18/0.46    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.18/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.18/0.46  fof(f21,plain,(
% 0.18/0.46    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.18/0.46    inference(cnf_transformation,[],[f16])).
% 0.18/0.46  fof(f16,plain,(
% 0.18/0.46    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.18/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).
% 0.18/0.46  fof(f15,plain,(
% 0.18/0.46    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 0.18/0.46    introduced(choice_axiom,[])).
% 0.18/0.46  fof(f12,plain,(
% 0.18/0.46    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.18/0.46    inference(ennf_transformation,[],[f11])).
% 0.18/0.46  fof(f11,negated_conjecture,(
% 0.18/0.46    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.18/0.46    inference(negated_conjecture,[],[f10])).
% 0.18/0.46  fof(f10,conjecture,(
% 0.18/0.46    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.18/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.18/0.46  fof(f53,plain,(
% 0.18/0.46    ( ! [X2,X1] : (r1_tarski(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X1,X1,X1,X2))) )),
% 0.18/0.46    inference(equality_resolution,[],[f45])).
% 0.18/0.46  fof(f45,plain,(
% 0.18/0.46    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) | k2_enumset1(X1,X1,X1,X2) != X0) )),
% 0.18/0.46    inference(definition_unfolding,[],[f29,f39,f39])).
% 0.18/0.46  fof(f29,plain,(
% 0.18/0.46    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k2_tarski(X1,X2) != X0) )),
% 0.18/0.46    inference(cnf_transformation,[],[f18])).
% 0.18/0.46  fof(f18,plain,(
% 0.18/0.46    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.18/0.46    inference(flattening,[],[f17])).
% 0.18/0.46  fof(f17,plain,(
% 0.18/0.46    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.18/0.46    inference(nnf_transformation,[],[f13])).
% 0.18/0.46  fof(f13,plain,(
% 0.18/0.46    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.18/0.46    inference(ennf_transformation,[],[f8])).
% 0.18/0.46  fof(f8,axiom,(
% 0.18/0.46    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.18/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 0.18/0.46  fof(f84,plain,(
% 0.18/0.46    ( ! [X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),k2_xboole_0(sK1,sK2)) | k2_xboole_0(sK1,sK2) = X0 | k1_xboole_0 = X0) )),
% 0.18/0.46    inference(resolution,[],[f83,f36])).
% 0.18/0.46  fof(f36,plain,(
% 0.18/0.46    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f14])).
% 0.18/0.46  fof(f14,plain,(
% 0.18/0.46    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.18/0.46    inference(ennf_transformation,[],[f2])).
% 0.18/0.46  fof(f2,axiom,(
% 0.18/0.46    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.18/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.18/0.46  fof(f83,plain,(
% 0.18/0.46    ( ! [X0] : (~r1_tarski(X0,k2_xboole_0(sK1,sK2)) | k1_xboole_0 = X0 | k2_xboole_0(sK1,sK2) = X0) )),
% 0.18/0.46    inference(superposition,[],[f52,f44])).
% 0.18/0.46  fof(f52,plain,(
% 0.18/0.46    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 0.18/0.46    inference(definition_unfolding,[],[f30,f40,f40])).
% 0.18/0.46  fof(f30,plain,(
% 0.18/0.46    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.18/0.46    inference(cnf_transformation,[],[f20])).
% 0.18/0.46  fof(f20,plain,(
% 0.18/0.46    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.18/0.46    inference(flattening,[],[f19])).
% 0.18/0.46  fof(f19,plain,(
% 0.18/0.46    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.18/0.46    inference(nnf_transformation,[],[f7])).
% 0.18/0.46  fof(f7,axiom,(
% 0.18/0.46    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.18/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.18/0.46  fof(f75,plain,(
% 0.18/0.46    sK2 != k2_xboole_0(sK1,sK2) | sK1 != k2_xboole_0(sK1,sK2)),
% 0.18/0.46    inference(superposition,[],[f43,f44])).
% 0.18/0.46  fof(f43,plain,(
% 0.18/0.46    sK2 != k2_enumset1(sK0,sK0,sK0,sK0) | sK1 != k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.18/0.46    inference(definition_unfolding,[],[f22,f40,f40])).
% 0.18/0.46  fof(f22,plain,(
% 0.18/0.46    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 0.18/0.46    inference(cnf_transformation,[],[f16])).
% 0.18/0.46  fof(f154,plain,(
% 0.18/0.46    sK1 = sK2 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 0.18/0.46    inference(duplicate_literal_removal,[],[f146])).
% 0.18/0.46  fof(f146,plain,(
% 0.18/0.46    sK1 = sK2 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 0.18/0.46    inference(resolution,[],[f141,f116])).
% 0.18/0.46  fof(f116,plain,(
% 0.18/0.46    r1_tarski(k2_xboole_0(sK1,sK2),sK1) | k1_xboole_0 = sK1),
% 0.18/0.46    inference(superposition,[],[f72,f104])).
% 0.18/0.46  fof(f72,plain,(
% 0.18/0.46    ( ! [X0] : (r1_tarski(k2_xboole_0(sK1,sK2),k2_enumset1(sK0,sK0,sK0,X0))) )),
% 0.18/0.46    inference(superposition,[],[f55,f44])).
% 0.18/0.46  fof(f55,plain,(
% 0.18/0.46    ( ! [X2,X1] : (r1_tarski(k2_enumset1(X1,X1,X1,X1),k2_enumset1(X1,X1,X1,X2))) )),
% 0.18/0.46    inference(equality_resolution,[],[f47])).
% 0.18/0.46  fof(f47,plain,(
% 0.18/0.46    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) | k2_enumset1(X1,X1,X1,X1) != X0) )),
% 0.18/0.46    inference(definition_unfolding,[],[f27,f39,f40])).
% 0.18/0.46  fof(f27,plain,(
% 0.18/0.46    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X1) != X0) )),
% 0.18/0.46    inference(cnf_transformation,[],[f18])).
% 0.18/0.46  fof(f141,plain,(
% 0.18/0.46    ( ! [X2,X1] : (~r1_tarski(k2_xboole_0(X2,X1),sK1) | sK1 = X1 | k1_xboole_0 = X1 | k1_xboole_0 = sK1) )),
% 0.18/0.46    inference(superposition,[],[f99,f34])).
% 0.18/0.46  fof(f34,plain,(
% 0.18/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f1])).
% 0.18/0.46  fof(f1,axiom,(
% 0.18/0.46    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.18/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.18/0.46  fof(f99,plain,(
% 0.18/0.46    ( ! [X4,X3] : (~r1_tarski(k2_xboole_0(X3,X4),sK1) | sK1 = X3 | k1_xboole_0 = X3 | k1_xboole_0 = sK1) )),
% 0.18/0.46    inference(superposition,[],[f84,f87])).
% 0.18/0.46  fof(f104,plain,(
% 0.18/0.46    sK1 = k2_enumset1(sK0,sK0,sK0,sK0) | k1_xboole_0 = sK1),
% 0.18/0.46    inference(duplicate_literal_removal,[],[f102])).
% 0.18/0.46  fof(f102,plain,(
% 0.18/0.46    k1_xboole_0 = sK1 | k1_xboole_0 = sK1 | sK1 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.18/0.46    inference(resolution,[],[f95,f52])).
% 0.18/0.46  fof(f95,plain,(
% 0.18/0.46    ( ! [X0] : (r1_tarski(sK1,k2_enumset1(X0,X0,X0,sK0)) | k1_xboole_0 = sK1) )),
% 0.18/0.46    inference(superposition,[],[f69,f87])).
% 0.18/0.46  fof(f69,plain,(
% 0.18/0.46    ( ! [X0] : (r1_tarski(k2_xboole_0(sK1,sK2),k2_enumset1(X0,X0,X0,sK0))) )),
% 0.18/0.46    inference(superposition,[],[f54,f44])).
% 0.18/0.46  fof(f54,plain,(
% 0.18/0.46    ( ! [X2,X1] : (r1_tarski(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X1,X1,X1,X2))) )),
% 0.18/0.46    inference(equality_resolution,[],[f46])).
% 0.18/0.46  fof(f46,plain,(
% 0.18/0.46    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) | k2_enumset1(X2,X2,X2,X2) != X0) )),
% 0.18/0.46    inference(definition_unfolding,[],[f28,f39,f40])).
% 0.18/0.46  fof(f28,plain,(
% 0.18/0.46    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 0.18/0.46    inference(cnf_transformation,[],[f18])).
% 0.18/0.46  fof(f41,plain,(
% 0.18/0.46    k1_xboole_0 != sK2 | sK1 != k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.18/0.46    inference(definition_unfolding,[],[f24,f40])).
% 0.18/0.46  fof(f24,plain,(
% 0.18/0.46    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 0.18/0.46    inference(cnf_transformation,[],[f16])).
% 0.18/0.46  fof(f42,plain,(
% 0.18/0.46    k1_xboole_0 != sK1 | sK2 != k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.18/0.46    inference(definition_unfolding,[],[f23,f40])).
% 0.18/0.46  fof(f23,plain,(
% 0.18/0.46    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 0.18/0.46    inference(cnf_transformation,[],[f16])).
% 0.18/0.46  fof(f171,plain,(
% 0.18/0.46    sK2 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 0.18/0.46    inference(forward_demodulation,[],[f160,f59])).
% 0.18/0.46  fof(f59,plain,(
% 0.18/0.46    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.18/0.46    inference(superposition,[],[f34,f33])).
% 0.18/0.46  fof(f33,plain,(
% 0.18/0.46    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.18/0.46    inference(cnf_transformation,[],[f3])).
% 0.18/0.46  fof(f3,axiom,(
% 0.18/0.46    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.18/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.18/0.46  fof(f160,plain,(
% 0.18/0.46    k2_enumset1(sK0,sK0,sK0,sK0) = k2_xboole_0(k1_xboole_0,sK2)),
% 0.18/0.46    inference(backward_demodulation,[],[f44,f156])).
% 0.18/0.46  % SZS output end Proof for theBenchmark
% 0.18/0.46  % (15574)------------------------------
% 0.18/0.46  % (15574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.46  % (15574)Termination reason: Refutation
% 0.18/0.46  
% 0.18/0.46  % (15574)Memory used [KB]: 6268
% 0.18/0.46  % (15574)Time elapsed: 0.097 s
% 0.18/0.46  % (15574)------------------------------
% 0.18/0.46  % (15574)------------------------------
% 0.18/0.46  % (15568)Success in time 0.122 s
%------------------------------------------------------------------------------
