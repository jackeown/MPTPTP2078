%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 596 expanded)
%              Number of leaves         :    7 ( 127 expanded)
%              Depth                    :   40
%              Number of atoms          :  231 (2205 expanded)
%              Number of equality atoms :  190 (1658 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f445,plain,(
    $false ),
    inference(subsumption_resolution,[],[f442,f181])).

fof(f181,plain,(
    sK0 != sK1 ),
    inference(subsumption_resolution,[],[f180,f19])).

fof(f19,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( sK0 != sK3
    & sK0 != sK2
    & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3] :
        ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) )
   => ( sK0 != sK3
      & sK0 != sK2
      & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f180,plain,
    ( sK0 != sK1
    | sK0 = sK2 ),
    inference(inner_rewriting,[],[f179])).

fof(f179,plain,
    ( sK0 != sK1
    | sK1 = sK2 ),
    inference(superposition,[],[f20,f174])).

fof(f174,plain,
    ( sK1 = sK3
    | sK1 = sK2 ),
    inference(condensation,[],[f173])).

fof(f173,plain,(
    ! [X0] :
      ( sK1 = X0
      | sK1 = sK3
      | sK1 = sK2 ) ),
    inference(condensation,[],[f172])).

fof(f172,plain,(
    ! [X0,X1] :
      ( sK1 = X0
      | sK1 = X1
      | sK1 = sK3
      | sK1 = sK2 ) ),
    inference(subsumption_resolution,[],[f155,f35])).

fof(f35,plain,(
    ! [X2,X1] : r1_tarski(k1_xboole_0,k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f17])).

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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f155,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,k2_tarski(X0,X1))
      | sK1 = X0
      | sK1 = X1
      | sK1 = sK3
      | sK1 = sK2 ) ),
    inference(superposition,[],[f31,f149])).

fof(f149,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | sK1 = sK3
    | sK1 = sK2 ),
    inference(superposition,[],[f141,f41])).

fof(f41,plain,(
    ! [X2] : k1_tarski(X2) = k2_xboole_0(k1_xboole_0,k1_tarski(X2)) ),
    inference(resolution,[],[f24,f36])).

fof(f36,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,k1_tarski(X0)) ),
    inference(superposition,[],[f35,f21])).

fof(f21,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f141,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_tarski(sK1))
    | sK1 = sK3
    | sK1 = sK2 ),
    inference(superposition,[],[f132,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f132,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),k1_xboole_0)
    | sK1 = sK3
    | sK1 = sK2 ),
    inference(superposition,[],[f42,f115])).

fof(f115,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK1)
    | sK1 = sK3
    | sK1 = sK2 ),
    inference(resolution,[],[f106,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X1),k1_tarski(X0))
      | X0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X1),k1_tarski(X0))
      | X0 = X1
      | X0 = X1 ) ),
    inference(superposition,[],[f31,f21])).

fof(f106,plain,
    ( r1_tarski(k1_tarski(sK1),k1_tarski(sK2))
    | k1_xboole_0 = k2_tarski(sK0,sK1)
    | sK1 = sK3 ),
    inference(superposition,[],[f33,f97])).

fof(f97,plain,
    ( k2_tarski(sK0,sK1) = k1_tarski(sK2)
    | k1_xboole_0 = k2_tarski(sK0,sK1)
    | sK1 = sK3 ),
    inference(subsumption_resolution,[],[f88,f54])).

fof(f88,plain,
    ( r1_tarski(k1_tarski(sK1),k1_tarski(sK3))
    | k1_xboole_0 = k2_tarski(sK0,sK1)
    | k2_tarski(sK0,sK1) = k1_tarski(sK2)
    | sK1 = sK3 ),
    inference(superposition,[],[f33,f81])).

fof(f81,plain,
    ( k2_tarski(sK0,sK1) = k1_tarski(sK3)
    | k1_xboole_0 = k2_tarski(sK0,sK1)
    | k2_tarski(sK0,sK1) = k1_tarski(sK2)
    | sK1 = sK3 ),
    inference(subsumption_resolution,[],[f77,f20])).

fof(f77,plain,
    ( k2_tarski(sK0,sK1) = k1_tarski(sK2)
    | k1_xboole_0 = k2_tarski(sK0,sK1)
    | k2_tarski(sK0,sK1) = k1_tarski(sK3)
    | sK0 = sK3
    | sK1 = sK3 ),
    inference(resolution,[],[f70,f31])).

fof(f70,plain,
    ( r1_tarski(k1_tarski(sK3),k2_tarski(sK0,sK1))
    | k2_tarski(sK0,sK1) = k1_tarski(sK2)
    | k1_xboole_0 = k2_tarski(sK0,sK1)
    | k2_tarski(sK0,sK1) = k1_tarski(sK3) ),
    inference(superposition,[],[f33,f58])).

fof(f58,plain,
    ( k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3)
    | k2_tarski(sK0,sK1) = k1_tarski(sK2)
    | k1_xboole_0 = k2_tarski(sK0,sK1)
    | k2_tarski(sK0,sK1) = k1_tarski(sK3) ),
    inference(resolution,[],[f26,f18])).

fof(f18,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f15])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | k2_tarski(X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f33,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f42,plain,(
    ! [X4,X3] : k2_tarski(X4,X3) = k2_xboole_0(k1_tarski(X3),k2_tarski(X4,X3)) ),
    inference(resolution,[],[f24,f33])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k2_tarski(X1,X2))
      | X0 = X1
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( X0 = X2
      | X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(f20,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f15])).

fof(f442,plain,(
    sK0 = sK1 ),
    inference(resolution,[],[f435,f54])).

fof(f435,plain,(
    r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(superposition,[],[f34,f426])).

fof(f426,plain,(
    k2_tarski(sK0,sK1) = k1_tarski(sK1) ),
    inference(superposition,[],[f422,f42])).

fof(f422,plain,(
    k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k2_tarski(sK0,sK1)) ),
    inference(superposition,[],[f413,f22])).

fof(f413,plain,(
    k1_tarski(sK1) = k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK1)) ),
    inference(forward_demodulation,[],[f399,f21])).

fof(f399,plain,(
    k2_tarski(sK1,sK1) = k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK1,sK1)) ),
    inference(backward_demodulation,[],[f274,f397])).

fof(f397,plain,(
    sK1 = sK2 ),
    inference(condensation,[],[f396])).

fof(f396,plain,(
    ! [X0] :
      ( sK1 = X0
      | sK1 = sK2 ) ),
    inference(condensation,[],[f395])).

fof(f395,plain,(
    ! [X0,X1] :
      ( sK1 = X0
      | sK1 = X1
      | sK1 = sK2 ) ),
    inference(subsumption_resolution,[],[f378,f35])).

fof(f378,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,k2_tarski(X0,X1))
      | sK1 = X0
      | sK1 = X1
      | sK1 = sK2 ) ),
    inference(superposition,[],[f31,f371])).

fof(f371,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | sK1 = sK2 ),
    inference(superposition,[],[f363,f41])).

fof(f363,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_tarski(sK1))
    | sK1 = sK2 ),
    inference(superposition,[],[f342,f22])).

fof(f342,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),k1_xboole_0)
    | sK1 = sK2 ),
    inference(superposition,[],[f42,f328])).

fof(f328,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK1)
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f325,f181])).

fof(f325,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK1)
    | sK1 = sK2
    | sK0 = sK1 ),
    inference(resolution,[],[f316,f54])).

fof(f316,plain,
    ( r1_tarski(k1_tarski(sK0),k1_tarski(sK1))
    | k1_xboole_0 = k2_tarski(sK0,sK1)
    | sK1 = sK2 ),
    inference(superposition,[],[f34,f307])).

fof(f307,plain,
    ( k2_tarski(sK0,sK1) = k1_tarski(sK1)
    | k1_xboole_0 = k2_tarski(sK0,sK1)
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f298,f54])).

fof(f298,plain,
    ( r1_tarski(k1_tarski(sK1),k1_tarski(sK2))
    | k2_tarski(sK0,sK1) = k1_tarski(sK1)
    | k1_xboole_0 = k2_tarski(sK0,sK1)
    | sK1 = sK2 ),
    inference(superposition,[],[f33,f284])).

fof(f284,plain,
    ( k2_tarski(sK0,sK1) = k1_tarski(sK2)
    | k2_tarski(sK0,sK1) = k1_tarski(sK1)
    | k1_xboole_0 = k2_tarski(sK0,sK1)
    | sK1 = sK2 ),
    inference(backward_demodulation,[],[f195,f272])).

fof(f272,plain,(
    sK1 = sK3 ),
    inference(condensation,[],[f271])).

fof(f271,plain,(
    ! [X0] :
      ( sK1 = X0
      | sK1 = sK3 ) ),
    inference(condensation,[],[f270])).

fof(f270,plain,(
    ! [X0,X1] :
      ( sK1 = X0
      | sK1 = X1
      | sK1 = sK3 ) ),
    inference(subsumption_resolution,[],[f250,f35])).

fof(f250,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,k2_tarski(X0,X1))
      | sK1 = X0
      | sK1 = X1
      | sK1 = sK3 ) ),
    inference(superposition,[],[f31,f240])).

fof(f240,plain,
    ( k1_xboole_0 = k1_tarski(sK1)
    | sK1 = sK3 ),
    inference(superposition,[],[f230,f41])).

fof(f230,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_tarski(sK1))
    | sK1 = sK3 ),
    inference(superposition,[],[f218,f22])).

fof(f218,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),k1_xboole_0)
    | sK1 = sK3 ),
    inference(superposition,[],[f42,f201])).

fof(f201,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK1)
    | sK1 = sK3 ),
    inference(subsumption_resolution,[],[f198,f19])).

fof(f198,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK1)
    | sK1 = sK3
    | sK0 = sK2 ),
    inference(resolution,[],[f107,f54])).

fof(f107,plain,
    ( r1_tarski(k1_tarski(sK0),k1_tarski(sK2))
    | k1_xboole_0 = k2_tarski(sK0,sK1)
    | sK1 = sK3 ),
    inference(superposition,[],[f34,f97])).

fof(f195,plain,
    ( k2_tarski(sK0,sK1) = k1_tarski(sK2)
    | k1_xboole_0 = k2_tarski(sK0,sK1)
    | k2_tarski(sK0,sK1) = k1_tarski(sK3)
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f188,f19])).

fof(f188,plain,
    ( k2_tarski(sK0,sK1) = k1_tarski(sK2)
    | k1_xboole_0 = k2_tarski(sK0,sK1)
    | k2_tarski(sK0,sK1) = k1_tarski(sK3)
    | sK0 = sK2
    | sK1 = sK2 ),
    inference(resolution,[],[f71,f31])).

fof(f71,plain,
    ( r1_tarski(k1_tarski(sK2),k2_tarski(sK0,sK1))
    | k2_tarski(sK0,sK1) = k1_tarski(sK2)
    | k1_xboole_0 = k2_tarski(sK0,sK1)
    | k2_tarski(sK0,sK1) = k1_tarski(sK3) ),
    inference(superposition,[],[f34,f58])).

fof(f274,plain,(
    k2_tarski(sK2,sK1) = k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK1)) ),
    inference(backward_demodulation,[],[f45,f272])).

fof(f45,plain,(
    k2_tarski(sK2,sK3) = k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(resolution,[],[f24,f18])).

fof(f34,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:01:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.52  % (31364)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (31348)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (31357)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (31349)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (31357)Refutation not found, incomplete strategy% (31357)------------------------------
% 0.20/0.54  % (31357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (31344)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.55  % (31357)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (31357)Memory used [KB]: 6140
% 0.20/0.55  % (31357)Time elapsed: 0.109 s
% 0.20/0.55  % (31357)------------------------------
% 0.20/0.55  % (31357)------------------------------
% 0.20/0.55  % (31345)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.55  % (31362)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (31343)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.55  % (31349)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f445,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(subsumption_resolution,[],[f442,f181])).
% 0.20/0.55  fof(f181,plain,(
% 0.20/0.55    sK0 != sK1),
% 0.20/0.55    inference(subsumption_resolution,[],[f180,f19])).
% 0.20/0.55  fof(f19,plain,(
% 0.20/0.55    sK0 != sK2),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f15,plain,(
% 0.20/0.55    sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f14])).
% 0.20/0.55  fof(f14,plain,(
% 0.20/0.55    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3))) => (sK0 != sK3 & sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f10,plain,(
% 0.20/0.55    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.20/0.55    inference(ennf_transformation,[],[f9])).
% 0.20/0.55  fof(f9,negated_conjecture,(
% 0.20/0.55    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.20/0.55    inference(negated_conjecture,[],[f8])).
% 0.20/0.55  fof(f8,conjecture,(
% 0.20/0.55    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 0.20/0.55  fof(f180,plain,(
% 0.20/0.55    sK0 != sK1 | sK0 = sK2),
% 0.20/0.55    inference(inner_rewriting,[],[f179])).
% 0.20/0.55  fof(f179,plain,(
% 0.20/0.55    sK0 != sK1 | sK1 = sK2),
% 0.20/0.55    inference(superposition,[],[f20,f174])).
% 0.20/0.55  fof(f174,plain,(
% 0.20/0.55    sK1 = sK3 | sK1 = sK2),
% 0.20/0.55    inference(condensation,[],[f173])).
% 0.20/0.55  fof(f173,plain,(
% 0.20/0.55    ( ! [X0] : (sK1 = X0 | sK1 = sK3 | sK1 = sK2) )),
% 0.20/0.55    inference(condensation,[],[f172])).
% 0.20/0.55  fof(f172,plain,(
% 0.20/0.55    ( ! [X0,X1] : (sK1 = X0 | sK1 = X1 | sK1 = sK3 | sK1 = sK2) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f155,f35])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    ( ! [X2,X1] : (r1_tarski(k1_xboole_0,k2_tarski(X1,X2))) )),
% 0.20/0.55    inference(equality_resolution,[],[f27])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_xboole_0 != X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f17])).
% 0.20/0.55  fof(f17,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.20/0.55    inference(flattening,[],[f16])).
% 0.20/0.55  fof(f16,plain,(
% 0.20/0.55    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 0.20/0.55    inference(nnf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 0.20/0.55  fof(f155,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,k2_tarski(X0,X1)) | sK1 = X0 | sK1 = X1 | sK1 = sK3 | sK1 = sK2) )),
% 0.20/0.55    inference(superposition,[],[f31,f149])).
% 0.20/0.55  fof(f149,plain,(
% 0.20/0.55    k1_xboole_0 = k1_tarski(sK1) | sK1 = sK3 | sK1 = sK2),
% 0.20/0.55    inference(superposition,[],[f141,f41])).
% 0.20/0.55  fof(f41,plain,(
% 0.20/0.55    ( ! [X2] : (k1_tarski(X2) = k2_xboole_0(k1_xboole_0,k1_tarski(X2))) )),
% 0.20/0.55    inference(resolution,[],[f24,f36])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,k1_tarski(X0))) )),
% 0.20/0.55    inference(superposition,[],[f35,f21])).
% 0.20/0.55  fof(f21,plain,(
% 0.20/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.55  fof(f24,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f11])).
% 0.20/0.55  fof(f11,plain,(
% 0.20/0.55    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.55    inference(ennf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.55  fof(f141,plain,(
% 0.20/0.55    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_tarski(sK1)) | sK1 = sK3 | sK1 = sK2),
% 0.20/0.55    inference(superposition,[],[f132,f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f1])).
% 0.20/0.55  fof(f1,axiom,(
% 0.20/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.55  fof(f132,plain,(
% 0.20/0.55    k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),k1_xboole_0) | sK1 = sK3 | sK1 = sK2),
% 0.20/0.55    inference(superposition,[],[f42,f115])).
% 0.20/0.55  fof(f115,plain,(
% 0.20/0.55    k1_xboole_0 = k2_tarski(sK0,sK1) | sK1 = sK3 | sK1 = sK2),
% 0.20/0.55    inference(resolution,[],[f106,f54])).
% 0.20/0.55  fof(f54,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X1),k1_tarski(X0)) | X0 = X1) )),
% 0.20/0.55    inference(duplicate_literal_removal,[],[f53])).
% 0.20/0.55  fof(f53,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X1),k1_tarski(X0)) | X0 = X1 | X0 = X1) )),
% 0.20/0.55    inference(superposition,[],[f31,f21])).
% 0.20/0.55  fof(f106,plain,(
% 0.20/0.55    r1_tarski(k1_tarski(sK1),k1_tarski(sK2)) | k1_xboole_0 = k2_tarski(sK0,sK1) | sK1 = sK3),
% 0.20/0.55    inference(superposition,[],[f33,f97])).
% 0.20/0.55  fof(f97,plain,(
% 0.20/0.55    k2_tarski(sK0,sK1) = k1_tarski(sK2) | k1_xboole_0 = k2_tarski(sK0,sK1) | sK1 = sK3),
% 0.20/0.55    inference(subsumption_resolution,[],[f88,f54])).
% 0.20/0.55  fof(f88,plain,(
% 0.20/0.55    r1_tarski(k1_tarski(sK1),k1_tarski(sK3)) | k1_xboole_0 = k2_tarski(sK0,sK1) | k2_tarski(sK0,sK1) = k1_tarski(sK2) | sK1 = sK3),
% 0.20/0.55    inference(superposition,[],[f33,f81])).
% 0.20/0.55  fof(f81,plain,(
% 0.20/0.55    k2_tarski(sK0,sK1) = k1_tarski(sK3) | k1_xboole_0 = k2_tarski(sK0,sK1) | k2_tarski(sK0,sK1) = k1_tarski(sK2) | sK1 = sK3),
% 0.20/0.55    inference(subsumption_resolution,[],[f77,f20])).
% 0.20/0.55  fof(f77,plain,(
% 0.20/0.55    k2_tarski(sK0,sK1) = k1_tarski(sK2) | k1_xboole_0 = k2_tarski(sK0,sK1) | k2_tarski(sK0,sK1) = k1_tarski(sK3) | sK0 = sK3 | sK1 = sK3),
% 0.20/0.55    inference(resolution,[],[f70,f31])).
% 0.20/0.55  fof(f70,plain,(
% 0.20/0.55    r1_tarski(k1_tarski(sK3),k2_tarski(sK0,sK1)) | k2_tarski(sK0,sK1) = k1_tarski(sK2) | k1_xboole_0 = k2_tarski(sK0,sK1) | k2_tarski(sK0,sK1) = k1_tarski(sK3)),
% 0.20/0.55    inference(superposition,[],[f33,f58])).
% 0.20/0.55  fof(f58,plain,(
% 0.20/0.55    k2_tarski(sK0,sK1) = k2_tarski(sK2,sK3) | k2_tarski(sK0,sK1) = k1_tarski(sK2) | k1_xboole_0 = k2_tarski(sK0,sK1) | k2_tarski(sK0,sK1) = k1_tarski(sK3)),
% 0.20/0.55    inference(resolution,[],[f26,f18])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k2_tarski(X1,X2) = X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f17])).
% 0.20/0.55  fof(f33,plain,(
% 0.20/0.55    ( ! [X2,X1] : (r1_tarski(k1_tarski(X2),k2_tarski(X1,X2))) )),
% 0.20/0.55    inference(equality_resolution,[],[f29])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f17])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    ( ! [X4,X3] : (k2_tarski(X4,X3) = k2_xboole_0(k1_tarski(X3),k2_tarski(X4,X3))) )),
% 0.20/0.55    inference(resolution,[],[f24,f33])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) | X0 = X1 | X0 = X2) )),
% 0.20/0.55    inference(cnf_transformation,[],[f13])).
% 0.20/0.55  fof(f13,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (X0 = X2 | X0 = X1 | ~r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 0.20/0.55    inference(ennf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).
% 0.20/0.55  fof(f20,plain,(
% 0.20/0.55    sK0 != sK3),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f442,plain,(
% 0.20/0.55    sK0 = sK1),
% 0.20/0.55    inference(resolution,[],[f435,f54])).
% 0.20/0.55  fof(f435,plain,(
% 0.20/0.55    r1_tarski(k1_tarski(sK0),k1_tarski(sK1))),
% 0.20/0.55    inference(superposition,[],[f34,f426])).
% 0.20/0.55  fof(f426,plain,(
% 0.20/0.55    k2_tarski(sK0,sK1) = k1_tarski(sK1)),
% 0.20/0.55    inference(superposition,[],[f422,f42])).
% 0.20/0.55  fof(f422,plain,(
% 0.20/0.55    k1_tarski(sK1) = k2_xboole_0(k1_tarski(sK1),k2_tarski(sK0,sK1))),
% 0.20/0.55    inference(superposition,[],[f413,f22])).
% 0.20/0.55  fof(f413,plain,(
% 0.20/0.55    k1_tarski(sK1) = k2_xboole_0(k2_tarski(sK0,sK1),k1_tarski(sK1))),
% 0.20/0.55    inference(forward_demodulation,[],[f399,f21])).
% 0.20/0.55  fof(f399,plain,(
% 0.20/0.55    k2_tarski(sK1,sK1) = k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK1,sK1))),
% 0.20/0.55    inference(backward_demodulation,[],[f274,f397])).
% 0.20/0.55  fof(f397,plain,(
% 0.20/0.55    sK1 = sK2),
% 0.20/0.55    inference(condensation,[],[f396])).
% 0.20/0.55  fof(f396,plain,(
% 0.20/0.55    ( ! [X0] : (sK1 = X0 | sK1 = sK2) )),
% 0.20/0.55    inference(condensation,[],[f395])).
% 0.20/0.55  fof(f395,plain,(
% 0.20/0.55    ( ! [X0,X1] : (sK1 = X0 | sK1 = X1 | sK1 = sK2) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f378,f35])).
% 0.20/0.55  fof(f378,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,k2_tarski(X0,X1)) | sK1 = X0 | sK1 = X1 | sK1 = sK2) )),
% 0.20/0.55    inference(superposition,[],[f31,f371])).
% 0.20/0.55  fof(f371,plain,(
% 0.20/0.55    k1_xboole_0 = k1_tarski(sK1) | sK1 = sK2),
% 0.20/0.55    inference(superposition,[],[f363,f41])).
% 0.20/0.55  fof(f363,plain,(
% 0.20/0.55    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_tarski(sK1)) | sK1 = sK2),
% 0.20/0.55    inference(superposition,[],[f342,f22])).
% 0.20/0.55  fof(f342,plain,(
% 0.20/0.55    k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),k1_xboole_0) | sK1 = sK2),
% 0.20/0.55    inference(superposition,[],[f42,f328])).
% 0.20/0.55  fof(f328,plain,(
% 0.20/0.55    k1_xboole_0 = k2_tarski(sK0,sK1) | sK1 = sK2),
% 0.20/0.55    inference(subsumption_resolution,[],[f325,f181])).
% 0.20/0.55  fof(f325,plain,(
% 0.20/0.55    k1_xboole_0 = k2_tarski(sK0,sK1) | sK1 = sK2 | sK0 = sK1),
% 0.20/0.55    inference(resolution,[],[f316,f54])).
% 0.20/0.55  fof(f316,plain,(
% 0.20/0.55    r1_tarski(k1_tarski(sK0),k1_tarski(sK1)) | k1_xboole_0 = k2_tarski(sK0,sK1) | sK1 = sK2),
% 0.20/0.55    inference(superposition,[],[f34,f307])).
% 0.20/0.55  fof(f307,plain,(
% 0.20/0.55    k2_tarski(sK0,sK1) = k1_tarski(sK1) | k1_xboole_0 = k2_tarski(sK0,sK1) | sK1 = sK2),
% 0.20/0.55    inference(subsumption_resolution,[],[f298,f54])).
% 0.20/0.55  fof(f298,plain,(
% 0.20/0.55    r1_tarski(k1_tarski(sK1),k1_tarski(sK2)) | k2_tarski(sK0,sK1) = k1_tarski(sK1) | k1_xboole_0 = k2_tarski(sK0,sK1) | sK1 = sK2),
% 0.20/0.55    inference(superposition,[],[f33,f284])).
% 0.20/0.55  fof(f284,plain,(
% 0.20/0.55    k2_tarski(sK0,sK1) = k1_tarski(sK2) | k2_tarski(sK0,sK1) = k1_tarski(sK1) | k1_xboole_0 = k2_tarski(sK0,sK1) | sK1 = sK2),
% 0.20/0.55    inference(backward_demodulation,[],[f195,f272])).
% 0.20/0.55  fof(f272,plain,(
% 0.20/0.55    sK1 = sK3),
% 0.20/0.55    inference(condensation,[],[f271])).
% 0.20/0.55  fof(f271,plain,(
% 0.20/0.55    ( ! [X0] : (sK1 = X0 | sK1 = sK3) )),
% 0.20/0.55    inference(condensation,[],[f270])).
% 0.20/0.55  fof(f270,plain,(
% 0.20/0.55    ( ! [X0,X1] : (sK1 = X0 | sK1 = X1 | sK1 = sK3) )),
% 0.20/0.55    inference(subsumption_resolution,[],[f250,f35])).
% 0.20/0.55  fof(f250,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,k2_tarski(X0,X1)) | sK1 = X0 | sK1 = X1 | sK1 = sK3) )),
% 0.20/0.55    inference(superposition,[],[f31,f240])).
% 0.20/0.55  fof(f240,plain,(
% 0.20/0.55    k1_xboole_0 = k1_tarski(sK1) | sK1 = sK3),
% 0.20/0.55    inference(superposition,[],[f230,f41])).
% 0.20/0.55  fof(f230,plain,(
% 0.20/0.55    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_tarski(sK1)) | sK1 = sK3),
% 0.20/0.55    inference(superposition,[],[f218,f22])).
% 0.20/0.55  fof(f218,plain,(
% 0.20/0.55    k1_xboole_0 = k2_xboole_0(k1_tarski(sK1),k1_xboole_0) | sK1 = sK3),
% 0.20/0.55    inference(superposition,[],[f42,f201])).
% 0.20/0.55  fof(f201,plain,(
% 0.20/0.55    k1_xboole_0 = k2_tarski(sK0,sK1) | sK1 = sK3),
% 0.20/0.55    inference(subsumption_resolution,[],[f198,f19])).
% 0.20/0.55  fof(f198,plain,(
% 0.20/0.55    k1_xboole_0 = k2_tarski(sK0,sK1) | sK1 = sK3 | sK0 = sK2),
% 0.20/0.55    inference(resolution,[],[f107,f54])).
% 0.20/0.55  fof(f107,plain,(
% 0.20/0.55    r1_tarski(k1_tarski(sK0),k1_tarski(sK2)) | k1_xboole_0 = k2_tarski(sK0,sK1) | sK1 = sK3),
% 0.20/0.55    inference(superposition,[],[f34,f97])).
% 0.20/0.55  fof(f195,plain,(
% 0.20/0.55    k2_tarski(sK0,sK1) = k1_tarski(sK2) | k1_xboole_0 = k2_tarski(sK0,sK1) | k2_tarski(sK0,sK1) = k1_tarski(sK3) | sK1 = sK2),
% 0.20/0.55    inference(subsumption_resolution,[],[f188,f19])).
% 0.20/0.55  fof(f188,plain,(
% 0.20/0.55    k2_tarski(sK0,sK1) = k1_tarski(sK2) | k1_xboole_0 = k2_tarski(sK0,sK1) | k2_tarski(sK0,sK1) = k1_tarski(sK3) | sK0 = sK2 | sK1 = sK2),
% 0.20/0.55    inference(resolution,[],[f71,f31])).
% 0.20/0.55  fof(f71,plain,(
% 0.20/0.55    r1_tarski(k1_tarski(sK2),k2_tarski(sK0,sK1)) | k2_tarski(sK0,sK1) = k1_tarski(sK2) | k1_xboole_0 = k2_tarski(sK0,sK1) | k2_tarski(sK0,sK1) = k1_tarski(sK3)),
% 0.20/0.55    inference(superposition,[],[f34,f58])).
% 0.20/0.55  fof(f274,plain,(
% 0.20/0.55    k2_tarski(sK2,sK1) = k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK1))),
% 0.20/0.55    inference(backward_demodulation,[],[f45,f272])).
% 0.20/0.55  fof(f45,plain,(
% 0.20/0.55    k2_tarski(sK2,sK3) = k2_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 0.20/0.55    inference(resolution,[],[f24,f18])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    ( ! [X2,X1] : (r1_tarski(k1_tarski(X1),k2_tarski(X1,X2))) )),
% 0.20/0.55    inference(equality_resolution,[],[f28])).
% 0.20/0.55  fof(f28,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X1) != X0) )),
% 0.20/0.55    inference(cnf_transformation,[],[f17])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (31349)------------------------------
% 0.20/0.55  % (31349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (31349)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (31349)Memory used [KB]: 6396
% 0.20/0.55  % (31349)Time elapsed: 0.125 s
% 0.20/0.55  % (31349)------------------------------
% 0.20/0.55  % (31349)------------------------------
% 0.20/0.56  % (31341)Success in time 0.195 s
%------------------------------------------------------------------------------
