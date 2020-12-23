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
% DateTime   : Thu Dec  3 12:37:30 EST 2020

% Result     : Theorem 3.16s
% Output     : Refutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 181 expanded)
%              Number of leaves         :   23 (  65 expanded)
%              Depth                    :   18
%              Number of atoms          :  171 ( 282 expanded)
%              Number of equality atoms :   86 ( 168 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2064,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f86,f150,f374,f1986,f1996,f2025,f2055])).

fof(f2055,plain,
    ( spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(avatar_contradiction_clause,[],[f2054])).

fof(f2054,plain,
    ( $false
    | spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f2053,f46])).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f2053,plain,
    ( k1_tarski(sK0) != k2_tarski(sK0,sK0)
    | spl3_1
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f2052,f505])).

fof(f505,plain,
    ( ! [X0] : k3_tarski(k1_tarski(X0)) = X0
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f504,f53])).

fof(f53,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f504,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k3_tarski(k1_tarski(X0))
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f500,f80])).

fof(f80,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0)) ),
    inference(superposition,[],[f47,f46])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f500,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,X0)
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(superposition,[],[f441,f493])).

fof(f493,plain,
    ( ! [X5] : k1_xboole_0 = k4_xboole_0(X5,X5)
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f490,f422])).

fof(f422,plain,
    ( ! [X4] : k1_xboole_0 = k3_xboole_0(X4,k1_xboole_0)
    | ~ spl3_5 ),
    inference(superposition,[],[f339,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f339,plain,
    ( ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f338])).

fof(f338,plain,
    ( spl3_5
  <=> ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f490,plain,
    ( ! [X5] : k4_xboole_0(X5,X5) = k3_xboole_0(X5,k1_xboole_0)
    | ~ spl3_3 ),
    inference(superposition,[],[f55,f478])).

fof(f478,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f132,f476])).

fof(f476,plain,
    ( ! [X12] : k2_xboole_0(X12,k1_xboole_0) = X12
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f466,f53])).

fof(f466,plain,
    ( ! [X12] : k2_xboole_0(X12,k1_xboole_0) = k5_xboole_0(X12,k1_xboole_0)
    | ~ spl3_3 ),
    inference(superposition,[],[f441,f320])).

fof(f320,plain,
    ( ! [X10] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X10)
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f309,f66])).

fof(f66,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f309,plain,
    ( ! [X10] :
        ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,X10)
        | ~ r1_tarski(k1_xboole_0,X10) )
    | ~ spl3_3 ),
    inference(superposition,[],[f226,f146])).

fof(f146,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl3_3
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f226,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(X1,X2) = k4_xboole_0(X1,X1)
      | ~ r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f96,f95])).

fof(f95,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f52,f45])).

fof(f45,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f96,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,X1)
      | ~ r1_tarski(X1,X2) ) ),
    inference(superposition,[],[f52,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f132,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f120,f52])).

fof(f120,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f51,f53])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f441,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k5_xboole_0(X2,k4_xboole_0(X3,X2)) ),
    inference(forward_demodulation,[],[f129,f97])).

fof(f97,plain,(
    ! [X4,X3] : k4_xboole_0(X3,X4) = k5_xboole_0(X3,k3_xboole_0(X4,X3)) ),
    inference(superposition,[],[f52,f44])).

fof(f129,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3))) = k2_xboole_0(X2,X3) ),
    inference(superposition,[],[f51,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f2052,plain,
    ( k2_tarski(sK0,sK0) != k3_tarski(k1_tarski(k1_tarski(sK0)))
    | spl3_1
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f2043,f46])).

fof(f2043,plain,
    ( k2_tarski(sK0,sK0) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK0)))
    | spl3_1
    | ~ spl3_16 ),
    inference(backward_demodulation,[],[f78,f1995])).

fof(f1995,plain,
    ( sK0 = sK1
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f1993])).

fof(f1993,plain,
    ( spl3_16
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f78,plain,
    ( k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl3_1
  <=> k2_tarski(sK0,sK1) = k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f2025,plain,
    ( spl3_16
    | spl3_15 ),
    inference(avatar_split_clause,[],[f2024,f1983,f1993])).

fof(f1983,plain,
    ( spl3_15
  <=> k2_tarski(sK0,sK1) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f2024,plain,
    ( sK0 = sK1
    | spl3_15 ),
    inference(trivial_inequality_removal,[],[f2021])).

fof(f2021,plain,
    ( k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1)
    | sK0 = sK1
    | spl3_15 ),
    inference(superposition,[],[f1985,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

fof(f1985,plain,
    ( k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f1983])).

fof(f1996,plain,
    ( spl3_16
    | spl3_14 ),
    inference(avatar_split_clause,[],[f1989,f1979,f1993])).

fof(f1979,plain,
    ( spl3_14
  <=> r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f1989,plain,
    ( sK0 = sK1
    | spl3_14 ),
    inference(resolution,[],[f1981,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

fof(f1981,plain,
    ( ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f1979])).

fof(f1986,plain,
    ( ~ spl3_14
    | ~ spl3_15
    | spl3_2 ),
    inference(avatar_split_clause,[],[f1969,f83,f1983,f1979])).

fof(f83,plain,
    ( spl3_2
  <=> k2_tarski(sK0,sK1) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f1969,plain,
    ( k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | ~ r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0))
    | spl3_2 ),
    inference(superposition,[],[f85,f463])).

fof(f463,plain,(
    ! [X6,X7] :
      ( k2_xboole_0(X7,X6) = k5_xboole_0(X7,X6)
      | ~ r1_xboole_0(X6,X7) ) ),
    inference(superposition,[],[f441,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f85,plain,
    ( k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f374,plain,
    ( spl3_5
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f327,f144,f338])).

fof(f327,plain,
    ( ! [X3] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X3)
    | ~ spl3_3 ),
    inference(superposition,[],[f320,f55])).

fof(f150,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f141,f144])).

fof(f141,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f53,f95])).

fof(f86,plain,
    ( ~ spl3_2
    | spl3_1 ),
    inference(avatar_split_clause,[],[f81,f76,f83])).

fof(f81,plain,
    ( k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | spl3_1 ),
    inference(superposition,[],[f78,f47])).

fof(f79,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f41,f76])).

fof(f41,plain,(
    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f34])).

fof(f34,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))
   => k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:38:07 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.22/0.51  % (15841)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (15851)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (15858)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.53  % (15839)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (15865)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (15843)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (15844)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (15842)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (15864)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (15840)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (15862)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (15840)Refutation not found, incomplete strategy% (15840)------------------------------
% 0.22/0.55  % (15840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (15840)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (15840)Memory used [KB]: 10746
% 0.22/0.55  % (15840)Time elapsed: 0.123 s
% 0.22/0.55  % (15840)------------------------------
% 0.22/0.55  % (15840)------------------------------
% 0.22/0.55  % (15868)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (15850)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (15850)Refutation not found, incomplete strategy% (15850)------------------------------
% 0.22/0.55  % (15850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (15850)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (15850)Memory used [KB]: 10618
% 0.22/0.55  % (15850)Time elapsed: 0.103 s
% 0.22/0.55  % (15850)------------------------------
% 0.22/0.55  % (15850)------------------------------
% 0.22/0.56  % (15854)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.56  % (15854)Refutation not found, incomplete strategy% (15854)------------------------------
% 0.22/0.56  % (15854)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (15854)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (15854)Memory used [KB]: 6140
% 0.22/0.56  % (15854)Time elapsed: 0.098 s
% 0.22/0.56  % (15854)------------------------------
% 0.22/0.56  % (15854)------------------------------
% 0.22/0.56  % (15861)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.56  % (15860)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.56  % (15862)Refutation not found, incomplete strategy% (15862)------------------------------
% 0.22/0.56  % (15862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (15862)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (15862)Memory used [KB]: 1663
% 0.22/0.56  % (15862)Time elapsed: 0.096 s
% 0.22/0.56  % (15862)------------------------------
% 0.22/0.56  % (15862)------------------------------
% 0.22/0.56  % (15838)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.56  % (15838)Refutation not found, incomplete strategy% (15838)------------------------------
% 0.22/0.56  % (15838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (15838)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (15838)Memory used [KB]: 1663
% 0.22/0.56  % (15838)Time elapsed: 0.134 s
% 0.22/0.56  % (15838)------------------------------
% 0.22/0.56  % (15838)------------------------------
% 0.22/0.56  % (15860)Refutation not found, incomplete strategy% (15860)------------------------------
% 0.22/0.56  % (15860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (15860)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (15860)Memory used [KB]: 1791
% 0.22/0.56  % (15860)Time elapsed: 0.138 s
% 0.22/0.56  % (15860)------------------------------
% 0.22/0.56  % (15860)------------------------------
% 0.22/0.56  % (15867)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.56  % (15845)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.46/0.56  % (15852)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.46/0.56  % (15859)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.46/0.56  % (15857)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.46/0.57  % (15848)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.46/0.57  % (15849)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.46/0.57  % (15853)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.46/0.57  % (15849)Refutation not found, incomplete strategy% (15849)------------------------------
% 1.46/0.57  % (15849)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.57  % (15859)Refutation not found, incomplete strategy% (15859)------------------------------
% 1.46/0.57  % (15859)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.57  % (15859)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.57  
% 1.46/0.57  % (15859)Memory used [KB]: 10746
% 1.46/0.57  % (15859)Time elapsed: 0.143 s
% 1.46/0.57  % (15859)------------------------------
% 1.46/0.57  % (15859)------------------------------
% 1.46/0.57  % (15849)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.57  
% 1.46/0.57  % (15849)Memory used [KB]: 10618
% 1.46/0.57  % (15849)Time elapsed: 0.144 s
% 1.46/0.57  % (15849)------------------------------
% 1.46/0.57  % (15849)------------------------------
% 1.46/0.57  % (15856)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.46/0.57  % (15856)Refutation not found, incomplete strategy% (15856)------------------------------
% 1.46/0.57  % (15856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.57  % (15856)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.57  
% 1.46/0.57  % (15856)Memory used [KB]: 10618
% 1.46/0.57  % (15856)Time elapsed: 0.158 s
% 1.46/0.57  % (15856)------------------------------
% 1.46/0.57  % (15856)------------------------------
% 1.46/0.58  % (15847)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.46/0.58  % (15847)Refutation not found, incomplete strategy% (15847)------------------------------
% 1.46/0.58  % (15847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.58  % (15847)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.58  
% 1.46/0.58  % (15847)Memory used [KB]: 10746
% 1.46/0.58  % (15847)Time elapsed: 0.158 s
% 1.46/0.58  % (15847)------------------------------
% 1.46/0.58  % (15847)------------------------------
% 1.46/0.58  % (15855)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.46/0.58  % (15866)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.46/0.58  % (15863)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 2.35/0.72  % (15874)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.35/0.73  % (15875)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.35/0.73  % (15878)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.35/0.73  % (15881)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.35/0.73  % (15876)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.35/0.73  % (15877)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.35/0.73  % (15879)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.35/0.73  % (15873)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.35/0.74  % (15872)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.35/0.74  % (15872)Refutation not found, incomplete strategy% (15872)------------------------------
% 2.35/0.74  % (15872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.35/0.74  % (15872)Termination reason: Refutation not found, incomplete strategy
% 2.35/0.74  
% 2.35/0.74  % (15872)Memory used [KB]: 6140
% 2.35/0.74  % (15872)Time elapsed: 0.143 s
% 2.35/0.74  % (15872)------------------------------
% 2.35/0.74  % (15872)------------------------------
% 2.69/0.76  % (15880)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 3.16/0.87  % (15843)Time limit reached!
% 3.16/0.87  % (15843)------------------------------
% 3.16/0.87  % (15843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.16/0.87  % (15843)Termination reason: Time limit
% 3.16/0.87  % (15843)Termination phase: Saturation
% 3.16/0.87  
% 3.16/0.87  % (15843)Memory used [KB]: 9338
% 3.16/0.87  % (15843)Time elapsed: 0.400 s
% 3.16/0.87  % (15843)------------------------------
% 3.16/0.87  % (15843)------------------------------
% 3.16/0.88  % (15874)Refutation found. Thanks to Tanya!
% 3.16/0.88  % SZS status Theorem for theBenchmark
% 3.16/0.88  % SZS output start Proof for theBenchmark
% 3.16/0.88  fof(f2064,plain,(
% 3.16/0.88    $false),
% 3.16/0.88    inference(avatar_sat_refutation,[],[f79,f86,f150,f374,f1986,f1996,f2025,f2055])).
% 3.16/0.88  fof(f2055,plain,(
% 3.16/0.88    spl3_1 | ~spl3_3 | ~spl3_5 | ~spl3_16),
% 3.16/0.88    inference(avatar_contradiction_clause,[],[f2054])).
% 3.16/0.88  fof(f2054,plain,(
% 3.16/0.88    $false | (spl3_1 | ~spl3_3 | ~spl3_5 | ~spl3_16)),
% 3.16/0.88    inference(subsumption_resolution,[],[f2053,f46])).
% 3.16/0.88  fof(f46,plain,(
% 3.16/0.88    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.16/0.88    inference(cnf_transformation,[],[f12])).
% 3.16/0.88  fof(f12,axiom,(
% 3.16/0.88    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.16/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 3.16/0.88  fof(f2053,plain,(
% 3.16/0.88    k1_tarski(sK0) != k2_tarski(sK0,sK0) | (spl3_1 | ~spl3_3 | ~spl3_5 | ~spl3_16)),
% 3.16/0.88    inference(forward_demodulation,[],[f2052,f505])).
% 3.16/0.88  fof(f505,plain,(
% 3.16/0.88    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) ) | (~spl3_3 | ~spl3_5)),
% 3.16/0.88    inference(forward_demodulation,[],[f504,f53])).
% 3.16/0.88  fof(f53,plain,(
% 3.16/0.88    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.16/0.88    inference(cnf_transformation,[],[f7])).
% 3.16/0.88  fof(f7,axiom,(
% 3.16/0.88    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 3.16/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 3.16/0.88  fof(f504,plain,(
% 3.16/0.88    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k3_tarski(k1_tarski(X0))) ) | (~spl3_3 | ~spl3_5)),
% 3.16/0.88    inference(forward_demodulation,[],[f500,f80])).
% 3.16/0.88  fof(f80,plain,(
% 3.16/0.88    ( ! [X0] : (k2_xboole_0(X0,X0) = k3_tarski(k1_tarski(X0))) )),
% 3.16/0.88    inference(superposition,[],[f47,f46])).
% 3.16/0.88  fof(f47,plain,(
% 3.16/0.88    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.16/0.88    inference(cnf_transformation,[],[f20])).
% 3.16/0.88  fof(f20,axiom,(
% 3.16/0.88    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.16/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 3.16/0.88  fof(f500,plain,(
% 3.16/0.88    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,X0)) ) | (~spl3_3 | ~spl3_5)),
% 3.16/0.88    inference(superposition,[],[f441,f493])).
% 3.16/0.88  fof(f493,plain,(
% 3.16/0.88    ( ! [X5] : (k1_xboole_0 = k4_xboole_0(X5,X5)) ) | (~spl3_3 | ~spl3_5)),
% 3.16/0.88    inference(forward_demodulation,[],[f490,f422])).
% 3.16/0.88  fof(f422,plain,(
% 3.16/0.88    ( ! [X4] : (k1_xboole_0 = k3_xboole_0(X4,k1_xboole_0)) ) | ~spl3_5),
% 3.16/0.88    inference(superposition,[],[f339,f44])).
% 3.16/0.88  fof(f44,plain,(
% 3.16/0.88    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.16/0.88    inference(cnf_transformation,[],[f1])).
% 3.16/0.88  fof(f1,axiom,(
% 3.16/0.88    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.16/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.16/0.88  fof(f339,plain,(
% 3.16/0.88    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)) ) | ~spl3_5),
% 3.16/0.88    inference(avatar_component_clause,[],[f338])).
% 3.16/0.88  fof(f338,plain,(
% 3.16/0.88    spl3_5 <=> ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)),
% 3.16/0.88    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 3.16/0.88  fof(f490,plain,(
% 3.16/0.88    ( ! [X5] : (k4_xboole_0(X5,X5) = k3_xboole_0(X5,k1_xboole_0)) ) | ~spl3_3),
% 3.16/0.88    inference(superposition,[],[f55,f478])).
% 3.16/0.88  fof(f478,plain,(
% 3.16/0.88    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_3),
% 3.16/0.88    inference(backward_demodulation,[],[f132,f476])).
% 3.16/0.88  fof(f476,plain,(
% 3.16/0.88    ( ! [X12] : (k2_xboole_0(X12,k1_xboole_0) = X12) ) | ~spl3_3),
% 3.16/0.88    inference(forward_demodulation,[],[f466,f53])).
% 3.16/0.88  fof(f466,plain,(
% 3.16/0.88    ( ! [X12] : (k2_xboole_0(X12,k1_xboole_0) = k5_xboole_0(X12,k1_xboole_0)) ) | ~spl3_3),
% 3.16/0.88    inference(superposition,[],[f441,f320])).
% 3.16/0.88  fof(f320,plain,(
% 3.16/0.88    ( ! [X10] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X10)) ) | ~spl3_3),
% 3.16/0.88    inference(subsumption_resolution,[],[f309,f66])).
% 3.16/0.88  fof(f66,plain,(
% 3.16/0.88    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.16/0.88    inference(cnf_transformation,[],[f5])).
% 3.16/0.88  fof(f5,axiom,(
% 3.16/0.88    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.16/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 3.16/0.88  fof(f309,plain,(
% 3.16/0.88    ( ! [X10] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X10) | ~r1_tarski(k1_xboole_0,X10)) ) | ~spl3_3),
% 3.16/0.88    inference(superposition,[],[f226,f146])).
% 3.16/0.88  fof(f146,plain,(
% 3.16/0.88    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl3_3),
% 3.16/0.88    inference(avatar_component_clause,[],[f144])).
% 3.16/0.88  fof(f144,plain,(
% 3.16/0.88    spl3_3 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 3.16/0.88    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 3.16/0.88  fof(f226,plain,(
% 3.16/0.88    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(X1,X1) | ~r1_tarski(X1,X2)) )),
% 3.16/0.88    inference(forward_demodulation,[],[f96,f95])).
% 3.16/0.88  fof(f95,plain,(
% 3.16/0.88    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 3.16/0.88    inference(superposition,[],[f52,f45])).
% 3.16/0.88  fof(f45,plain,(
% 3.16/0.88    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.16/0.88    inference(cnf_transformation,[],[f25])).
% 3.16/0.88  fof(f25,plain,(
% 3.16/0.88    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.16/0.88    inference(rectify,[],[f2])).
% 3.16/0.88  fof(f2,axiom,(
% 3.16/0.88    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.16/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 3.16/0.88  fof(f52,plain,(
% 3.16/0.88    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.16/0.88    inference(cnf_transformation,[],[f3])).
% 3.16/0.88  fof(f3,axiom,(
% 3.16/0.88    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.16/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.16/0.88  fof(f96,plain,(
% 3.16/0.88    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,X1) | ~r1_tarski(X1,X2)) )),
% 3.16/0.88    inference(superposition,[],[f52,f54])).
% 3.16/0.88  fof(f54,plain,(
% 3.16/0.88    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.16/0.88    inference(cnf_transformation,[],[f31])).
% 3.16/0.88  fof(f31,plain,(
% 3.16/0.88    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.16/0.88    inference(ennf_transformation,[],[f4])).
% 3.16/0.88  fof(f4,axiom,(
% 3.16/0.88    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.16/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 3.16/0.88  fof(f132,plain,(
% 3.16/0.88    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 3.16/0.88    inference(forward_demodulation,[],[f120,f52])).
% 3.16/0.88  fof(f120,plain,(
% 3.16/0.88    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) )),
% 3.16/0.88    inference(superposition,[],[f51,f53])).
% 3.16/0.88  fof(f51,plain,(
% 3.16/0.88    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 3.16/0.88    inference(cnf_transformation,[],[f10])).
% 3.16/0.88  fof(f10,axiom,(
% 3.16/0.88    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 3.16/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 3.16/0.88  fof(f55,plain,(
% 3.16/0.88    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.16/0.88    inference(cnf_transformation,[],[f6])).
% 3.16/0.88  fof(f6,axiom,(
% 3.16/0.88    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.16/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 3.16/0.88  fof(f441,plain,(
% 3.16/0.88    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k5_xboole_0(X2,k4_xboole_0(X3,X2))) )),
% 3.16/0.88    inference(forward_demodulation,[],[f129,f97])).
% 3.16/0.88  fof(f97,plain,(
% 3.16/0.88    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k5_xboole_0(X3,k3_xboole_0(X4,X3))) )),
% 3.16/0.88    inference(superposition,[],[f52,f44])).
% 3.16/0.88  fof(f129,plain,(
% 3.16/0.88    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3))) = k2_xboole_0(X2,X3)) )),
% 3.16/0.88    inference(superposition,[],[f51,f42])).
% 3.16/0.88  fof(f42,plain,(
% 3.16/0.88    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 3.16/0.88    inference(cnf_transformation,[],[f9])).
% 3.16/0.88  fof(f9,axiom,(
% 3.16/0.88    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 3.16/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 3.16/0.88  fof(f2052,plain,(
% 3.16/0.88    k2_tarski(sK0,sK0) != k3_tarski(k1_tarski(k1_tarski(sK0))) | (spl3_1 | ~spl3_16)),
% 3.16/0.88    inference(forward_demodulation,[],[f2043,f46])).
% 3.16/0.88  fof(f2043,plain,(
% 3.16/0.88    k2_tarski(sK0,sK0) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK0))) | (spl3_1 | ~spl3_16)),
% 3.16/0.88    inference(backward_demodulation,[],[f78,f1995])).
% 3.16/0.88  fof(f1995,plain,(
% 3.16/0.88    sK0 = sK1 | ~spl3_16),
% 3.16/0.88    inference(avatar_component_clause,[],[f1993])).
% 3.16/0.88  fof(f1993,plain,(
% 3.16/0.88    spl3_16 <=> sK0 = sK1),
% 3.16/0.88    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 3.16/0.88  fof(f78,plain,(
% 3.16/0.88    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1))) | spl3_1),
% 3.16/0.88    inference(avatar_component_clause,[],[f76])).
% 3.16/0.88  fof(f76,plain,(
% 3.16/0.88    spl3_1 <=> k2_tarski(sK0,sK1) = k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 3.16/0.88    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 3.16/0.88  fof(f2025,plain,(
% 3.16/0.88    spl3_16 | spl3_15),
% 3.16/0.88    inference(avatar_split_clause,[],[f2024,f1983,f1993])).
% 3.16/0.88  fof(f1983,plain,(
% 3.16/0.88    spl3_15 <=> k2_tarski(sK0,sK1) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 3.16/0.88    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 3.16/0.88  fof(f2024,plain,(
% 3.16/0.88    sK0 = sK1 | spl3_15),
% 3.16/0.88    inference(trivial_inequality_removal,[],[f2021])).
% 3.16/0.88  fof(f2021,plain,(
% 3.16/0.88    k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1) | sK0 = sK1 | spl3_15),
% 3.16/0.88    inference(superposition,[],[f1985,f43])).
% 3.16/0.88  fof(f43,plain,(
% 3.16/0.88    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 3.16/0.88    inference(cnf_transformation,[],[f28])).
% 3.16/0.88  fof(f28,plain,(
% 3.16/0.88    ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 3.16/0.88    inference(ennf_transformation,[],[f22])).
% 3.16/0.88  fof(f22,axiom,(
% 3.16/0.88    ! [X0,X1] : (X0 != X1 => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 3.16/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).
% 3.16/0.88  fof(f1985,plain,(
% 3.16/0.88    k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | spl3_15),
% 3.16/0.88    inference(avatar_component_clause,[],[f1983])).
% 3.16/0.88  fof(f1996,plain,(
% 3.16/0.88    spl3_16 | spl3_14),
% 3.16/0.88    inference(avatar_split_clause,[],[f1989,f1979,f1993])).
% 3.16/0.88  fof(f1979,plain,(
% 3.16/0.88    spl3_14 <=> r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0))),
% 3.16/0.88    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 3.16/0.88  fof(f1989,plain,(
% 3.16/0.88    sK0 = sK1 | spl3_14),
% 3.16/0.88    inference(resolution,[],[f1981,f49])).
% 3.16/0.88  fof(f49,plain,(
% 3.16/0.88    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 3.16/0.88    inference(cnf_transformation,[],[f30])).
% 3.16/0.88  fof(f30,plain,(
% 3.16/0.88    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1)),
% 3.16/0.88    inference(ennf_transformation,[],[f21])).
% 3.16/0.88  fof(f21,axiom,(
% 3.16/0.88    ! [X0,X1] : (X0 != X1 => r1_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 3.16/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).
% 3.16/0.88  fof(f1981,plain,(
% 3.16/0.88    ~r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) | spl3_14),
% 3.16/0.88    inference(avatar_component_clause,[],[f1979])).
% 3.16/0.88  fof(f1986,plain,(
% 3.16/0.88    ~spl3_14 | ~spl3_15 | spl3_2),
% 3.16/0.88    inference(avatar_split_clause,[],[f1969,f83,f1983,f1979])).
% 3.16/0.88  fof(f83,plain,(
% 3.16/0.88    spl3_2 <=> k2_tarski(sK0,sK1) = k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 3.16/0.88    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 3.16/0.88  fof(f1969,plain,(
% 3.16/0.88    k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | ~r1_xboole_0(k1_tarski(sK1),k1_tarski(sK0)) | spl3_2),
% 3.16/0.88    inference(superposition,[],[f85,f463])).
% 3.16/0.88  fof(f463,plain,(
% 3.16/0.88    ( ! [X6,X7] : (k2_xboole_0(X7,X6) = k5_xboole_0(X7,X6) | ~r1_xboole_0(X6,X7)) )),
% 3.16/0.88    inference(superposition,[],[f441,f64])).
% 3.16/0.88  fof(f64,plain,(
% 3.16/0.88    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.16/0.88    inference(cnf_transformation,[],[f33])).
% 3.16/0.88  fof(f33,plain,(
% 3.16/0.88    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 3.16/0.88    inference(ennf_transformation,[],[f26])).
% 3.16/0.88  fof(f26,plain,(
% 3.16/0.88    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 3.16/0.88    inference(unused_predicate_definition_removal,[],[f8])).
% 3.16/0.88  fof(f8,axiom,(
% 3.16/0.88    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.16/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 3.16/0.88  fof(f85,plain,(
% 3.16/0.88    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | spl3_2),
% 3.16/0.88    inference(avatar_component_clause,[],[f83])).
% 3.16/0.88  fof(f374,plain,(
% 3.16/0.88    spl3_5 | ~spl3_3),
% 3.16/0.88    inference(avatar_split_clause,[],[f327,f144,f338])).
% 3.16/0.88  fof(f327,plain,(
% 3.16/0.88    ( ! [X3] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X3)) ) | ~spl3_3),
% 3.16/0.88    inference(superposition,[],[f320,f55])).
% 3.16/0.88  fof(f150,plain,(
% 3.16/0.88    spl3_3),
% 3.16/0.88    inference(avatar_split_clause,[],[f141,f144])).
% 3.16/0.88  fof(f141,plain,(
% 3.16/0.88    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 3.16/0.88    inference(superposition,[],[f53,f95])).
% 3.16/0.88  fof(f86,plain,(
% 3.16/0.88    ~spl3_2 | spl3_1),
% 3.16/0.88    inference(avatar_split_clause,[],[f81,f76,f83])).
% 3.16/0.88  fof(f81,plain,(
% 3.16/0.88    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | spl3_1),
% 3.16/0.88    inference(superposition,[],[f78,f47])).
% 3.16/0.88  fof(f79,plain,(
% 3.16/0.88    ~spl3_1),
% 3.16/0.88    inference(avatar_split_clause,[],[f41,f76])).
% 3.16/0.88  fof(f41,plain,(
% 3.16/0.88    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 3.16/0.88    inference(cnf_transformation,[],[f35])).
% 3.16/0.88  fof(f35,plain,(
% 3.16/0.88    k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 3.16/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f34])).
% 3.16/0.88  fof(f34,plain,(
% 3.16/0.88    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1))) => k2_tarski(sK0,sK1) != k3_tarski(k2_tarski(k1_tarski(sK0),k1_tarski(sK1)))),
% 3.16/0.88    introduced(choice_axiom,[])).
% 3.16/0.88  fof(f27,plain,(
% 3.16/0.88    ? [X0,X1] : k2_tarski(X0,X1) != k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 3.16/0.88    inference(ennf_transformation,[],[f24])).
% 3.16/0.88  fof(f24,negated_conjecture,(
% 3.16/0.88    ~! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 3.16/0.88    inference(negated_conjecture,[],[f23])).
% 3.16/0.88  fof(f23,conjecture,(
% 3.16/0.88    ! [X0,X1] : k2_tarski(X0,X1) = k3_tarski(k2_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 3.16/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).
% 3.16/0.88  % SZS output end Proof for theBenchmark
% 3.16/0.88  % (15874)------------------------------
% 3.16/0.88  % (15874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.16/0.88  % (15874)Termination reason: Refutation
% 3.16/0.88  
% 3.16/0.88  % (15874)Memory used [KB]: 7675
% 3.16/0.88  % (15874)Time elapsed: 0.298 s
% 3.16/0.88  % (15874)------------------------------
% 3.16/0.88  % (15874)------------------------------
% 3.42/0.88  % (15837)Success in time 0.505 s
%------------------------------------------------------------------------------
