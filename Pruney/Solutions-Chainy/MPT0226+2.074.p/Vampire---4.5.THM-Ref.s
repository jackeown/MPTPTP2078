%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:23 EST 2020

% Result     : Theorem 40.79s
% Output     : Refutation 40.79s
% Verified   : 
% Statistics : Number of formulae       :  218 (30317 expanded)
%              Number of leaves         :   23 (9681 expanded)
%              Depth                    :   40
%              Number of atoms          :  335 (36091 expanded)
%              Number of equality atoms :  204 (30526 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27452,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f24003,f26633,f27451])).

fof(f27451,plain,(
    ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f27450])).

fof(f27450,plain,
    ( $false
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f27449,f32])).

fof(f32,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( X0 != X1
      & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
       => X0 = X1 ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

fof(f27449,plain,
    ( sK0 = sK1
    | ~ spl4_4 ),
    inference(duplicate_literal_removal,[],[f27448])).

fof(f27448,plain,
    ( sK0 = sK1
    | sK0 = sK1
    | ~ spl4_4 ),
    inference(resolution,[],[f27432,f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | X1 = X3
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f27432,plain,
    ( sP3(sK0,sK1,sK1)
    | ~ spl4_4 ),
    inference(resolution,[],[f27265,f84])).

fof(f84,plain,(
    ! [X0,X3] : sP3(X3,X3,X0) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( X1 != X3
      | sP3(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f27265,plain,
    ( ! [X0] :
        ( ~ sP3(X0,sK0,sK0)
        | sP3(X0,sK1,sK1) )
    | ~ spl4_4 ),
    inference(resolution,[],[f27063,f90])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_enumset1(X0,X0,X0,X1))
      | ~ sP3(X3,X1,X0) ) ),
    inference(forward_demodulation,[],[f83,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k2_enumset1(X0,X1,X2,X3)) ),
    inference(definition_unfolding,[],[f58,f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(definition_unfolding,[],[f59,f34])).

fof(f34,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_enumset1)).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | r2_hidden(X3,k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f54,f66])).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f65])).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f27063,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0))
        | sP3(X0,sK1,sK1) )
    | ~ spl4_4 ),
    inference(superposition,[],[f89,f24002])).

fof(f24002,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f24000])).

fof(f24000,plain,
    ( spl4_4
  <=> k2_enumset1(sK1,sK1,sK1,sK1) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X1))
      | sP3(X3,X1,X0) ) ),
    inference(forward_demodulation,[],[f82,f69])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( sP3(X3,X1,X0)
      | ~ r2_hidden(X3,k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1))) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f55,f66])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f26633,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f26632])).

fof(f26632,plain,
    ( $false
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f26631,f32])).

fof(f26631,plain,
    ( sK0 = sK1
    | ~ spl4_3 ),
    inference(duplicate_literal_removal,[],[f26630])).

fof(f26630,plain,
    ( sK0 = sK1
    | sK0 = sK1
    | ~ spl4_3 ),
    inference(resolution,[],[f26429,f53])).

fof(f26429,plain,
    ( sP3(sK0,sK1,sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f26423,f85])).

fof(f85,plain,(
    ! [X3,X1] : sP3(X3,X1,X3) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( X0 != X3
      | sP3(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f26423,plain,
    ( ! [X0] :
        ( ~ sP3(X0,sK1,sK0)
        | sP3(X0,sK1,sK1) )
    | ~ spl4_3 ),
    inference(resolution,[],[f26006,f90])).

fof(f26006,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK1))
        | sP3(X0,sK1,sK1) )
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f25060,f25913])).

fof(f25913,plain,
    ( ! [X1] : k2_enumset1(X1,sK1,sK0,sK0) = k2_enumset1(X1,X1,sK0,sK1)
    | ~ spl4_3 ),
    inference(superposition,[],[f25855,f25027])).

fof(f25027,plain,
    ( ! [X1] : k2_enumset1(X1,sK1,sK1,sK1) = k2_enumset1(X1,sK1,sK0,sK0)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f25002,f24756])).

fof(f24756,plain,
    ( ! [X74,X72,X75,X73] : k2_enumset1(X72,X73,X74,X75) = k5_enumset1(X72,X73,X74,X75,sK0,sK0,sK0)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f24713,f9356])).

fof(f9356,plain,(
    ! [X5] : k2_xboole_0(X5,k1_xboole_0) = X5 ),
    inference(backward_demodulation,[],[f525,f9354])).

fof(f9354,plain,(
    ! [X27] : k4_xboole_0(X27,k1_xboole_0) = X27 ),
    inference(subsumption_resolution,[],[f9353,f1779])).

fof(f1779,plain,(
    ! [X10,X11] : r1_tarski(k4_xboole_0(X10,X11),X10) ),
    inference(trivial_inequality_removal,[],[f1743])).

fof(f1743,plain,(
    ! [X10,X11] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k4_xboole_0(X10,X11),X10) ) ),
    inference(superposition,[],[f43,f1622])).

fof(f1622,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),X5) ),
    inference(resolution,[],[f1419,f579])).

fof(f579,plain,(
    ! [X4] :
      ( ~ r1_tarski(X4,k1_xboole_0)
      | k1_xboole_0 = X4 ) ),
    inference(trivial_inequality_removal,[],[f574])).

fof(f574,plain,(
    ! [X4] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = X4
      | ~ r1_tarski(X4,k1_xboole_0) ) ),
    inference(superposition,[],[f98,f451])).

fof(f451,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(backward_demodulation,[],[f430,f431])).

fof(f431,plain,(
    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f174,f35])).

fof(f35,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f174,plain,(
    ! [X0,X1] : k4_xboole_0(k5_xboole_0(X0,X0),X1) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f47,f35])).

fof(f47,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_xboole_1)).

fof(f430,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f174,f33])).

fof(f33,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f98,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != k4_xboole_0(X3,X2)
      | X2 = X3
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f38,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f1419,plain,(
    ! [X12,X13] : r1_tarski(k4_xboole_0(k4_xboole_0(X12,X13),X12),k1_xboole_0) ),
    inference(superposition,[],[f133,f135])).

fof(f135,plain,(
    ! [X23,X21,X22] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X21,X22),k4_xboole_0(X21,k4_xboole_0(X22,X23))) ),
    inference(superposition,[],[f35,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f133,plain,(
    ! [X14,X15,X16] : r1_tarski(k4_xboole_0(X14,X15),k4_xboole_0(X14,k4_xboole_0(X15,X16))) ),
    inference(superposition,[],[f95,f45])).

fof(f95,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(trivial_inequality_removal,[],[f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(X0,k2_xboole_0(X0,X1)) ) ),
    inference(superposition,[],[f43,f35])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f9353,plain,(
    ! [X27] :
      ( ~ r1_tarski(k4_xboole_0(X27,k1_xboole_0),X27)
      | k4_xboole_0(X27,k1_xboole_0) = X27 ) ),
    inference(forward_demodulation,[],[f8327,f8248])).

fof(f8248,plain,(
    ! [X13] : k2_xboole_0(k1_xboole_0,X13) = X13 ),
    inference(subsumption_resolution,[],[f8241,f1840])).

fof(f1840,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(resolution,[],[f1779,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f8241,plain,(
    ! [X13] :
      ( k2_xboole_0(k1_xboole_0,X13) = X13
      | ~ r1_tarski(X13,k2_xboole_0(k1_xboole_0,X13)) ) ),
    inference(trivial_inequality_removal,[],[f8167])).

fof(f8167,plain,(
    ! [X13] :
      ( k1_xboole_0 != k1_xboole_0
      | k2_xboole_0(k1_xboole_0,X13) = X13
      | ~ r1_tarski(X13,k2_xboole_0(k1_xboole_0,X13)) ) ),
    inference(superposition,[],[f98,f7640])).

fof(f7640,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),X1) ),
    inference(forward_demodulation,[],[f7639,f431])).

fof(f7639,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),X1) ),
    inference(forward_demodulation,[],[f7638,f33])).

fof(f7638,plain,(
    ! [X1] : k2_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k5_xboole_0(k2_xboole_0(k1_xboole_0,X1),k1_xboole_0),X1) ),
    inference(forward_demodulation,[],[f7579,f451])).

fof(f7579,plain,(
    ! [X1] : k4_xboole_0(k5_xboole_0(k2_xboole_0(k1_xboole_0,X1),k1_xboole_0),X1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(k1_xboole_0,X1),X1))) ),
    inference(superposition,[],[f47,f672])).

fof(f672,plain,(
    ! [X11] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X11),k2_xboole_0(k1_xboole_0,X11)) ),
    inference(superposition,[],[f147,f431])).

fof(f147,plain,(
    ! [X6,X7,X5] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(k2_xboole_0(X5,X7),X6)) ),
    inference(superposition,[],[f35,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_1)).

fof(f8327,plain,(
    ! [X27] :
      ( k4_xboole_0(X27,k1_xboole_0) = X27
      | ~ r1_tarski(k4_xboole_0(k2_xboole_0(k1_xboole_0,X27),k1_xboole_0),X27) ) ),
    inference(backward_demodulation,[],[f5948,f8248])).

fof(f5948,plain,(
    ! [X27] :
      ( k4_xboole_0(k2_xboole_0(k1_xboole_0,X27),k1_xboole_0) = X27
      | ~ r1_tarski(k4_xboole_0(k2_xboole_0(k1_xboole_0,X27),k1_xboole_0),X27) ) ),
    inference(resolution,[],[f580,f1672])).

fof(f1672,plain,(
    ! [X0] : r1_tarski(X0,k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1671,f860])).

fof(f860,plain,(
    ! [X10,X9] : k4_xboole_0(X10,k1_xboole_0) = k4_xboole_0(X10,k3_xboole_0(k1_xboole_0,X9)) ),
    inference(forward_demodulation,[],[f859,f33])).

fof(f859,plain,(
    ! [X10,X9] : k4_xboole_0(k5_xboole_0(X10,k1_xboole_0),k3_xboole_0(k1_xboole_0,X9)) = k4_xboole_0(X10,k1_xboole_0) ),
    inference(forward_demodulation,[],[f858,f525])).

fof(f858,plain,(
    ! [X10,X9] : k4_xboole_0(k5_xboole_0(X10,k1_xboole_0),k3_xboole_0(k1_xboole_0,X9)) = k2_xboole_0(k4_xboole_0(X10,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f841,f451])).

fof(f841,plain,(
    ! [X10,X9] : k4_xboole_0(k5_xboole_0(X10,k1_xboole_0),k3_xboole_0(k1_xboole_0,X9)) = k2_xboole_0(k4_xboole_0(X10,k1_xboole_0),k4_xboole_0(k1_xboole_0,k2_xboole_0(X10,k3_xboole_0(k1_xboole_0,X9)))) ),
    inference(superposition,[],[f47,f570])).

fof(f570,plain,(
    ! [X7] : k1_xboole_0 = k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X7)) ),
    inference(forward_demodulation,[],[f557,f451])).

fof(f557,plain,(
    ! [X6,X7] : k4_xboole_0(k1_xboole_0,k4_xboole_0(X6,X7)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X7)) ),
    inference(superposition,[],[f45,f451])).

fof(f1671,plain,(
    ! [X0] : r1_tarski(X0,k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k3_xboole_0(k1_xboole_0,X0))) ),
    inference(superposition,[],[f1453,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).

fof(f1453,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,k4_xboole_0(X0,k1_xboole_0))) ),
    inference(resolution,[],[f1397,f50])).

fof(f1397,plain,(
    ! [X2,X0] : r1_tarski(k4_xboole_0(X2,X0),k4_xboole_0(X2,k1_xboole_0)) ),
    inference(superposition,[],[f133,f35])).

fof(f580,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,X2)
      | X2 = X3
      | ~ r1_tarski(X2,X3) ) ),
    inference(trivial_inequality_removal,[],[f573])).

fof(f573,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 != k1_xboole_0
      | X2 = X3
      | ~ r1_tarski(X3,X2)
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f98,f42])).

fof(f525,plain,(
    ! [X5] : k4_xboole_0(X5,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X5,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f524,f33])).

fof(f524,plain,(
    ! [X5] : k4_xboole_0(k5_xboole_0(X5,k1_xboole_0),k1_xboole_0) = k2_xboole_0(k4_xboole_0(X5,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f516,f451])).

fof(f516,plain,(
    ! [X5] : k4_xboole_0(k5_xboole_0(X5,k1_xboole_0),k1_xboole_0) = k2_xboole_0(k4_xboole_0(X5,k1_xboole_0),k4_xboole_0(k1_xboole_0,k2_xboole_0(X5,k1_xboole_0))) ),
    inference(superposition,[],[f47,f431])).

fof(f24713,plain,
    ( ! [X74,X72,X75,X73] : k5_enumset1(X72,X73,X74,X75,sK0,sK0,sK0) = k2_xboole_0(k2_enumset1(X72,X73,X74,X75),k1_xboole_0)
    | ~ spl4_3 ),
    inference(superposition,[],[f262,f23998])).

fof(f23998,plain,
    ( k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f23996])).

fof(f23996,plain,
    ( spl4_3
  <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f262,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X4,X5,X6)) ),
    inference(backward_demodulation,[],[f79,f250])).

fof(f250,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(superposition,[],[f78,f69])).

fof(f78,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(definition_unfolding,[],[f60,f65])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_enumset1)).

fof(f79,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k5_enumset1(X4,X4,X4,X4,X4,X5,X6)) ),
    inference(definition_unfolding,[],[f62,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_enumset1)).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_enumset1)).

fof(f25002,plain,
    ( ! [X1] : k2_enumset1(X1,sK1,sK1,sK1) = k5_enumset1(X1,sK1,sK0,sK0,sK0,sK0,sK0)
    | ~ spl4_3 ),
    inference(superposition,[],[f24815,f238])).

fof(f238,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k5_enumset1(X0,X1,X2,X2,X2,X3,X4) ),
    inference(superposition,[],[f91,f79])).

fof(f91,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X0,X0,X1),k5_enumset1(X2,X2,X2,X3,X4,X5,X6)) ),
    inference(backward_demodulation,[],[f86,f78])).

fof(f86,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k2_enumset1(X3,X4,X5,X6))) ),
    inference(backward_demodulation,[],[f67,f69])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)),k2_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k2_enumset1(X3,X4,X5,X6))) ),
    inference(definition_unfolding,[],[f61,f66,f65])).

fof(f61,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_enumset1)).

fof(f24815,plain,
    ( ! [X18] : k5_enumset1(X18,X18,X18,sK1,sK0,sK0,sK0) = k2_enumset1(X18,sK1,sK1,sK1)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f24814,f24683])).

fof(f24683,plain,
    ( ! [X130] : k5_enumset1(X130,X130,X130,sK0,sK1,sK1,sK1) = k2_enumset1(X130,sK1,sK1,sK1)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f24682,f427])).

fof(f427,plain,(
    ! [X6,X8,X7,X5] : k2_enumset1(X5,X6,X7,X8) = k5_enumset1(X5,X5,X5,X6,X6,X7,X8) ),
    inference(forward_demodulation,[],[f411,f250])).

fof(f411,plain,(
    ! [X6,X8,X7,X5] : k5_enumset1(X5,X5,X5,X5,X6,X7,X8) = k5_enumset1(X5,X5,X5,X6,X6,X7,X8) ),
    inference(superposition,[],[f325,f262])).

fof(f325,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(forward_demodulation,[],[f295,f250])).

fof(f295,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(backward_demodulation,[],[f78,f280])).

fof(f280,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X1,X2,X3,X4,X4,X5,X6) ),
    inference(superposition,[],[f262,f64])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).

fof(f24682,plain,
    ( ! [X130] : k5_enumset1(X130,X130,X130,sK1,sK1,sK1,sK1) = k5_enumset1(X130,X130,X130,sK0,sK1,sK1,sK1)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f24654,f325])).

fof(f24654,plain,
    ( ! [X130] : k5_enumset1(X130,X130,X130,sK1,sK1,sK1,sK1) = k2_xboole_0(k2_enumset1(X130,X130,X130,X130),k2_enumset1(sK0,sK1,sK1,sK1))
    | ~ spl4_3 ),
    inference(superposition,[],[f325,f24290])).

fof(f24290,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k2_enumset1(sK0,sK1,sK1,sK1)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f24289,f9354])).

fof(f24289,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k4_xboole_0(k2_enumset1(sK0,sK1,sK1,sK1),k1_xboole_0)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f24080,f9354])).

fof(f24080,plain,
    ( k4_xboole_0(k2_enumset1(sK0,sK1,sK1,sK1),k1_xboole_0) = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0)
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f13869,f23998])).

fof(f13869,plain,(
    k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)) = k4_xboole_0(k2_enumset1(sK0,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(backward_demodulation,[],[f8619,f13867])).

fof(f13867,plain,(
    ! [X2,X0,X1] : k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,X0,X1,X2)) ),
    inference(forward_demodulation,[],[f13866,f9354])).

fof(f13866,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,X0,X1,X2)) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f13806,f250])).

fof(f13806,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,X0,X1,X2)) ),
    inference(superposition,[],[f8820,f225])).

fof(f225,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k1_xboole_0 = k4_xboole_0(k2_enumset1(X0,X1,X2,X3),k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) ),
    inference(superposition,[],[f35,f79])).

fof(f8820,plain,(
    ! [X6] : k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X6) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),X6)) ),
    inference(backward_demodulation,[],[f357,f8248])).

fof(f357,plain,(
    ! [X6] : k2_xboole_0(k1_xboole_0,k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X6)) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),X6)) ),
    inference(forward_demodulation,[],[f356,f250])).

fof(f356,plain,(
    ! [X6] : k2_xboole_0(k1_xboole_0,k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),X6)) = k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),X6)) ),
    inference(forward_demodulation,[],[f355,f280])).

fof(f355,plain,(
    ! [X6] : k2_xboole_0(k1_xboole_0,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X6)) = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),X6)) ),
    inference(forward_demodulation,[],[f318,f250])).

fof(f318,plain,(
    ! [X6] : k2_xboole_0(k1_xboole_0,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X6)) = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),X6)) ),
    inference(backward_demodulation,[],[f128,f280])).

fof(f128,plain,(
    ! [X6] : k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X6)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X6)) ),
    inference(superposition,[],[f45,f70])).

fof(f70,plain,(
    k1_xboole_0 = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f31,f34,f34])).

fof(f31,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f8619,plain,(
    k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)) = k4_xboole_0(k2_enumset1(sK0,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(backward_demodulation,[],[f428,f8248])).

fof(f428,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))) = k4_xboole_0(k2_enumset1(sK0,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(backward_demodulation,[],[f361,f427])).

fof(f361,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))) = k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(forward_demodulation,[],[f360,f325])).

fof(f360,plain,(
    k4_xboole_0(k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f359,f250])).

fof(f359,plain,(
    k4_xboole_0(k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f358,f250])).

fof(f358,plain,(
    k4_xboole_0(k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f319,f280])).

fof(f319,plain,(
    k4_xboole_0(k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f155,f280])).

fof(f155,plain,(
    k4_xboole_0(k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f37,f70])).

fof(f24814,plain,
    ( ! [X18] : k5_enumset1(X18,X18,X18,sK1,sK0,sK0,sK0) = k5_enumset1(X18,X18,X18,sK0,sK1,sK1,sK1)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f24792,f325])).

fof(f24792,plain,
    ( ! [X18] : k5_enumset1(X18,X18,X18,sK1,sK0,sK0,sK0) = k2_xboole_0(k2_enumset1(X18,X18,X18,X18),k2_enumset1(sK0,sK1,sK1,sK1))
    | ~ spl4_3 ),
    inference(superposition,[],[f325,f24339])).

fof(f24339,plain,
    ( k2_enumset1(sK0,sK1,sK1,sK1) = k2_enumset1(sK1,sK0,sK0,sK0)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f24338,f9354])).

fof(f24338,plain,
    ( k2_enumset1(sK1,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK1,sK1,sK1),k1_xboole_0)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f24337,f9354])).

fof(f24337,plain,
    ( k4_xboole_0(k2_enumset1(sK0,sK1,sK1,sK1),k1_xboole_0) = k4_xboole_0(k2_enumset1(sK1,sK0,sK0,sK0),k1_xboole_0)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f24081,f13749])).

fof(f13749,plain,(
    ! [X65] : k1_xboole_0 = k3_xboole_0(X65,k1_xboole_0) ),
    inference(forward_demodulation,[],[f13730,f35])).

fof(f13730,plain,(
    ! [X66,X65] : k3_xboole_0(X65,k1_xboole_0) = k4_xboole_0(X65,k2_xboole_0(X65,X66)) ),
    inference(superposition,[],[f8669,f9354])).

fof(f8669,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,X2) = k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X2)) ),
    inference(backward_demodulation,[],[f126,f8248])).

fof(f126,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X2)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X2)) ),
    inference(superposition,[],[f45,f35])).

fof(f24081,plain,
    ( k4_xboole_0(k2_enumset1(sK0,sK1,sK1,sK1),k1_xboole_0) = k4_xboole_0(k2_enumset1(sK1,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0))
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f13896,f23998])).

fof(f13896,plain,(
    k4_xboole_0(k2_enumset1(sK1,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))) = k4_xboole_0(k2_enumset1(sK0,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(backward_demodulation,[],[f9138,f13869])).

fof(f9138,plain,(
    k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)) = k4_xboole_0(k2_enumset1(sK1,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f1361,f8264])).

fof(f8264,plain,(
    ! [X21,X20] : k4_xboole_0(X20,X21) = k2_xboole_0(k4_xboole_0(X20,X21),k1_xboole_0) ),
    inference(backward_demodulation,[],[f571,f8248])).

fof(f571,plain,(
    ! [X21,X20] : k4_xboole_0(X20,X21) = k2_xboole_0(k4_xboole_0(X20,k2_xboole_0(k1_xboole_0,X21)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f565,f33])).

fof(f565,plain,(
    ! [X21,X20] : k4_xboole_0(k5_xboole_0(X20,k1_xboole_0),X21) = k2_xboole_0(k4_xboole_0(X20,k2_xboole_0(k1_xboole_0,X21)),k1_xboole_0) ),
    inference(superposition,[],[f47,f451])).

fof(f1361,plain,(
    k2_xboole_0(k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0) = k4_xboole_0(k2_enumset1(sK1,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f366,f1349])).

fof(f1349,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k5_enumset1(X4,X5,X5,X5,X5,X6,X7) ),
    inference(superposition,[],[f238,f427])).

fof(f366,plain,(
    k2_xboole_0(k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0) = k4_xboole_0(k5_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f365,f238])).

fof(f365,plain,(
    k2_xboole_0(k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0) = k4_xboole_0(k5_enumset1(sK1,sK1,sK1,sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f364,f325])).

fof(f364,plain,(
    k4_xboole_0(k2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))) = k2_xboole_0(k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f363,f250])).

fof(f363,plain,(
    k4_xboole_0(k2_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))) = k2_xboole_0(k4_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f362,f250])).

fof(f362,plain,(
    k4_xboole_0(k2_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k2_xboole_0(k4_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f320,f280])).

fof(f320,plain,(
    k4_xboole_0(k2_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k2_xboole_0(k4_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0) ),
    inference(backward_demodulation,[],[f158,f280])).

fof(f158,plain,(
    k4_xboole_0(k2_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k2_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0) ),
    inference(superposition,[],[f37,f70])).

fof(f25855,plain,
    ( ! [X1] : k2_enumset1(X1,sK1,sK1,sK1) = k2_enumset1(X1,X1,sK0,sK1)
    | ~ spl4_3 ),
    inference(superposition,[],[f25225,f427])).

fof(f25225,plain,
    ( ! [X130] : k5_enumset1(X130,X130,X130,sK1,sK1,sK1,sK1) = k2_enumset1(X130,X130,sK0,sK1)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f25197,f25116])).

fof(f25116,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X0,sK1,sK0,sK0)) = k2_enumset1(X1,X2,X0,sK1)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f25115,f25027])).

fof(f25115,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X0,sK1,sK1,sK1)) = k2_enumset1(X1,X2,X0,sK1)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f25004,f24756])).

fof(f25004,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X0,sK1,sK1,sK1)) = k5_enumset1(X1,X2,X0,sK1,sK0,sK0,sK0)
    | ~ spl4_3 ),
    inference(superposition,[],[f91,f24815])).

fof(f25197,plain,
    ( ! [X130] : k5_enumset1(X130,X130,X130,sK1,sK1,sK1,sK1) = k2_xboole_0(k2_enumset1(X130,X130,X130,X130),k2_enumset1(sK0,sK1,sK0,sK0))
    | ~ spl4_3 ),
    inference(superposition,[],[f325,f25049])).

fof(f25049,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k2_enumset1(sK0,sK1,sK0,sK0)
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f24290,f25027])).

fof(f25060,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_enumset1(sK0,sK1,sK0,sK0))
        | sP3(X0,sK1,sK1) )
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f24622,f25027])).

fof(f24622,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_enumset1(sK0,sK1,sK1,sK1))
        | sP3(X0,sK1,sK1) )
    | ~ spl4_3 ),
    inference(superposition,[],[f89,f24290])).

fof(f24003,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f407,f24000,f23996])).

fof(f407,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f324,f354])).

fof(f354,plain,(
    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f353,f250])).

fof(f353,plain,(
    r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f352,f280])).

fof(f352,plain,(
    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f317,f250])).

fof(f317,plain,(
    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(backward_demodulation,[],[f123,f280])).

fof(f123,plain,(
    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(trivial_inequality_removal,[],[f119])).

fof(f119,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(superposition,[],[f43,f70])).

fof(f324,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f323,f250])).

fof(f323,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1))
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f322,f280])).

fof(f322,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(forward_demodulation,[],[f294,f250])).

fof(f294,plain,(
    ! [X0,X1] :
      ( k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(backward_demodulation,[],[f73,f280])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f39,f34,f34])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:48:26 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.22/0.55  % (3859)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.56  % (3857)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.57  % (3875)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.57  % (3858)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.57  % (3865)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.57  % (3867)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.58  % (3873)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.58  % (3874)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.59  % (3866)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.59  % (3867)Refutation not found, incomplete strategy% (3867)------------------------------
% 0.22/0.59  % (3867)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (3867)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (3867)Memory used [KB]: 10618
% 0.22/0.59  % (3867)Time elapsed: 0.147 s
% 0.22/0.59  % (3867)------------------------------
% 0.22/0.59  % (3867)------------------------------
% 0.22/0.62  % (3854)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.62  % (3855)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.63  % (3860)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.63  % (3872)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.63  % (3868)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.63  % (3856)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.63  % (3870)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.64  % (3871)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.64  % (3880)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.64  % (3863)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.64  % (3852)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.64  % (3876)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.65  % (3864)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.65  % (3878)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.65  % (3879)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.65  % (3862)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.68  % (3853)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.69  % (3877)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.70  % (3869)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.70  % (3851)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.71  % (3861)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 3.07/0.79  % (3883)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 3.56/0.85  % (3875)Time limit reached!
% 3.56/0.85  % (3875)------------------------------
% 3.56/0.85  % (3875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.56/0.85  % (3875)Termination reason: Time limit
% 3.56/0.85  
% 3.56/0.85  % (3875)Memory used [KB]: 12792
% 3.56/0.85  % (3875)Time elapsed: 0.409 s
% 3.56/0.85  % (3875)------------------------------
% 3.56/0.85  % (3875)------------------------------
% 3.56/0.89  % (3854)Refutation not found, incomplete strategy% (3854)------------------------------
% 3.56/0.89  % (3854)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.56/0.89  % (3854)Termination reason: Refutation not found, incomplete strategy
% 3.56/0.89  
% 3.56/0.89  % (3854)Memory used [KB]: 6140
% 3.56/0.89  % (3854)Time elapsed: 0.443 s
% 3.56/0.89  % (3854)------------------------------
% 3.56/0.89  % (3854)------------------------------
% 4.25/0.95  % (3857)Time limit reached!
% 4.25/0.95  % (3857)------------------------------
% 4.25/0.95  % (3857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.25/0.95  % (3857)Termination reason: Time limit
% 4.25/0.95  
% 4.25/0.95  % (3857)Memory used [KB]: 14583
% 4.25/0.95  % (3857)Time elapsed: 0.502 s
% 4.25/0.95  % (3857)------------------------------
% 4.25/0.95  % (3857)------------------------------
% 4.25/0.96  % (3865)Time limit reached!
% 4.25/0.96  % (3865)------------------------------
% 4.25/0.96  % (3865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.25/0.96  % (3865)Termination reason: Time limit
% 4.25/0.96  
% 4.25/0.96  % (3865)Memory used [KB]: 5884
% 4.25/0.96  % (3865)Time elapsed: 0.508 s
% 4.25/0.96  % (3865)------------------------------
% 4.25/0.96  % (3865)------------------------------
% 4.72/1.02  % (3853)Time limit reached!
% 4.72/1.02  % (3853)------------------------------
% 4.72/1.02  % (3853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.72/1.02  % (3853)Termination reason: Time limit
% 4.72/1.02  
% 4.72/1.02  % (3853)Memory used [KB]: 6268
% 4.72/1.02  % (3853)Time elapsed: 0.548 s
% 4.72/1.02  % (3853)------------------------------
% 4.72/1.02  % (3853)------------------------------
% 4.72/1.04  % (3887)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 5.20/1.07  % (3892)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 5.32/1.08  % (3893)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 5.32/1.09  % (3858)Time limit reached!
% 5.32/1.09  % (3858)------------------------------
% 5.32/1.09  % (3858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.32/1.09  % (3858)Termination reason: Time limit
% 5.32/1.09  
% 5.32/1.09  % (3858)Memory used [KB]: 7803
% 5.32/1.09  % (3858)Time elapsed: 0.634 s
% 5.32/1.09  % (3858)------------------------------
% 5.32/1.09  % (3858)------------------------------
% 5.32/1.09  % (3891)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 5.32/1.10  % (3890)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 5.61/1.12  % (3890)Refutation not found, incomplete strategy% (3890)------------------------------
% 5.61/1.12  % (3890)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.61/1.12  % (3890)Termination reason: Refutation not found, incomplete strategy
% 5.61/1.12  
% 5.61/1.12  % (3890)Memory used [KB]: 6140
% 5.61/1.12  % (3890)Time elapsed: 0.192 s
% 5.61/1.12  % (3890)------------------------------
% 5.61/1.12  % (3890)------------------------------
% 5.61/1.13  % (3880)Time limit reached!
% 5.61/1.13  % (3880)------------------------------
% 5.61/1.13  % (3880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.61/1.13  % (3880)Termination reason: Time limit
% 5.61/1.13  
% 5.61/1.13  % (3880)Memory used [KB]: 35308
% 5.61/1.13  % (3880)Time elapsed: 0.656 s
% 5.61/1.13  % (3880)------------------------------
% 5.61/1.13  % (3880)------------------------------
% 5.78/1.21  % (3933)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 5.78/1.23  % (3935)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 6.71/1.26  % (3940)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 7.23/1.30  % (3852)Time limit reached!
% 7.23/1.30  % (3852)------------------------------
% 7.23/1.30  % (3852)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.23/1.30  % (3852)Termination reason: Time limit
% 7.23/1.30  
% 7.23/1.30  % (3852)Memory used [KB]: 6652
% 7.23/1.30  % (3852)Time elapsed: 0.813 s
% 7.23/1.30  % (3852)------------------------------
% 7.23/1.30  % (3852)------------------------------
% 8.09/1.41  % (4037)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 8.27/1.44  % (3863)Time limit reached!
% 8.27/1.44  % (3863)------------------------------
% 8.27/1.44  % (3863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.27/1.44  % (3863)Termination reason: Time limit
% 8.27/1.44  % (3863)Termination phase: Saturation
% 8.27/1.44  
% 8.27/1.44  % (3863)Memory used [KB]: 13944
% 8.27/1.44  % (3863)Time elapsed: 1.0000 s
% 8.27/1.44  % (3863)------------------------------
% 8.27/1.44  % (3863)------------------------------
% 8.27/1.49  % (3878)Time limit reached!
% 8.27/1.49  % (3878)------------------------------
% 8.27/1.49  % (3878)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.27/1.49  % (3878)Termination reason: Time limit
% 8.27/1.49  
% 8.27/1.49  % (3878)Memory used [KB]: 12025
% 8.27/1.49  % (3878)Time elapsed: 1.036 s
% 8.27/1.49  % (3878)------------------------------
% 8.27/1.49  % (3878)------------------------------
% 8.98/1.57  % (4071)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 9.47/1.63  % (4081)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 9.47/1.65  % (3851)Time limit reached!
% 9.47/1.65  % (3851)------------------------------
% 9.47/1.65  % (3851)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.47/1.65  % (3851)Termination reason: Time limit
% 9.47/1.65  % (3851)Termination phase: Saturation
% 9.47/1.65  
% 9.47/1.65  % (3851)Memory used [KB]: 12537
% 9.47/1.65  % (3851)Time elapsed: 1.200 s
% 9.47/1.65  % (3851)------------------------------
% 9.47/1.65  % (3851)------------------------------
% 10.72/1.75  % (3933)Time limit reached!
% 10.72/1.75  % (3933)------------------------------
% 10.72/1.75  % (3933)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.72/1.75  % (3933)Termination reason: Time limit
% 10.72/1.75  
% 10.72/1.75  % (3933)Memory used [KB]: 17398
% 10.72/1.75  % (3933)Time elapsed: 0.610 s
% 10.72/1.75  % (3933)------------------------------
% 10.72/1.75  % (3933)------------------------------
% 10.72/1.76  % (3856)Time limit reached!
% 10.72/1.76  % (3856)------------------------------
% 10.72/1.76  % (3856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.72/1.76  % (3856)Termination reason: Time limit
% 10.72/1.76  
% 10.72/1.76  % (3856)Memory used [KB]: 12025
% 10.72/1.76  % (3856)Time elapsed: 1.311 s
% 10.72/1.76  % (3856)------------------------------
% 10.72/1.76  % (3856)------------------------------
% 10.72/1.81  % (4129)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 11.46/1.87  % (4131)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 11.46/1.89  % (4130)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 13.18/2.07  % (3877)Time limit reached!
% 13.18/2.07  % (3877)------------------------------
% 13.18/2.07  % (3877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.18/2.08  % (3877)Termination reason: Time limit
% 13.18/2.08  
% 13.18/2.08  % (3877)Memory used [KB]: 20340
% 13.18/2.08  % (3877)Time elapsed: 1.615 s
% 13.18/2.08  % (3877)------------------------------
% 13.18/2.08  % (3877)------------------------------
% 13.70/2.16  % (4037)Time limit reached!
% 13.70/2.16  % (4037)------------------------------
% 13.70/2.16  % (4037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.70/2.17  % (4037)Termination reason: Time limit
% 13.70/2.17  % (4037)Termination phase: Saturation
% 13.70/2.17  
% 13.70/2.17  % (4037)Memory used [KB]: 17782
% 13.70/2.17  % (4037)Time elapsed: 0.800 s
% 13.70/2.17  % (4037)------------------------------
% 13.70/2.17  % (4037)------------------------------
% 13.70/2.17  % (4130)Time limit reached!
% 13.70/2.17  % (4130)------------------------------
% 13.70/2.17  % (4130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.70/2.17  % (4130)Termination reason: Time limit
% 13.70/2.17  % (4130)Termination phase: Saturation
% 13.70/2.17  
% 13.70/2.17  % (4130)Memory used [KB]: 14839
% 13.70/2.17  % (4130)Time elapsed: 0.400 s
% 13.70/2.17  % (4130)------------------------------
% 13.70/2.17  % (4130)------------------------------
% 14.37/2.22  % (4132)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 14.37/2.27  % (3871)Time limit reached!
% 14.37/2.27  % (3871)------------------------------
% 14.37/2.27  % (3871)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.37/2.27  % (3871)Termination reason: Time limit
% 14.37/2.27  % (3871)Termination phase: Saturation
% 14.37/2.27  
% 14.37/2.27  % (3871)Memory used [KB]: 31726
% 14.37/2.27  % (3871)Time elapsed: 1.800 s
% 14.37/2.27  % (3871)------------------------------
% 14.37/2.27  % (3871)------------------------------
% 14.74/2.28  % (4133)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 14.74/2.31  % (4134)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 15.44/2.40  % (4135)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 16.38/2.50  % (4132)Time limit reached!
% 16.38/2.50  % (4132)------------------------------
% 16.38/2.50  % (4132)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.81/2.52  % (4132)Termination reason: Time limit
% 16.81/2.52  % (4132)Termination phase: Saturation
% 16.81/2.52  
% 16.81/2.52  % (4132)Memory used [KB]: 7931
% 16.81/2.52  % (4132)Time elapsed: 0.400 s
% 16.81/2.52  % (4132)------------------------------
% 16.81/2.52  % (4132)------------------------------
% 17.24/2.61  % (4134)Time limit reached!
% 17.24/2.61  % (4134)------------------------------
% 17.24/2.61  % (4134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.24/2.62  % (4134)Termination reason: Time limit
% 17.24/2.62  
% 17.24/2.62  % (4134)Memory used [KB]: 10234
% 17.24/2.62  % (4134)Time elapsed: 0.424 s
% 17.24/2.62  % (4134)------------------------------
% 17.24/2.62  % (4134)------------------------------
% 17.24/2.64  % (4136)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 18.30/2.73  % (4133)Time limit reached!
% 18.30/2.73  % (4133)------------------------------
% 18.30/2.73  % (4133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.30/2.74  % (4133)Termination reason: Time limit
% 18.30/2.74  
% 18.30/2.74  % (4133)Memory used [KB]: 13048
% 18.30/2.74  % (4133)Time elapsed: 0.509 s
% 18.30/2.74  % (4133)------------------------------
% 18.30/2.74  % (4133)------------------------------
% 18.69/2.76  % (4137)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 19.14/2.85  % (3866)Time limit reached!
% 19.14/2.85  % (3866)------------------------------
% 19.14/2.85  % (3866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.14/2.85  % (3866)Termination reason: Time limit
% 19.14/2.85  % (3866)Termination phase: Saturation
% 19.14/2.85  
% 19.14/2.85  % (3866)Memory used [KB]: 23666
% 19.14/2.85  % (3866)Time elapsed: 2.400 s
% 19.14/2.85  % (3866)------------------------------
% 19.14/2.85  % (3866)------------------------------
% 20.46/2.98  % (4136)Time limit reached!
% 20.46/2.98  % (4136)------------------------------
% 20.46/2.98  % (4136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.46/2.98  % (4136)Termination reason: Time limit
% 20.46/2.98  % (4136)Termination phase: Saturation
% 20.46/2.98  
% 20.46/2.98  % (4136)Memory used [KB]: 4477
% 20.46/2.98  % (4136)Time elapsed: 0.400 s
% 20.46/2.98  % (4136)------------------------------
% 20.46/2.98  % (4136)------------------------------
% 21.21/3.09  % (4137)Time limit reached!
% 21.21/3.09  % (4137)------------------------------
% 21.21/3.09  % (4137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 21.21/3.09  % (4137)Termination reason: Time limit
% 21.21/3.09  
% 21.21/3.09  % (4137)Memory used [KB]: 8443
% 21.21/3.09  % (4137)Time elapsed: 0.443 s
% 21.21/3.09  % (4137)------------------------------
% 21.21/3.09  % (4137)------------------------------
% 24.79/3.54  % (3862)Time limit reached!
% 24.79/3.54  % (3862)------------------------------
% 24.79/3.54  % (3862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 24.79/3.54  % (3862)Termination reason: Time limit
% 24.79/3.54  % (3862)Termination phase: Saturation
% 24.79/3.54  
% 24.79/3.54  % (3862)Memory used [KB]: 45798
% 24.79/3.54  % (3862)Time elapsed: 3.100 s
% 24.79/3.54  % (3862)------------------------------
% 24.79/3.54  % (3862)------------------------------
% 25.31/3.58  % (3859)Time limit reached!
% 25.31/3.58  % (3859)------------------------------
% 25.31/3.58  % (3859)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 25.31/3.60  % (3859)Termination reason: Time limit
% 25.31/3.60  
% 25.31/3.60  % (3859)Memory used [KB]: 22643
% 25.31/3.60  % (3859)Time elapsed: 3.137 s
% 25.31/3.60  % (3859)------------------------------
% 25.31/3.60  % (3859)------------------------------
% 27.73/3.91  % (3870)Time limit reached!
% 27.73/3.91  % (3870)------------------------------
% 27.73/3.91  % (3870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 28.12/3.93  % (3870)Termination reason: Time limit
% 28.12/3.93  
% 28.12/3.93  % (3870)Memory used [KB]: 23411
% 28.12/3.93  % (3870)Time elapsed: 3.446 s
% 28.12/3.93  % (3870)------------------------------
% 28.12/3.93  % (3870)------------------------------
% 30.08/4.16  % (3940)Time limit reached!
% 30.08/4.16  % (3940)------------------------------
% 30.08/4.16  % (3940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 30.21/4.18  % (3940)Termination reason: Time limit
% 30.21/4.18  % (3940)Termination phase: Saturation
% 30.21/4.18  
% 30.21/4.18  % (3940)Memory used [KB]: 17270
% 30.21/4.18  % (3940)Time elapsed: 3.0000 s
% 30.21/4.18  % (3940)------------------------------
% 30.21/4.18  % (3940)------------------------------
% 31.84/4.40  % (3891)Time limit reached!
% 31.84/4.40  % (3891)------------------------------
% 31.84/4.40  % (3891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 31.84/4.41  % (3891)Termination reason: Time limit
% 31.84/4.41  % (3891)Termination phase: Saturation
% 31.84/4.41  
% 31.84/4.41  % (3891)Memory used [KB]: 56672
% 31.84/4.41  % (3891)Time elapsed: 3.400 s
% 31.84/4.41  % (3891)------------------------------
% 31.84/4.41  % (3891)------------------------------
% 32.62/4.51  % (3935)Time limit reached!
% 32.62/4.51  % (3935)------------------------------
% 32.62/4.51  % (3935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 32.95/4.52  % (3935)Termination reason: Time limit
% 32.95/4.52  
% 32.95/4.52  % (3935)Memory used [KB]: 26225
% 32.95/4.52  % (3935)Time elapsed: 3.335 s
% 32.95/4.52  % (3935)------------------------------
% 32.95/4.52  % (3935)------------------------------
% 38.66/5.30  % (3868)Time limit reached!
% 38.66/5.30  % (3868)------------------------------
% 38.66/5.30  % (3868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 39.25/5.30  % (3868)Termination reason: Time limit
% 39.25/5.30  % (3868)Termination phase: Saturation
% 39.25/5.30  
% 39.25/5.30  % (3868)Memory used [KB]: 51811
% 39.25/5.30  % (3868)Time elapsed: 4.800 s
% 39.25/5.30  % (3868)------------------------------
% 39.25/5.30  % (3868)------------------------------
% 40.79/5.50  % (4071)Refutation found. Thanks to Tanya!
% 40.79/5.50  % SZS status Theorem for theBenchmark
% 40.79/5.50  % SZS output start Proof for theBenchmark
% 40.79/5.50  fof(f27452,plain,(
% 40.79/5.50    $false),
% 40.79/5.50    inference(avatar_sat_refutation,[],[f24003,f26633,f27451])).
% 40.79/5.50  fof(f27451,plain,(
% 40.79/5.50    ~spl4_4),
% 40.79/5.50    inference(avatar_contradiction_clause,[],[f27450])).
% 40.79/5.50  fof(f27450,plain,(
% 40.79/5.50    $false | ~spl4_4),
% 40.79/5.50    inference(subsumption_resolution,[],[f27449,f32])).
% 40.79/5.50  fof(f32,plain,(
% 40.79/5.50    sK0 != sK1),
% 40.79/5.50    inference(cnf_transformation,[],[f26])).
% 40.79/5.50  fof(f26,plain,(
% 40.79/5.50    ? [X0,X1] : (X0 != X1 & k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 40.79/5.50    inference(ennf_transformation,[],[f25])).
% 40.79/5.50  fof(f25,negated_conjecture,(
% 40.79/5.50    ~! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 40.79/5.50    inference(negated_conjecture,[],[f24])).
% 40.79/5.50  fof(f24,conjecture,(
% 40.79/5.50    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 40.79/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).
% 40.79/5.50  fof(f27449,plain,(
% 40.79/5.50    sK0 = sK1 | ~spl4_4),
% 40.79/5.50    inference(duplicate_literal_removal,[],[f27448])).
% 40.79/5.50  fof(f27448,plain,(
% 40.79/5.50    sK0 = sK1 | sK0 = sK1 | ~spl4_4),
% 40.79/5.50    inference(resolution,[],[f27432,f53])).
% 40.79/5.50  fof(f53,plain,(
% 40.79/5.50    ( ! [X0,X3,X1] : (~sP3(X3,X1,X0) | X1 = X3 | X0 = X3) )),
% 40.79/5.50    inference(cnf_transformation,[],[f12])).
% 40.79/5.50  fof(f12,axiom,(
% 40.79/5.50    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 40.79/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 40.79/5.50  fof(f27432,plain,(
% 40.79/5.50    sP3(sK0,sK1,sK1) | ~spl4_4),
% 40.79/5.50    inference(resolution,[],[f27265,f84])).
% 40.79/5.50  fof(f84,plain,(
% 40.79/5.50    ( ! [X0,X3] : (sP3(X3,X3,X0)) )),
% 40.79/5.50    inference(equality_resolution,[],[f52])).
% 40.79/5.50  fof(f52,plain,(
% 40.79/5.50    ( ! [X0,X3,X1] : (X1 != X3 | sP3(X3,X1,X0)) )),
% 40.79/5.50    inference(cnf_transformation,[],[f12])).
% 40.79/5.50  fof(f27265,plain,(
% 40.79/5.50    ( ! [X0] : (~sP3(X0,sK0,sK0) | sP3(X0,sK1,sK1)) ) | ~spl4_4),
% 40.79/5.50    inference(resolution,[],[f27063,f90])).
% 40.79/5.50  fof(f90,plain,(
% 40.79/5.50    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_enumset1(X0,X0,X0,X1)) | ~sP3(X3,X1,X0)) )),
% 40.79/5.50    inference(forward_demodulation,[],[f83,f69])).
% 40.79/5.50  fof(f69,plain,(
% 40.79/5.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k2_enumset1(X0,X1,X2,X3))) )),
% 40.79/5.50    inference(definition_unfolding,[],[f58,f65])).
% 40.79/5.50  fof(f65,plain,(
% 40.79/5.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k2_enumset1(X1,X2,X3,X4))) )),
% 40.79/5.50    inference(definition_unfolding,[],[f59,f34])).
% 40.79/5.50  fof(f34,plain,(
% 40.79/5.50    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 40.79/5.50    inference(cnf_transformation,[],[f22])).
% 40.79/5.50  fof(f22,axiom,(
% 40.79/5.50    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)),
% 40.79/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_enumset1)).
% 40.79/5.50  fof(f59,plain,(
% 40.79/5.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 40.79/5.50    inference(cnf_transformation,[],[f15])).
% 40.79/5.50  fof(f15,axiom,(
% 40.79/5.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 40.79/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).
% 40.79/5.50  fof(f58,plain,(
% 40.79/5.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 40.79/5.50    inference(cnf_transformation,[],[f18])).
% 40.79/5.50  fof(f18,axiom,(
% 40.79/5.50    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 40.79/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 40.79/5.50  fof(f83,plain,(
% 40.79/5.50    ( ! [X0,X3,X1] : (~sP3(X3,X1,X0) | r2_hidden(X3,k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)))) )),
% 40.79/5.50    inference(equality_resolution,[],[f77])).
% 40.79/5.50  fof(f77,plain,(
% 40.79/5.50    ( ! [X2,X0,X3,X1] : (~sP3(X3,X1,X0) | r2_hidden(X3,X2) | k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) != X2) )),
% 40.79/5.50    inference(definition_unfolding,[],[f54,f66])).
% 40.79/5.50  fof(f66,plain,(
% 40.79/5.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1))) )),
% 40.79/5.50    inference(definition_unfolding,[],[f36,f65])).
% 40.79/5.50  fof(f36,plain,(
% 40.79/5.50    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 40.79/5.50    inference(cnf_transformation,[],[f20])).
% 40.79/5.50  fof(f20,axiom,(
% 40.79/5.50    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)),
% 40.79/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_enumset1)).
% 40.79/5.50  fof(f54,plain,(
% 40.79/5.50    ( ! [X2,X0,X3,X1] : (~sP3(X3,X1,X0) | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 40.79/5.50    inference(cnf_transformation,[],[f12])).
% 40.79/5.50  fof(f27063,plain,(
% 40.79/5.50    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK0)) | sP3(X0,sK1,sK1)) ) | ~spl4_4),
% 40.79/5.50    inference(superposition,[],[f89,f24002])).
% 40.79/5.50  fof(f24002,plain,(
% 40.79/5.50    k2_enumset1(sK1,sK1,sK1,sK1) = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl4_4),
% 40.79/5.50    inference(avatar_component_clause,[],[f24000])).
% 40.79/5.50  fof(f24000,plain,(
% 40.79/5.50    spl4_4 <=> k2_enumset1(sK1,sK1,sK1,sK1) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 40.79/5.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 40.79/5.50  fof(f89,plain,(
% 40.79/5.50    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X1)) | sP3(X3,X1,X0)) )),
% 40.79/5.50    inference(forward_demodulation,[],[f82,f69])).
% 40.79/5.50  fof(f82,plain,(
% 40.79/5.50    ( ! [X0,X3,X1] : (sP3(X3,X1,X0) | ~r2_hidden(X3,k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)))) )),
% 40.79/5.50    inference(equality_resolution,[],[f76])).
% 40.79/5.50  fof(f76,plain,(
% 40.79/5.50    ( ! [X2,X0,X3,X1] : (sP3(X3,X1,X0) | ~r2_hidden(X3,X2) | k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)) != X2) )),
% 40.79/5.50    inference(definition_unfolding,[],[f55,f66])).
% 40.79/5.50  fof(f55,plain,(
% 40.79/5.50    ( ! [X2,X0,X3,X1] : (sP3(X3,X1,X0) | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 40.79/5.50    inference(cnf_transformation,[],[f12])).
% 40.79/5.50  fof(f26633,plain,(
% 40.79/5.50    ~spl4_3),
% 40.79/5.50    inference(avatar_contradiction_clause,[],[f26632])).
% 40.79/5.50  fof(f26632,plain,(
% 40.79/5.50    $false | ~spl4_3),
% 40.79/5.50    inference(subsumption_resolution,[],[f26631,f32])).
% 40.79/5.50  fof(f26631,plain,(
% 40.79/5.50    sK0 = sK1 | ~spl4_3),
% 40.79/5.50    inference(duplicate_literal_removal,[],[f26630])).
% 40.79/5.50  fof(f26630,plain,(
% 40.79/5.50    sK0 = sK1 | sK0 = sK1 | ~spl4_3),
% 40.79/5.50    inference(resolution,[],[f26429,f53])).
% 40.79/5.50  fof(f26429,plain,(
% 40.79/5.50    sP3(sK0,sK1,sK1) | ~spl4_3),
% 40.79/5.50    inference(resolution,[],[f26423,f85])).
% 40.79/5.50  fof(f85,plain,(
% 40.79/5.50    ( ! [X3,X1] : (sP3(X3,X1,X3)) )),
% 40.79/5.50    inference(equality_resolution,[],[f51])).
% 40.79/5.50  fof(f51,plain,(
% 40.79/5.50    ( ! [X0,X3,X1] : (X0 != X3 | sP3(X3,X1,X0)) )),
% 40.79/5.50    inference(cnf_transformation,[],[f12])).
% 40.79/5.50  fof(f26423,plain,(
% 40.79/5.50    ( ! [X0] : (~sP3(X0,sK1,sK0) | sP3(X0,sK1,sK1)) ) | ~spl4_3),
% 40.79/5.50    inference(resolution,[],[f26006,f90])).
% 40.79/5.50  fof(f26006,plain,(
% 40.79/5.50    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK0,sK0,sK1)) | sP3(X0,sK1,sK1)) ) | ~spl4_3),
% 40.79/5.50    inference(backward_demodulation,[],[f25060,f25913])).
% 40.79/5.50  fof(f25913,plain,(
% 40.79/5.50    ( ! [X1] : (k2_enumset1(X1,sK1,sK0,sK0) = k2_enumset1(X1,X1,sK0,sK1)) ) | ~spl4_3),
% 40.79/5.50    inference(superposition,[],[f25855,f25027])).
% 40.79/5.50  fof(f25027,plain,(
% 40.79/5.50    ( ! [X1] : (k2_enumset1(X1,sK1,sK1,sK1) = k2_enumset1(X1,sK1,sK0,sK0)) ) | ~spl4_3),
% 40.79/5.50    inference(forward_demodulation,[],[f25002,f24756])).
% 40.79/5.50  fof(f24756,plain,(
% 40.79/5.50    ( ! [X74,X72,X75,X73] : (k2_enumset1(X72,X73,X74,X75) = k5_enumset1(X72,X73,X74,X75,sK0,sK0,sK0)) ) | ~spl4_3),
% 40.79/5.50    inference(forward_demodulation,[],[f24713,f9356])).
% 40.79/5.50  fof(f9356,plain,(
% 40.79/5.50    ( ! [X5] : (k2_xboole_0(X5,k1_xboole_0) = X5) )),
% 40.79/5.50    inference(backward_demodulation,[],[f525,f9354])).
% 40.79/5.50  fof(f9354,plain,(
% 40.79/5.50    ( ! [X27] : (k4_xboole_0(X27,k1_xboole_0) = X27) )),
% 40.79/5.50    inference(subsumption_resolution,[],[f9353,f1779])).
% 40.79/5.50  fof(f1779,plain,(
% 40.79/5.50    ( ! [X10,X11] : (r1_tarski(k4_xboole_0(X10,X11),X10)) )),
% 40.79/5.50    inference(trivial_inequality_removal,[],[f1743])).
% 40.79/5.50  fof(f1743,plain,(
% 40.79/5.50    ( ! [X10,X11] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k4_xboole_0(X10,X11),X10)) )),
% 40.79/5.50    inference(superposition,[],[f43,f1622])).
% 40.79/5.50  fof(f1622,plain,(
% 40.79/5.50    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),X5)) )),
% 40.79/5.50    inference(resolution,[],[f1419,f579])).
% 40.79/5.50  fof(f579,plain,(
% 40.79/5.50    ( ! [X4] : (~r1_tarski(X4,k1_xboole_0) | k1_xboole_0 = X4) )),
% 40.79/5.50    inference(trivial_inequality_removal,[],[f574])).
% 40.79/5.50  fof(f574,plain,(
% 40.79/5.50    ( ! [X4] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = X4 | ~r1_tarski(X4,k1_xboole_0)) )),
% 40.79/5.50    inference(superposition,[],[f98,f451])).
% 40.79/5.50  fof(f451,plain,(
% 40.79/5.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 40.79/5.50    inference(backward_demodulation,[],[f430,f431])).
% 40.79/5.50  fof(f431,plain,(
% 40.79/5.50    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 40.79/5.50    inference(superposition,[],[f174,f35])).
% 40.79/5.50  fof(f35,plain,(
% 40.79/5.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 40.79/5.50    inference(cnf_transformation,[],[f6])).
% 40.79/5.50  fof(f6,axiom,(
% 40.79/5.50    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 40.79/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 40.79/5.50  fof(f174,plain,(
% 40.79/5.50    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X0),X1) = k2_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 40.79/5.50    inference(superposition,[],[f47,f35])).
% 40.79/5.50  fof(f47,plain,(
% 40.79/5.50    ( ! [X2,X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2)))) )),
% 40.79/5.50    inference(cnf_transformation,[],[f11])).
% 40.79/5.50  fof(f11,axiom,(
% 40.79/5.50    ! [X0,X1,X2] : k4_xboole_0(k5_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X1,k2_xboole_0(X0,X2)))),
% 40.79/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_xboole_1)).
% 40.79/5.50  fof(f430,plain,(
% 40.79/5.50    ( ! [X0] : (k2_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X0)) )),
% 40.79/5.50    inference(superposition,[],[f174,f33])).
% 40.79/5.50  fof(f33,plain,(
% 40.79/5.50    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 40.79/5.50    inference(cnf_transformation,[],[f9])).
% 40.79/5.50  fof(f9,axiom,(
% 40.79/5.50    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 40.79/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 40.79/5.50  fof(f98,plain,(
% 40.79/5.50    ( ! [X2,X3] : (k1_xboole_0 != k4_xboole_0(X3,X2) | X2 = X3 | ~r1_tarski(X2,X3)) )),
% 40.79/5.50    inference(superposition,[],[f38,f42])).
% 40.79/5.50  fof(f42,plain,(
% 40.79/5.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 40.79/5.50    inference(cnf_transformation,[],[f1])).
% 40.79/5.50  fof(f1,axiom,(
% 40.79/5.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 40.79/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 40.79/5.50  fof(f38,plain,(
% 40.79/5.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) | X0 = X1) )),
% 40.79/5.50    inference(cnf_transformation,[],[f27])).
% 40.79/5.50  fof(f27,plain,(
% 40.79/5.50    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 40.79/5.50    inference(ennf_transformation,[],[f4])).
% 40.79/5.50  fof(f4,axiom,(
% 40.79/5.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 40.79/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).
% 40.79/5.50  fof(f1419,plain,(
% 40.79/5.50    ( ! [X12,X13] : (r1_tarski(k4_xboole_0(k4_xboole_0(X12,X13),X12),k1_xboole_0)) )),
% 40.79/5.50    inference(superposition,[],[f133,f135])).
% 40.79/5.50  fof(f135,plain,(
% 40.79/5.50    ( ! [X23,X21,X22] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X21,X22),k4_xboole_0(X21,k4_xboole_0(X22,X23)))) )),
% 40.79/5.50    inference(superposition,[],[f35,f45])).
% 40.79/5.50  fof(f45,plain,(
% 40.79/5.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 40.79/5.50    inference(cnf_transformation,[],[f7])).
% 40.79/5.50  fof(f7,axiom,(
% 40.79/5.50    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 40.79/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 40.79/5.50  fof(f133,plain,(
% 40.79/5.50    ( ! [X14,X15,X16] : (r1_tarski(k4_xboole_0(X14,X15),k4_xboole_0(X14,k4_xboole_0(X15,X16)))) )),
% 40.79/5.50    inference(superposition,[],[f95,f45])).
% 40.79/5.50  fof(f95,plain,(
% 40.79/5.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 40.79/5.50    inference(trivial_inequality_removal,[],[f93])).
% 40.79/5.50  fof(f93,plain,(
% 40.79/5.50    ( ! [X0,X1] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 40.79/5.50    inference(superposition,[],[f43,f35])).
% 40.79/5.50  fof(f43,plain,(
% 40.79/5.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 40.79/5.50    inference(cnf_transformation,[],[f1])).
% 40.79/5.50  fof(f9353,plain,(
% 40.79/5.50    ( ! [X27] : (~r1_tarski(k4_xboole_0(X27,k1_xboole_0),X27) | k4_xboole_0(X27,k1_xboole_0) = X27) )),
% 40.79/5.50    inference(forward_demodulation,[],[f8327,f8248])).
% 40.79/5.50  fof(f8248,plain,(
% 40.79/5.50    ( ! [X13] : (k2_xboole_0(k1_xboole_0,X13) = X13) )),
% 40.79/5.50    inference(subsumption_resolution,[],[f8241,f1840])).
% 40.79/5.50  fof(f1840,plain,(
% 40.79/5.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 40.79/5.50    inference(resolution,[],[f1779,f50])).
% 40.79/5.50  fof(f50,plain,(
% 40.79/5.50    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 40.79/5.50    inference(cnf_transformation,[],[f30])).
% 40.79/5.50  fof(f30,plain,(
% 40.79/5.50    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 40.79/5.50    inference(ennf_transformation,[],[f5])).
% 40.79/5.50  fof(f5,axiom,(
% 40.79/5.50    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 40.79/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 40.79/5.50  fof(f8241,plain,(
% 40.79/5.50    ( ! [X13] : (k2_xboole_0(k1_xboole_0,X13) = X13 | ~r1_tarski(X13,k2_xboole_0(k1_xboole_0,X13))) )),
% 40.79/5.50    inference(trivial_inequality_removal,[],[f8167])).
% 40.79/5.50  fof(f8167,plain,(
% 40.79/5.50    ( ! [X13] : (k1_xboole_0 != k1_xboole_0 | k2_xboole_0(k1_xboole_0,X13) = X13 | ~r1_tarski(X13,k2_xboole_0(k1_xboole_0,X13))) )),
% 40.79/5.50    inference(superposition,[],[f98,f7640])).
% 40.79/5.50  fof(f7640,plain,(
% 40.79/5.50    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),X1)) )),
% 40.79/5.50    inference(forward_demodulation,[],[f7639,f431])).
% 40.79/5.50  fof(f7639,plain,(
% 40.79/5.50    ( ! [X1] : (k2_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),X1)) )),
% 40.79/5.50    inference(forward_demodulation,[],[f7638,f33])).
% 40.79/5.50  fof(f7638,plain,(
% 40.79/5.50    ( ! [X1] : (k2_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k5_xboole_0(k2_xboole_0(k1_xboole_0,X1),k1_xboole_0),X1)) )),
% 40.79/5.50    inference(forward_demodulation,[],[f7579,f451])).
% 40.79/5.50  fof(f7579,plain,(
% 40.79/5.50    ( ! [X1] : (k4_xboole_0(k5_xboole_0(k2_xboole_0(k1_xboole_0,X1),k1_xboole_0),X1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(k1_xboole_0,X1),X1)))) )),
% 40.79/5.50    inference(superposition,[],[f47,f672])).
% 40.79/5.50  fof(f672,plain,(
% 40.79/5.50    ( ! [X11] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X11),k2_xboole_0(k1_xboole_0,X11))) )),
% 40.79/5.50    inference(superposition,[],[f147,f431])).
% 40.79/5.50  fof(f147,plain,(
% 40.79/5.50    ( ! [X6,X7,X5] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(k2_xboole_0(X5,X7),X6))) )),
% 40.79/5.50    inference(superposition,[],[f35,f46])).
% 40.79/5.50  fof(f46,plain,(
% 40.79/5.50    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))) )),
% 40.79/5.50    inference(cnf_transformation,[],[f10])).
% 40.79/5.50  fof(f10,axiom,(
% 40.79/5.50    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))),
% 40.79/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_1)).
% 40.79/5.50  fof(f8327,plain,(
% 40.79/5.50    ( ! [X27] : (k4_xboole_0(X27,k1_xboole_0) = X27 | ~r1_tarski(k4_xboole_0(k2_xboole_0(k1_xboole_0,X27),k1_xboole_0),X27)) )),
% 40.79/5.50    inference(backward_demodulation,[],[f5948,f8248])).
% 40.79/5.50  fof(f5948,plain,(
% 40.79/5.50    ( ! [X27] : (k4_xboole_0(k2_xboole_0(k1_xboole_0,X27),k1_xboole_0) = X27 | ~r1_tarski(k4_xboole_0(k2_xboole_0(k1_xboole_0,X27),k1_xboole_0),X27)) )),
% 40.79/5.50    inference(resolution,[],[f580,f1672])).
% 40.79/5.50  fof(f1672,plain,(
% 40.79/5.50    ( ! [X0] : (r1_tarski(X0,k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k1_xboole_0))) )),
% 40.79/5.50    inference(forward_demodulation,[],[f1671,f860])).
% 40.79/5.50  fof(f860,plain,(
% 40.79/5.50    ( ! [X10,X9] : (k4_xboole_0(X10,k1_xboole_0) = k4_xboole_0(X10,k3_xboole_0(k1_xboole_0,X9))) )),
% 40.79/5.50    inference(forward_demodulation,[],[f859,f33])).
% 40.79/5.50  fof(f859,plain,(
% 40.79/5.50    ( ! [X10,X9] : (k4_xboole_0(k5_xboole_0(X10,k1_xboole_0),k3_xboole_0(k1_xboole_0,X9)) = k4_xboole_0(X10,k1_xboole_0)) )),
% 40.79/5.50    inference(forward_demodulation,[],[f858,f525])).
% 40.79/5.50  fof(f858,plain,(
% 40.79/5.50    ( ! [X10,X9] : (k4_xboole_0(k5_xboole_0(X10,k1_xboole_0),k3_xboole_0(k1_xboole_0,X9)) = k2_xboole_0(k4_xboole_0(X10,k1_xboole_0),k1_xboole_0)) )),
% 40.79/5.50    inference(forward_demodulation,[],[f841,f451])).
% 40.79/5.50  fof(f841,plain,(
% 40.79/5.50    ( ! [X10,X9] : (k4_xboole_0(k5_xboole_0(X10,k1_xboole_0),k3_xboole_0(k1_xboole_0,X9)) = k2_xboole_0(k4_xboole_0(X10,k1_xboole_0),k4_xboole_0(k1_xboole_0,k2_xboole_0(X10,k3_xboole_0(k1_xboole_0,X9))))) )),
% 40.79/5.50    inference(superposition,[],[f47,f570])).
% 40.79/5.50  fof(f570,plain,(
% 40.79/5.50    ( ! [X7] : (k1_xboole_0 = k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X7))) )),
% 40.79/5.50    inference(forward_demodulation,[],[f557,f451])).
% 40.79/5.50  fof(f557,plain,(
% 40.79/5.50    ( ! [X6,X7] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(X6,X7)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X7))) )),
% 40.79/5.50    inference(superposition,[],[f45,f451])).
% 40.79/5.50  fof(f1671,plain,(
% 40.79/5.50    ( ! [X0] : (r1_tarski(X0,k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k3_xboole_0(k1_xboole_0,X0)))) )),
% 40.79/5.50    inference(superposition,[],[f1453,f37])).
% 40.79/5.50  fof(f37,plain,(
% 40.79/5.50    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 40.79/5.50    inference(cnf_transformation,[],[f8])).
% 40.79/5.50  fof(f8,axiom,(
% 40.79/5.50    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 40.79/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).
% 40.79/5.50  fof(f1453,plain,(
% 40.79/5.50    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,k4_xboole_0(X0,k1_xboole_0)))) )),
% 40.79/5.50    inference(resolution,[],[f1397,f50])).
% 40.79/5.50  fof(f1397,plain,(
% 40.79/5.50    ( ! [X2,X0] : (r1_tarski(k4_xboole_0(X2,X0),k4_xboole_0(X2,k1_xboole_0))) )),
% 40.79/5.50    inference(superposition,[],[f133,f35])).
% 40.79/5.50  fof(f580,plain,(
% 40.79/5.50    ( ! [X2,X3] : (~r1_tarski(X3,X2) | X2 = X3 | ~r1_tarski(X2,X3)) )),
% 40.79/5.50    inference(trivial_inequality_removal,[],[f573])).
% 40.79/5.50  fof(f573,plain,(
% 40.79/5.50    ( ! [X2,X3] : (k1_xboole_0 != k1_xboole_0 | X2 = X3 | ~r1_tarski(X3,X2) | ~r1_tarski(X2,X3)) )),
% 40.79/5.50    inference(superposition,[],[f98,f42])).
% 40.79/5.50  fof(f525,plain,(
% 40.79/5.50    ( ! [X5] : (k4_xboole_0(X5,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X5,k1_xboole_0),k1_xboole_0)) )),
% 40.79/5.50    inference(forward_demodulation,[],[f524,f33])).
% 40.79/5.50  fof(f524,plain,(
% 40.79/5.50    ( ! [X5] : (k4_xboole_0(k5_xboole_0(X5,k1_xboole_0),k1_xboole_0) = k2_xboole_0(k4_xboole_0(X5,k1_xboole_0),k1_xboole_0)) )),
% 40.79/5.50    inference(forward_demodulation,[],[f516,f451])).
% 40.79/5.50  fof(f516,plain,(
% 40.79/5.50    ( ! [X5] : (k4_xboole_0(k5_xboole_0(X5,k1_xboole_0),k1_xboole_0) = k2_xboole_0(k4_xboole_0(X5,k1_xboole_0),k4_xboole_0(k1_xboole_0,k2_xboole_0(X5,k1_xboole_0)))) )),
% 40.79/5.50    inference(superposition,[],[f47,f431])).
% 40.79/5.50  fof(f24713,plain,(
% 40.79/5.50    ( ! [X74,X72,X75,X73] : (k5_enumset1(X72,X73,X74,X75,sK0,sK0,sK0) = k2_xboole_0(k2_enumset1(X72,X73,X74,X75),k1_xboole_0)) ) | ~spl4_3),
% 40.79/5.50    inference(superposition,[],[f262,f23998])).
% 40.79/5.50  fof(f23998,plain,(
% 40.79/5.50    k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0) | ~spl4_3),
% 40.79/5.50    inference(avatar_component_clause,[],[f23996])).
% 40.79/5.50  fof(f23996,plain,(
% 40.79/5.50    spl4_3 <=> k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 40.79/5.50    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 40.79/5.50  fof(f262,plain,(
% 40.79/5.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X4,X5,X6))) )),
% 40.79/5.50    inference(backward_demodulation,[],[f79,f250])).
% 40.79/5.50  fof(f250,plain,(
% 40.79/5.50    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 40.79/5.50    inference(superposition,[],[f78,f69])).
% 40.79/5.50  fof(f78,plain,(
% 40.79/5.50    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k2_enumset1(X1,X2,X3,X4))) )),
% 40.79/5.50    inference(definition_unfolding,[],[f60,f65])).
% 40.79/5.50  fof(f60,plain,(
% 40.79/5.50    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 40.79/5.50    inference(cnf_transformation,[],[f19])).
% 40.79/5.50  fof(f19,axiom,(
% 40.79/5.50    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)),
% 40.79/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_enumset1)).
% 40.79/5.50  fof(f79,plain,(
% 40.79/5.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k5_enumset1(X4,X4,X4,X4,X4,X5,X6))) )),
% 40.79/5.50    inference(definition_unfolding,[],[f62,f44])).
% 40.79/5.50  fof(f44,plain,(
% 40.79/5.50    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 40.79/5.50    inference(cnf_transformation,[],[f21])).
% 40.79/5.50  fof(f21,axiom,(
% 40.79/5.50    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)),
% 40.79/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_enumset1)).
% 40.79/5.50  fof(f62,plain,(
% 40.79/5.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))) )),
% 40.79/5.50    inference(cnf_transformation,[],[f13])).
% 40.79/5.50  fof(f13,axiom,(
% 40.79/5.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6))),
% 40.79/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_enumset1)).
% 40.79/5.50  fof(f25002,plain,(
% 40.79/5.50    ( ! [X1] : (k2_enumset1(X1,sK1,sK1,sK1) = k5_enumset1(X1,sK1,sK0,sK0,sK0,sK0,sK0)) ) | ~spl4_3),
% 40.79/5.50    inference(superposition,[],[f24815,f238])).
% 40.79/5.50  fof(f238,plain,(
% 40.79/5.50    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k5_enumset1(X0,X1,X2,X2,X2,X3,X4)) )),
% 40.79/5.50    inference(superposition,[],[f91,f79])).
% 40.79/5.50  fof(f91,plain,(
% 40.79/5.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X0,X0,X1),k5_enumset1(X2,X2,X2,X3,X4,X5,X6))) )),
% 40.79/5.50    inference(backward_demodulation,[],[f86,f78])).
% 40.79/5.50  fof(f86,plain,(
% 40.79/5.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X0,X0,X1),k2_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k2_enumset1(X3,X4,X5,X6)))) )),
% 40.79/5.50    inference(backward_demodulation,[],[f67,f69])).
% 40.79/5.50  fof(f67,plain,(
% 40.79/5.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k2_enumset1(X0,X0,X0,X1)),k2_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k2_enumset1(X3,X4,X5,X6)))) )),
% 40.79/5.50    inference(definition_unfolding,[],[f61,f66,f65])).
% 40.79/5.50  fof(f61,plain,(
% 40.79/5.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))) )),
% 40.79/5.50    inference(cnf_transformation,[],[f16])).
% 40.79/5.50  fof(f16,axiom,(
% 40.79/5.50    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))),
% 40.79/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_enumset1)).
% 40.79/5.50  fof(f24815,plain,(
% 40.79/5.50    ( ! [X18] : (k5_enumset1(X18,X18,X18,sK1,sK0,sK0,sK0) = k2_enumset1(X18,sK1,sK1,sK1)) ) | ~spl4_3),
% 40.79/5.50    inference(forward_demodulation,[],[f24814,f24683])).
% 40.79/5.50  fof(f24683,plain,(
% 40.79/5.50    ( ! [X130] : (k5_enumset1(X130,X130,X130,sK0,sK1,sK1,sK1) = k2_enumset1(X130,sK1,sK1,sK1)) ) | ~spl4_3),
% 40.79/5.50    inference(forward_demodulation,[],[f24682,f427])).
% 40.79/5.50  fof(f427,plain,(
% 40.79/5.50    ( ! [X6,X8,X7,X5] : (k2_enumset1(X5,X6,X7,X8) = k5_enumset1(X5,X5,X5,X6,X6,X7,X8)) )),
% 40.79/5.50    inference(forward_demodulation,[],[f411,f250])).
% 40.79/5.50  fof(f411,plain,(
% 40.79/5.50    ( ! [X6,X8,X7,X5] : (k5_enumset1(X5,X5,X5,X5,X6,X7,X8) = k5_enumset1(X5,X5,X5,X6,X6,X7,X8)) )),
% 40.79/5.50    inference(superposition,[],[f325,f262])).
% 40.79/5.50  fof(f325,plain,(
% 40.79/5.50    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X2,X3,X4))) )),
% 40.79/5.50    inference(forward_demodulation,[],[f295,f250])).
% 40.79/5.50  fof(f295,plain,(
% 40.79/5.50    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k2_xboole_0(k5_enumset1(X0,X0,X0,X0,X0,X0,X0),k2_enumset1(X1,X2,X3,X4))) )),
% 40.79/5.50    inference(backward_demodulation,[],[f78,f280])).
% 40.79/5.50  fof(f280,plain,(
% 40.79/5.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X1,X2,X3,X4,X4,X5,X6)) )),
% 40.79/5.50    inference(superposition,[],[f262,f64])).
% 40.79/5.50  fof(f64,plain,(
% 40.79/5.50    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))) )),
% 40.79/5.50    inference(cnf_transformation,[],[f14])).
% 40.79/5.50  fof(f14,axiom,(
% 40.79/5.50    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7))),
% 40.79/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l75_enumset1)).
% 40.79/5.50  fof(f24682,plain,(
% 40.79/5.50    ( ! [X130] : (k5_enumset1(X130,X130,X130,sK1,sK1,sK1,sK1) = k5_enumset1(X130,X130,X130,sK0,sK1,sK1,sK1)) ) | ~spl4_3),
% 40.79/5.50    inference(forward_demodulation,[],[f24654,f325])).
% 40.79/5.50  fof(f24654,plain,(
% 40.79/5.50    ( ! [X130] : (k5_enumset1(X130,X130,X130,sK1,sK1,sK1,sK1) = k2_xboole_0(k2_enumset1(X130,X130,X130,X130),k2_enumset1(sK0,sK1,sK1,sK1))) ) | ~spl4_3),
% 40.79/5.50    inference(superposition,[],[f325,f24290])).
% 40.79/5.50  fof(f24290,plain,(
% 40.79/5.50    k2_enumset1(sK1,sK1,sK1,sK1) = k2_enumset1(sK0,sK1,sK1,sK1) | ~spl4_3),
% 40.79/5.50    inference(forward_demodulation,[],[f24289,f9354])).
% 40.79/5.50  fof(f24289,plain,(
% 40.79/5.50    k2_enumset1(sK1,sK1,sK1,sK1) = k4_xboole_0(k2_enumset1(sK0,sK1,sK1,sK1),k1_xboole_0) | ~spl4_3),
% 40.79/5.50    inference(forward_demodulation,[],[f24080,f9354])).
% 40.79/5.50  fof(f24080,plain,(
% 40.79/5.50    k4_xboole_0(k2_enumset1(sK0,sK1,sK1,sK1),k1_xboole_0) = k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0) | ~spl4_3),
% 40.79/5.50    inference(backward_demodulation,[],[f13869,f23998])).
% 40.79/5.50  fof(f13869,plain,(
% 40.79/5.50    k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)) = k4_xboole_0(k2_enumset1(sK0,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))),
% 40.79/5.50    inference(backward_demodulation,[],[f8619,f13867])).
% 40.79/5.50  fof(f13867,plain,(
% 40.79/5.50    ( ! [X2,X0,X1] : (k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,X0,X1,X2))) )),
% 40.79/5.50    inference(forward_demodulation,[],[f13866,f9354])).
% 40.79/5.50  fof(f13866,plain,(
% 40.79/5.50    ( ! [X2,X0,X1] : (k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,X0,X1,X2)) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0)) )),
% 40.79/5.50    inference(forward_demodulation,[],[f13806,f250])).
% 40.79/5.50  fof(f13806,plain,(
% 40.79/5.50    ( ! [X2,X0,X1] : (k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k1_xboole_0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,X0,X1,X2))) )),
% 40.79/5.50    inference(superposition,[],[f8820,f225])).
% 40.79/5.50  fof(f225,plain,(
% 40.79/5.50    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k1_xboole_0 = k4_xboole_0(k2_enumset1(X0,X1,X2,X3),k5_enumset1(X0,X1,X2,X3,X4,X5,X6))) )),
% 40.79/5.50    inference(superposition,[],[f35,f79])).
% 40.79/5.50  fof(f8820,plain,(
% 40.79/5.50    ( ! [X6] : (k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X6) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),X6))) )),
% 40.79/5.50    inference(backward_demodulation,[],[f357,f8248])).
% 40.79/5.50  fof(f357,plain,(
% 40.79/5.50    ( ! [X6] : (k2_xboole_0(k1_xboole_0,k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X6)) = k4_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),X6))) )),
% 40.79/5.50    inference(forward_demodulation,[],[f356,f250])).
% 40.79/5.50  fof(f356,plain,(
% 40.79/5.50    ( ! [X6] : (k2_xboole_0(k1_xboole_0,k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),X6)) = k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),X6))) )),
% 40.79/5.50    inference(forward_demodulation,[],[f355,f280])).
% 40.79/5.50  fof(f355,plain,(
% 40.79/5.50    ( ! [X6] : (k2_xboole_0(k1_xboole_0,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X6)) = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),X6))) )),
% 40.79/5.50    inference(forward_demodulation,[],[f318,f250])).
% 40.79/5.50  fof(f318,plain,(
% 40.79/5.50    ( ! [X6] : (k2_xboole_0(k1_xboole_0,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X6)) = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),X6))) )),
% 40.79/5.50    inference(backward_demodulation,[],[f128,f280])).
% 40.79/5.50  fof(f128,plain,(
% 40.79/5.50    ( ! [X6] : (k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),X6)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),X6))) )),
% 40.79/5.50    inference(superposition,[],[f45,f70])).
% 40.79/5.50  fof(f70,plain,(
% 40.79/5.50    k1_xboole_0 = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 40.79/5.50    inference(definition_unfolding,[],[f31,f34,f34])).
% 40.79/5.50  fof(f31,plain,(
% 40.79/5.50    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 40.79/5.50    inference(cnf_transformation,[],[f26])).
% 40.79/5.50  fof(f8619,plain,(
% 40.79/5.50    k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)) = k4_xboole_0(k2_enumset1(sK0,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)))),
% 40.79/5.50    inference(backward_demodulation,[],[f428,f8248])).
% 40.79/5.50  fof(f428,plain,(
% 40.79/5.50    k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))) = k4_xboole_0(k2_enumset1(sK0,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)))),
% 40.79/5.50    inference(backward_demodulation,[],[f361,f427])).
% 40.79/5.50  fof(f361,plain,(
% 40.79/5.50    k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))) = k4_xboole_0(k5_enumset1(sK0,sK0,sK0,sK1,sK1,sK1,sK1),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)))),
% 40.79/5.50    inference(forward_demodulation,[],[f360,f325])).
% 40.79/5.50  fof(f360,plain,(
% 40.79/5.50    k4_xboole_0(k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)))),
% 40.79/5.50    inference(forward_demodulation,[],[f359,f250])).
% 40.79/5.50  fof(f359,plain,(
% 40.79/5.50    k4_xboole_0(k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)))),
% 40.79/5.50    inference(forward_demodulation,[],[f358,f250])).
% 40.79/5.50  fof(f358,plain,(
% 40.79/5.50    k4_xboole_0(k2_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 40.79/5.50    inference(forward_demodulation,[],[f319,f280])).
% 40.79/5.50  fof(f319,plain,(
% 40.79/5.50    k4_xboole_0(k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 40.79/5.50    inference(backward_demodulation,[],[f155,f280])).
% 40.79/5.50  fof(f155,plain,(
% 40.79/5.50    k4_xboole_0(k2_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 40.79/5.50    inference(superposition,[],[f37,f70])).
% 40.79/5.50  fof(f24814,plain,(
% 40.79/5.50    ( ! [X18] : (k5_enumset1(X18,X18,X18,sK1,sK0,sK0,sK0) = k5_enumset1(X18,X18,X18,sK0,sK1,sK1,sK1)) ) | ~spl4_3),
% 40.79/5.50    inference(forward_demodulation,[],[f24792,f325])).
% 40.79/5.50  fof(f24792,plain,(
% 40.79/5.50    ( ! [X18] : (k5_enumset1(X18,X18,X18,sK1,sK0,sK0,sK0) = k2_xboole_0(k2_enumset1(X18,X18,X18,X18),k2_enumset1(sK0,sK1,sK1,sK1))) ) | ~spl4_3),
% 40.79/5.50    inference(superposition,[],[f325,f24339])).
% 40.79/5.50  fof(f24339,plain,(
% 40.79/5.50    k2_enumset1(sK0,sK1,sK1,sK1) = k2_enumset1(sK1,sK0,sK0,sK0) | ~spl4_3),
% 40.79/5.50    inference(forward_demodulation,[],[f24338,f9354])).
% 40.79/5.50  fof(f24338,plain,(
% 40.79/5.50    k2_enumset1(sK1,sK0,sK0,sK0) = k4_xboole_0(k2_enumset1(sK0,sK1,sK1,sK1),k1_xboole_0) | ~spl4_3),
% 40.79/5.50    inference(forward_demodulation,[],[f24337,f9354])).
% 40.79/5.50  fof(f24337,plain,(
% 40.79/5.50    k4_xboole_0(k2_enumset1(sK0,sK1,sK1,sK1),k1_xboole_0) = k4_xboole_0(k2_enumset1(sK1,sK0,sK0,sK0),k1_xboole_0) | ~spl4_3),
% 40.79/5.50    inference(forward_demodulation,[],[f24081,f13749])).
% 40.79/5.50  fof(f13749,plain,(
% 40.79/5.50    ( ! [X65] : (k1_xboole_0 = k3_xboole_0(X65,k1_xboole_0)) )),
% 40.79/5.50    inference(forward_demodulation,[],[f13730,f35])).
% 40.79/5.50  fof(f13730,plain,(
% 40.79/5.50    ( ! [X66,X65] : (k3_xboole_0(X65,k1_xboole_0) = k4_xboole_0(X65,k2_xboole_0(X65,X66))) )),
% 40.79/5.50    inference(superposition,[],[f8669,f9354])).
% 40.79/5.50  fof(f8669,plain,(
% 40.79/5.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X2) = k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X2))) )),
% 40.79/5.50    inference(backward_demodulation,[],[f126,f8248])).
% 40.79/5.50  fof(f126,plain,(
% 40.79/5.50    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(k2_xboole_0(X0,X1),X2)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X2))) )),
% 40.79/5.50    inference(superposition,[],[f45,f35])).
% 40.79/5.50  fof(f24081,plain,(
% 40.79/5.50    k4_xboole_0(k2_enumset1(sK0,sK1,sK1,sK1),k1_xboole_0) = k4_xboole_0(k2_enumset1(sK1,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k1_xboole_0)) | ~spl4_3),
% 40.79/5.50    inference(backward_demodulation,[],[f13896,f23998])).
% 40.79/5.50  fof(f13896,plain,(
% 40.79/5.50    k4_xboole_0(k2_enumset1(sK1,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))) = k4_xboole_0(k2_enumset1(sK0,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))),
% 40.79/5.50    inference(backward_demodulation,[],[f9138,f13869])).
% 40.79/5.50  fof(f9138,plain,(
% 40.79/5.50    k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)) = k4_xboole_0(k2_enumset1(sK1,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)))),
% 40.79/5.50    inference(backward_demodulation,[],[f1361,f8264])).
% 40.79/5.50  fof(f8264,plain,(
% 40.79/5.50    ( ! [X21,X20] : (k4_xboole_0(X20,X21) = k2_xboole_0(k4_xboole_0(X20,X21),k1_xboole_0)) )),
% 40.79/5.50    inference(backward_demodulation,[],[f571,f8248])).
% 40.79/5.50  fof(f571,plain,(
% 40.79/5.50    ( ! [X21,X20] : (k4_xboole_0(X20,X21) = k2_xboole_0(k4_xboole_0(X20,k2_xboole_0(k1_xboole_0,X21)),k1_xboole_0)) )),
% 40.79/5.50    inference(forward_demodulation,[],[f565,f33])).
% 40.79/5.50  fof(f565,plain,(
% 40.79/5.50    ( ! [X21,X20] : (k4_xboole_0(k5_xboole_0(X20,k1_xboole_0),X21) = k2_xboole_0(k4_xboole_0(X20,k2_xboole_0(k1_xboole_0,X21)),k1_xboole_0)) )),
% 40.79/5.50    inference(superposition,[],[f47,f451])).
% 40.79/5.50  fof(f1361,plain,(
% 40.79/5.50    k2_xboole_0(k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0) = k4_xboole_0(k2_enumset1(sK1,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)))),
% 40.79/5.50    inference(backward_demodulation,[],[f366,f1349])).
% 40.79/5.50  fof(f1349,plain,(
% 40.79/5.50    ( ! [X6,X4,X7,X5] : (k2_enumset1(X4,X5,X6,X7) = k5_enumset1(X4,X5,X5,X5,X5,X6,X7)) )),
% 40.79/5.50    inference(superposition,[],[f238,f427])).
% 40.79/5.50  fof(f366,plain,(
% 40.79/5.50    k2_xboole_0(k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0) = k4_xboole_0(k5_enumset1(sK1,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)))),
% 40.79/5.50    inference(forward_demodulation,[],[f365,f238])).
% 40.79/5.50  fof(f365,plain,(
% 40.79/5.50    k2_xboole_0(k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0) = k4_xboole_0(k5_enumset1(sK1,sK1,sK1,sK0,sK0,sK0,sK0),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)))),
% 40.79/5.50    inference(forward_demodulation,[],[f364,f325])).
% 40.79/5.50  fof(f364,plain,(
% 40.79/5.50    k4_xboole_0(k2_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)),k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))) = k2_xboole_0(k4_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0)),
% 40.79/5.50    inference(forward_demodulation,[],[f363,f250])).
% 40.79/5.50  fof(f363,plain,(
% 40.79/5.50    k4_xboole_0(k2_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0))) = k2_xboole_0(k4_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK0)),k1_xboole_0)),
% 40.79/5.50    inference(forward_demodulation,[],[f362,f250])).
% 40.79/5.50  fof(f362,plain,(
% 40.79/5.50    k4_xboole_0(k2_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k2_xboole_0(k4_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0)),
% 40.79/5.50    inference(forward_demodulation,[],[f320,f280])).
% 40.79/5.50  fof(f320,plain,(
% 40.79/5.50    k4_xboole_0(k2_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k2_xboole_0(k4_xboole_0(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0)),
% 40.79/5.50    inference(backward_demodulation,[],[f158,f280])).
% 40.79/5.50  fof(f158,plain,(
% 40.79/5.50    k4_xboole_0(k2_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) = k2_xboole_0(k4_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0)),
% 40.79/5.50    inference(superposition,[],[f37,f70])).
% 40.79/5.50  fof(f25855,plain,(
% 40.79/5.50    ( ! [X1] : (k2_enumset1(X1,sK1,sK1,sK1) = k2_enumset1(X1,X1,sK0,sK1)) ) | ~spl4_3),
% 40.79/5.50    inference(superposition,[],[f25225,f427])).
% 40.79/5.50  fof(f25225,plain,(
% 40.79/5.50    ( ! [X130] : (k5_enumset1(X130,X130,X130,sK1,sK1,sK1,sK1) = k2_enumset1(X130,X130,sK0,sK1)) ) | ~spl4_3),
% 40.79/5.50    inference(forward_demodulation,[],[f25197,f25116])).
% 40.79/5.50  fof(f25116,plain,(
% 40.79/5.50    ( ! [X2,X0,X1] : (k2_xboole_0(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X0,sK1,sK0,sK0)) = k2_enumset1(X1,X2,X0,sK1)) ) | ~spl4_3),
% 40.79/5.50    inference(forward_demodulation,[],[f25115,f25027])).
% 40.79/5.50  fof(f25115,plain,(
% 40.79/5.50    ( ! [X2,X0,X1] : (k2_xboole_0(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X0,sK1,sK1,sK1)) = k2_enumset1(X1,X2,X0,sK1)) ) | ~spl4_3),
% 40.79/5.50    inference(forward_demodulation,[],[f25004,f24756])).
% 40.79/5.50  fof(f25004,plain,(
% 40.79/5.50    ( ! [X2,X0,X1] : (k2_xboole_0(k2_enumset1(X1,X1,X1,X2),k2_enumset1(X0,sK1,sK1,sK1)) = k5_enumset1(X1,X2,X0,sK1,sK0,sK0,sK0)) ) | ~spl4_3),
% 40.79/5.50    inference(superposition,[],[f91,f24815])).
% 40.79/5.50  fof(f25197,plain,(
% 40.79/5.50    ( ! [X130] : (k5_enumset1(X130,X130,X130,sK1,sK1,sK1,sK1) = k2_xboole_0(k2_enumset1(X130,X130,X130,X130),k2_enumset1(sK0,sK1,sK0,sK0))) ) | ~spl4_3),
% 40.79/5.50    inference(superposition,[],[f325,f25049])).
% 40.79/5.50  fof(f25049,plain,(
% 40.79/5.50    k2_enumset1(sK1,sK1,sK1,sK1) = k2_enumset1(sK0,sK1,sK0,sK0) | ~spl4_3),
% 40.79/5.50    inference(backward_demodulation,[],[f24290,f25027])).
% 40.79/5.50  fof(f25060,plain,(
% 40.79/5.50    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK1,sK0,sK0)) | sP3(X0,sK1,sK1)) ) | ~spl4_3),
% 40.79/5.50    inference(backward_demodulation,[],[f24622,f25027])).
% 40.79/5.50  fof(f24622,plain,(
% 40.79/5.50    ( ! [X0] : (~r2_hidden(X0,k2_enumset1(sK0,sK1,sK1,sK1)) | sP3(X0,sK1,sK1)) ) | ~spl4_3),
% 40.79/5.50    inference(superposition,[],[f89,f24290])).
% 40.79/5.50  fof(f24003,plain,(
% 40.79/5.50    spl4_3 | spl4_4),
% 40.79/5.50    inference(avatar_split_clause,[],[f407,f24000,f23996])).
% 40.79/5.50  fof(f407,plain,(
% 40.79/5.50    k2_enumset1(sK1,sK1,sK1,sK1) = k2_enumset1(sK0,sK0,sK0,sK0) | k1_xboole_0 = k2_enumset1(sK0,sK0,sK0,sK0)),
% 40.79/5.50    inference(resolution,[],[f324,f354])).
% 40.79/5.50  fof(f354,plain,(
% 40.79/5.50    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 40.79/5.50    inference(forward_demodulation,[],[f353,f250])).
% 40.79/5.50  fof(f353,plain,(
% 40.79/5.50    r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 40.79/5.50    inference(forward_demodulation,[],[f352,f280])).
% 40.79/5.50  fof(f352,plain,(
% 40.79/5.50    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 40.79/5.50    inference(forward_demodulation,[],[f317,f250])).
% 40.79/5.50  fof(f317,plain,(
% 40.79/5.50    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 40.79/5.50    inference(backward_demodulation,[],[f123,f280])).
% 40.79/5.50  fof(f123,plain,(
% 40.79/5.50    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 40.79/5.50    inference(trivial_inequality_removal,[],[f119])).
% 40.79/5.50  fof(f119,plain,(
% 40.79/5.50    k1_xboole_0 != k1_xboole_0 | r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 40.79/5.50    inference(superposition,[],[f43,f70])).
% 40.79/5.50  fof(f324,plain,(
% 40.79/5.50    ( ! [X0,X1] : (~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) | k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 40.79/5.50    inference(forward_demodulation,[],[f323,f250])).
% 40.79/5.50  fof(f323,plain,(
% 40.79/5.50    ( ! [X0,X1] : (~r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X1)) | k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 40.79/5.50    inference(forward_demodulation,[],[f322,f280])).
% 40.79/5.50  fof(f322,plain,(
% 40.79/5.50    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 40.79/5.50    inference(forward_demodulation,[],[f294,f250])).
% 40.79/5.50  fof(f294,plain,(
% 40.79/5.50    ( ! [X0,X1] : (k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 40.79/5.50    inference(backward_demodulation,[],[f73,f280])).
% 40.79/5.50  fof(f73,plain,(
% 40.79/5.50    ( ! [X0,X1] : (k1_xboole_0 = X0 | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 40.79/5.50    inference(definition_unfolding,[],[f39,f34,f34])).
% 40.79/5.50  fof(f39,plain,(
% 40.79/5.50    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 40.79/5.50    inference(cnf_transformation,[],[f23])).
% 40.79/5.50  fof(f23,axiom,(
% 40.79/5.50    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 40.79/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 40.79/5.50  % SZS output end Proof for theBenchmark
% 40.79/5.50  % (4071)------------------------------
% 40.79/5.50  % (4071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 40.79/5.50  % (4071)Termination reason: Refutation
% 40.79/5.50  
% 40.79/5.50  % (4071)Memory used [KB]: 37099
% 40.79/5.50  % (4071)Time elapsed: 4.025 s
% 40.79/5.50  % (4071)------------------------------
% 40.79/5.50  % (4071)------------------------------
% 40.79/5.50  % (3850)Success in time 5.126 s
%------------------------------------------------------------------------------
