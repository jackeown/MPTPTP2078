%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t146_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:02 EDT 2019

% Result     : Theorem 11.89s
% Output     : Refutation 11.89s
% Verified   : 
% Statistics : Number of formulae       :   50 (  89 expanded)
%              Number of leaves         :   13 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :   59 ( 106 expanded)
%              Number of equality atoms :   43 (  89 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f229357,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f61,f3970,f229159])).

fof(f229159,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f229158])).

fof(f229158,plain,
    ( $false
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f228870,f743])).

fof(f743,plain,(
    ! [X6,X8,X7,X9] : k2_zfmisc_1(k2_tarski(X6,X7),k2_tarski(X9,X8)) = k2_zfmisc_1(k2_tarski(X7,X6),k2_tarski(X8,X9)) ),
    inference(superposition,[],[f737,f619])).

fof(f619,plain,(
    ! [X50,X48,X49] : k2_zfmisc_1(k2_tarski(X48,X49),X50) = k2_zfmisc_1(k2_tarski(X49,X48),X50) ),
    inference(forward_demodulation,[],[f583,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t146_zfmisc_1.p',t41_enumset1)).

fof(f583,plain,(
    ! [X50,X48,X49] : k2_zfmisc_1(k2_tarski(X48,X49),X50) = k2_zfmisc_1(k2_xboole_0(k1_tarski(X49),k1_tarski(X48)),X50) ),
    inference(superposition,[],[f560,f40])).

fof(f560,plain,(
    ! [X4,X5,X3] : k2_zfmisc_1(k2_xboole_0(X3,X5),X4) = k2_zfmisc_1(k2_xboole_0(X5,X3),X4) ),
    inference(superposition,[],[f87,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t146_zfmisc_1.p',t120_zfmisc_1)).

fof(f87,plain,(
    ! [X6,X7,X5] : k2_zfmisc_1(k2_xboole_0(X5,X7),X6) = k2_xboole_0(k2_zfmisc_1(X7,X6),k2_zfmisc_1(X5,X6)) ),
    inference(superposition,[],[f42,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t146_zfmisc_1.p',commutativity_k2_xboole_0)).

fof(f737,plain,(
    ! [X54,X52,X53] : k2_zfmisc_1(X54,k2_tarski(X52,X53)) = k2_zfmisc_1(X54,k2_tarski(X53,X52)) ),
    inference(forward_demodulation,[],[f680,f40])).

fof(f680,plain,(
    ! [X54,X52,X53] : k2_zfmisc_1(X54,k2_tarski(X52,X53)) = k2_zfmisc_1(X54,k2_xboole_0(k1_tarski(X53),k1_tarski(X52))) ),
    inference(superposition,[],[f652,f40])).

fof(f652,plain,(
    ! [X8,X7,X9] : k2_zfmisc_1(X7,k2_xboole_0(X8,X9)) = k2_zfmisc_1(X7,k2_xboole_0(X9,X8)) ),
    inference(superposition,[],[f94,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f94,plain,(
    ! [X8,X7,X9] : k2_zfmisc_1(X7,k2_xboole_0(X8,X9)) = k2_xboole_0(k2_zfmisc_1(X7,X9),k2_zfmisc_1(X7,X8)) ),
    inference(superposition,[],[f43,f39])).

fof(f228870,plain,
    ( k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_zfmisc_1(k2_tarski(sK1,sK0),k2_tarski(sK3,sK2))
    | ~ spl4_5 ),
    inference(superposition,[],[f3969,f160932])).

fof(f160932,plain,(
    ! [X64,X62,X65,X63] : k2_zfmisc_1(k2_tarski(X65,X62),k2_tarski(X64,X63)) = k2_enumset1(k4_tarski(X62,X63),k4_tarski(X62,X64),k4_tarski(X65,X63),k4_tarski(X65,X64)) ),
    inference(forward_demodulation,[],[f160780,f40])).

fof(f160780,plain,(
    ! [X64,X62,X65,X63] : k2_zfmisc_1(k2_xboole_0(k1_tarski(X65),k1_tarski(X62)),k2_tarski(X64,X63)) = k2_enumset1(k4_tarski(X62,X63),k4_tarski(X62,X64),k4_tarski(X65,X63),k4_tarski(X65,X64)) ),
    inference(superposition,[],[f15376,f757])).

fof(f757,plain,(
    ! [X23,X21,X22,X20] : k2_zfmisc_1(k2_xboole_0(X23,X20),k2_tarski(X21,X22)) = k2_xboole_0(k2_zfmisc_1(X20,k2_tarski(X22,X21)),k2_zfmisc_1(X23,k2_tarski(X21,X22))) ),
    inference(superposition,[],[f87,f737])).

fof(f15376,plain,(
    ! [X14,X19,X17,X15,X18,X16] : k2_enumset1(k4_tarski(X17,X18),k4_tarski(X17,X19),k4_tarski(X14,X15),k4_tarski(X14,X16)) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X17),k2_tarski(X18,X19)),k2_zfmisc_1(k1_tarski(X14),k2_tarski(X16,X15))) ),
    inference(superposition,[],[f265,f260])).

fof(f260,plain,(
    ! [X4,X5,X3] : k2_tarski(k4_tarski(X3,X5),k4_tarski(X3,X4)) = k2_zfmisc_1(k1_tarski(X3),k2_tarski(X4,X5)) ),
    inference(superposition,[],[f44,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t146_zfmisc_1.p',commutativity_k2_tarski)).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t146_zfmisc_1.p',t36_zfmisc_1)).

fof(f265,plain,(
    ! [X6,X10,X8,X7,X9] : k2_enumset1(k4_tarski(X6,X7),k4_tarski(X6,X8),X9,X10) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X6),k2_tarski(X7,X8)),k2_tarski(X9,X10)) ),
    inference(superposition,[],[f46,f44])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t146_zfmisc_1.p',t45_enumset1)).

fof(f3969,plain,
    ( k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f3968])).

fof(f3968,plain,
    ( spl4_5
  <=> k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f3970,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f32,f3968])).

fof(f32,plain,(
    k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f27,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) != k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))
   => k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) != k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t146_zfmisc_1.p',t146_zfmisc_1)).

fof(f61,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f34,f59])).

fof(f59,plain,
    ( spl4_2
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f34,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t146_zfmisc_1.p',d2_xboole_0)).

fof(f54,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f47,f52])).

fof(f52,plain,
    ( spl4_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f33,f34])).

fof(f33,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/zfmisc_1__t146_zfmisc_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
