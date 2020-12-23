%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t95_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:35 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   57 (  65 expanded)
%              Number of leaves         :   16 (  22 expanded)
%              Depth                    :   12
%              Number of atoms          :   87 ( 101 expanded)
%              Number of equality atoms :   44 (  50 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4244,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f80,f258,f4152])).

fof(f4152,plain,
    ( ~ spl2_2
    | spl2_5 ),
    inference(avatar_contradiction_clause,[],[f4151])).

fof(f4151,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(trivial_inequality_removal,[],[f4116])).

fof(f4116,plain,
    ( k3_xboole_0(sK0,sK1) != k3_xboole_0(sK0,sK1)
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(superposition,[],[f257,f2108])).

fof(f2108,plain,
    ( ! [X4,X5] : k3_xboole_0(X4,X5) = k5_xboole_0(k5_xboole_0(X4,X5),k2_xboole_0(X4,X5))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f2107,f90])).

fof(f90,plain,
    ( ! [X5] : k2_xboole_0(o_0_0_xboole_0,X5) = X5
    | ~ spl2_2 ),
    inference(superposition,[],[f55,f84])).

fof(f84,plain,
    ( ! [X0] : k2_xboole_0(X0,o_0_0_xboole_0) = X0
    | ~ spl2_2 ),
    inference(superposition,[],[f47,f79])).

fof(f79,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl2_2
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f47,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t95_xboole_1.p',t1_boole)).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t95_xboole_1.p',commutativity_k2_xboole_0)).

fof(f2107,plain,
    ( ! [X4,X5] : k5_xboole_0(k5_xboole_0(X4,X5),k2_xboole_0(X4,X5)) = k2_xboole_0(o_0_0_xboole_0,k3_xboole_0(X4,X5))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f2106,f284])).

fof(f284,plain,
    ( ! [X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = o_0_0_xboole_0
    | ~ spl2_2 ),
    inference(superposition,[],[f230,f59])).

fof(f59,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t95_xboole_1.p',l98_xboole_1)).

fof(f230,plain,
    ( ! [X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X0) = o_0_0_xboole_0
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f228,f79])).

fof(f228,plain,(
    ! [X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(resolution,[],[f64,f54])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t95_xboole_1.p',t36_xboole_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t95_xboole_1.p',l32_xboole_1)).

fof(f2106,plain,(
    ! [X4,X5] : k5_xboole_0(k5_xboole_0(X4,X5),k2_xboole_0(X4,X5)) = k2_xboole_0(k4_xboole_0(k5_xboole_0(X4,X5),k2_xboole_0(X4,X5)),k3_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f2068,f411])).

fof(f411,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,X3)) ),
    inference(superposition,[],[f60,f55])).

fof(f60,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t95_xboole_1.p',t93_xboole_1)).

fof(f2068,plain,(
    ! [X4,X5] : k5_xboole_0(k5_xboole_0(X4,X5),k2_xboole_0(k3_xboole_0(X4,X5),k5_xboole_0(X4,X5))) = k2_xboole_0(k4_xboole_0(k5_xboole_0(X4,X5),k2_xboole_0(k3_xboole_0(X4,X5),k5_xboole_0(X4,X5))),k3_xboole_0(X4,X5)) ),
    inference(superposition,[],[f61,f261])).

fof(f261,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k4_xboole_0(k2_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X2,X3)),k5_xboole_0(X2,X3)) ),
    inference(resolution,[],[f63,f58])).

fof(f58,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t95_xboole_1.p',l97_xboole_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t95_xboole_1.p',t88_xboole_1)).

fof(f61,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t95_xboole_1.p',d6_xboole_0)).

fof(f257,plain,
    ( k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl2_5
  <=> k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f258,plain,(
    ~ spl2_5 ),
    inference(avatar_split_clause,[],[f44,f256])).

fof(f44,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f36,f42])).

fof(f42,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t95_xboole_1.p',t95_xboole_1)).

fof(f80,plain,
    ( spl2_2
    | ~ spl2_0 ),
    inference(avatar_split_clause,[],[f73,f70,f78])).

fof(f70,plain,
    ( spl2_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_0])])).

fof(f73,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl2_0 ),
    inference(resolution,[],[f51,f71])).

fof(f71,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl2_0 ),
    inference(avatar_component_clause,[],[f70])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t95_xboole_1.p',t6_boole)).

fof(f72,plain,(
    spl2_0 ),
    inference(avatar_split_clause,[],[f45,f70])).

fof(f45,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t95_xboole_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
