%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t32_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:01 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   31 (  39 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :   12
%              Number of atoms          :   53 (  71 expanded)
%              Number of equality atoms :   33 (  43 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f87,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f86])).

fof(f86,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | ~ spl2_1 ),
    inference(trivial_inequality_removal,[],[f84])).

fof(f84,plain,
    ( k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1)
    | ~ spl2_1 ),
    inference(superposition,[],[f54,f75])).

fof(f75,plain,(
    ! [X0,X1] : k3_relat_1(k1_tarski(k4_tarski(X0,X1))) = k2_tarski(X0,X1) ),
    inference(forward_demodulation,[],[f74,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t32_relat_1.p',t41_enumset1)).

fof(f74,plain,(
    ! [X0,X1] : k3_relat_1(k1_tarski(k4_tarski(X0,X1))) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(backward_demodulation,[],[f73,f72])).

fof(f72,plain,(
    ! [X0,X1] : k3_relat_1(k1_tarski(k4_tarski(X0,X1))) = k2_xboole_0(k1_relat_1(k1_tarski(k4_tarski(X0,X1))),k1_tarski(X1)) ),
    inference(backward_demodulation,[],[f71,f70])).

fof(f70,plain,(
    ! [X0,X1] : k3_relat_1(k1_tarski(k4_tarski(X0,X1))) = k2_xboole_0(k1_relat_1(k1_tarski(k4_tarski(X0,X1))),k2_relat_1(k1_tarski(k4_tarski(X0,X1)))) ),
    inference(resolution,[],[f44,f46])).

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] : v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t32_relat_1.p',fc5_relat_1)).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t32_relat_1.p',d6_relat_1)).

fof(f71,plain,(
    ! [X0,X1] : k1_tarski(X0) = k2_relat_1(k1_tarski(k4_tarski(X1,X0))) ),
    inference(resolution,[],[f47,f46])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k1_tarski(k4_tarski(X0,X1)))
      | k1_tarski(X1) = k2_relat_1(k1_tarski(k4_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | k1_tarski(X1) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X1) = k2_relat_1(X2)
        & k1_tarski(X0) = k1_relat_1(X2) )
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X1) = k2_relat_1(X2)
        & k1_tarski(X0) = k1_relat_1(X2) )
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( k1_tarski(k4_tarski(X0,X1)) = X2
       => ( k1_tarski(X1) = k2_relat_1(X2)
          & k1_tarski(X0) = k1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t32_relat_1.p',t23_relat_1)).

fof(f73,plain,(
    ! [X0,X1] : k1_tarski(X0) = k1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(resolution,[],[f48,f46])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k1_tarski(k4_tarski(X0,X1)))
      | k1_tarski(X0) = k1_relat_1(k1_tarski(k4_tarski(X0,X1))) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k1_tarski(k4_tarski(X0,X1)) != X2
      | k1_tarski(X0) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f54,plain,
    ( k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) != k2_tarski(sK0,sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl2_1
  <=> k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) != k2_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f55,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f35,f53])).

fof(f35,plain,(
    k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) != k2_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0,X1] : k3_relat_1(k1_tarski(k4_tarski(X0,X1))) != k2_tarski(X0,X1) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] : k3_relat_1(k1_tarski(k4_tarski(X0,X1))) = k2_tarski(X0,X1) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] : k3_relat_1(k1_tarski(k4_tarski(X0,X1))) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t32_relat_1.p',t32_relat_1)).
%------------------------------------------------------------------------------
