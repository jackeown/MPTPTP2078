%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:02 EST 2020

% Result     : Theorem 8.40s
% Output     : Refutation 8.40s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 119 expanded)
%              Number of leaves         :   19 (  36 expanded)
%              Depth                    :   14
%              Number of atoms          :  175 ( 241 expanded)
%              Number of equality atoms :   48 (  53 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11584,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f148,f167,f171,f11582])).

fof(f11582,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | spl2_3 ),
    inference(avatar_contradiction_clause,[],[f11581])).

fof(f11581,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | spl2_3 ),
    inference(subsumption_resolution,[],[f7784,f11569])).

fof(f11569,plain,
    ( ! [X2] : r1_tarski(k1_relat_1(k7_relat_1(sK1,X2)),k1_relat_1(k8_relat_1(k9_relat_1(sK1,X2),sK1)))
    | ~ spl2_1 ),
    inference(superposition,[],[f245,f2318])).

fof(f2318,plain,
    ( ! [X1] : k7_relat_1(sK1,X1) = k7_relat_1(k8_relat_1(k9_relat_1(sK1,X1),sK1),X1)
    | ~ spl2_1 ),
    inference(superposition,[],[f230,f160])).

fof(f160,plain,
    ( ! [X8,X7] : k7_relat_1(k8_relat_1(X7,sK1),X8) = k8_relat_1(X7,k7_relat_1(sK1,X8))
    | ~ spl2_1 ),
    inference(resolution,[],[f147,f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).

fof(f147,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl2_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f230,plain,
    ( ! [X17] : k7_relat_1(sK1,X17) = k8_relat_1(k9_relat_1(sK1,X17),k7_relat_1(sK1,X17))
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f224,f149])).

fof(f149,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)
    | ~ spl2_1 ),
    inference(resolution,[],[f147,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f46])).

fof(f46,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f224,plain,
    ( ! [X17] : k7_relat_1(sK1,X17) = k8_relat_1(k2_relat_1(k7_relat_1(sK1,X17)),k7_relat_1(sK1,X17))
    | ~ spl2_1 ),
    inference(resolution,[],[f158,f130])).

fof(f130,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).

fof(f158,plain,
    ( ! [X6] : v1_relat_1(k7_relat_1(sK1,X6))
    | ~ spl2_1 ),
    inference(resolution,[],[f147,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f245,plain,
    ( ! [X12,X11] : r1_tarski(k1_relat_1(k7_relat_1(k8_relat_1(X11,sK1),X12)),k1_relat_1(k8_relat_1(X11,sK1)))
    | ~ spl2_1 ),
    inference(resolution,[],[f163,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f52])).

fof(f52,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

fof(f163,plain,
    ( ! [X11] : v1_relat_1(k8_relat_1(X11,sK1))
    | ~ spl2_1 ),
    inference(resolution,[],[f147,f141])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k8_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f7784,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(k8_relat_1(k9_relat_1(sK1,sK0),sK1)))
    | ~ spl2_1
    | ~ spl2_2
    | spl2_3 ),
    inference(forward_demodulation,[],[f7783,f535])).

fof(f535,plain,
    ( ! [X1] : k1_relat_1(k7_relat_1(sK1,X1)) = k3_xboole_0(X1,k1_relat_1(sK1))
    | ~ spl2_1 ),
    inference(superposition,[],[f155,f119])).

fof(f119,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f155,plain,
    ( ! [X3] : k1_relat_1(k7_relat_1(sK1,X3)) = k3_xboole_0(k1_relat_1(sK1),X3)
    | ~ spl2_1 ),
    inference(resolution,[],[f147,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f53])).

fof(f53,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f7783,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k8_relat_1(k9_relat_1(sK1,sK0),sK1)))
    | ~ spl2_1
    | ~ spl2_2
    | spl2_3 ),
    inference(superposition,[],[f170,f1517])).

fof(f1517,plain,
    ( ! [X0] : k9_relat_1(k4_relat_1(sK1),X0) = k1_relat_1(k8_relat_1(X0,sK1))
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f1516,f241])).

fof(f241,plain,
    ( ! [X5] : k1_relat_1(k8_relat_1(X5,sK1)) = k2_relat_1(k4_relat_1(k8_relat_1(X5,sK1)))
    | ~ spl2_1 ),
    inference(resolution,[],[f163,f102])).

fof(f102,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f1516,plain,
    ( ! [X0] : k9_relat_1(k4_relat_1(sK1),X0) = k2_relat_1(k4_relat_1(k8_relat_1(X0,sK1)))
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(superposition,[],[f172,f628])).

fof(f628,plain,
    ( ! [X5] : k7_relat_1(k4_relat_1(sK1),X5) = k4_relat_1(k8_relat_1(X5,sK1))
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f627,f162])).

fof(f162,plain,
    ( ! [X10] : k8_relat_1(X10,sK1) = k5_relat_1(sK1,k6_relat_1(X10))
    | ~ spl2_1 ),
    inference(resolution,[],[f147,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f627,plain,
    ( ! [X5] : k7_relat_1(k4_relat_1(sK1),X5) = k4_relat_1(k5_relat_1(sK1,k6_relat_1(X5)))
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f626,f184])).

fof(f184,plain,
    ( ! [X9] : k7_relat_1(k4_relat_1(sK1),X9) = k5_relat_1(k6_relat_1(X9),k4_relat_1(sK1))
    | ~ spl2_2 ),
    inference(resolution,[],[f166,f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f54])).

fof(f54,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f166,plain,
    ( v1_relat_1(k4_relat_1(sK1))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl2_2
  <=> v1_relat_1(k4_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f626,plain,
    ( ! [X5] : k4_relat_1(k5_relat_1(sK1,k6_relat_1(X5))) = k5_relat_1(k6_relat_1(X5),k4_relat_1(sK1))
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f618,f104])).

fof(f104,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

fof(f618,plain,
    ( ! [X5] : k4_relat_1(k5_relat_1(sK1,k6_relat_1(X5))) = k5_relat_1(k4_relat_1(k6_relat_1(X5)),k4_relat_1(sK1))
    | ~ spl2_1 ),
    inference(resolution,[],[f150,f135])).

fof(f135,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f150,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k4_relat_1(k5_relat_1(sK1,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(sK1)) )
    | ~ spl2_1 ),
    inference(resolution,[],[f147,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f48])).

fof(f48,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).

fof(f172,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(k4_relat_1(sK1),X0)) = k9_relat_1(k4_relat_1(sK1),X0)
    | ~ spl2_2 ),
    inference(resolution,[],[f166,f99])).

fof(f170,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,k1_relat_1(sK1)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0)))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl2_3
  <=> r1_tarski(k3_xboole_0(sK0,k1_relat_1(sK1)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f171,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f144,f169])).

fof(f144,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,k1_relat_1(sK1)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0))) ),
    inference(forward_demodulation,[],[f82,f119])).

fof(f82,plain,(
    ~ r1_tarski(k3_xboole_0(k1_relat_1(sK1),sK0),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f56])).

fof(f56,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) ) ),
    inference(negated_conjecture,[],[f55])).

fof(f55,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_relat_1)).

fof(f167,plain,
    ( spl2_2
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f153,f146,f165])).

fof(f153,plain,
    ( v1_relat_1(k4_relat_1(sK1))
    | ~ spl2_1 ),
    inference(resolution,[],[f147,f103])).

fof(f103,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f148,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f81,f146])).

fof(f81,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f57])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:29:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.22/0.52  % (30447)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.22/0.52  % (30438)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.22/0.53  % (30430)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.29/0.53  % (30425)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.29/0.54  % (30423)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.29/0.54  % (30452)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.29/0.54  % (30426)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.29/0.54  % (30427)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.29/0.54  % (30453)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.29/0.54  % (30441)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.29/0.55  % (30445)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.29/0.55  % (30444)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.29/0.55  % (30428)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.29/0.55  % (30443)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.29/0.55  % (30439)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.29/0.55  % (30450)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.29/0.55  % (30439)Refutation not found, incomplete strategy% (30439)------------------------------
% 1.29/0.55  % (30439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (30439)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (30439)Memory used [KB]: 10618
% 1.29/0.55  % (30439)Time elapsed: 0.136 s
% 1.29/0.55  % (30439)------------------------------
% 1.29/0.55  % (30439)------------------------------
% 1.29/0.55  % (30435)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.29/0.56  % (30434)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.29/0.56  % (30433)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.29/0.56  % (30431)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.29/0.56  % (30424)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.29/0.56  % (30433)Refutation not found, incomplete strategy% (30433)------------------------------
% 1.29/0.56  % (30433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.56  % (30433)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.56  
% 1.29/0.56  % (30433)Memory used [KB]: 10746
% 1.29/0.56  % (30433)Time elapsed: 0.148 s
% 1.29/0.56  % (30433)------------------------------
% 1.29/0.56  % (30433)------------------------------
% 1.29/0.56  % (30436)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.29/0.56  % (30452)Refutation not found, incomplete strategy% (30452)------------------------------
% 1.29/0.56  % (30452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.56  % (30452)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.56  
% 1.29/0.56  % (30452)Memory used [KB]: 10746
% 1.29/0.56  % (30452)Time elapsed: 0.147 s
% 1.29/0.56  % (30452)------------------------------
% 1.29/0.56  % (30452)------------------------------
% 1.29/0.56  % (30451)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.29/0.57  % (30448)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.29/0.57  % (30429)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.29/0.57  % (30437)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.29/0.57  % (30432)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.29/0.58  % (30449)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.29/0.59  % (30440)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.29/0.61  % (30446)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 2.44/0.72  % (30476)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.44/0.72  % (30475)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.44/0.72  % (30477)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 3.26/0.83  % (30448)Time limit reached!
% 3.26/0.83  % (30448)------------------------------
% 3.26/0.83  % (30448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.26/0.83  % (30448)Termination reason: Time limit
% 3.26/0.83  % (30448)Termination phase: Saturation
% 3.26/0.83  
% 3.26/0.83  % (30448)Memory used [KB]: 14072
% 3.26/0.83  % (30448)Time elapsed: 0.400 s
% 3.26/0.83  % (30448)------------------------------
% 3.26/0.83  % (30448)------------------------------
% 3.45/0.84  % (30425)Time limit reached!
% 3.45/0.84  % (30425)------------------------------
% 3.45/0.84  % (30425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.45/0.84  % (30425)Termination reason: Time limit
% 3.45/0.84  % (30425)Termination phase: Saturation
% 3.45/0.84  
% 3.45/0.84  % (30425)Memory used [KB]: 7291
% 3.45/0.84  % (30425)Time elapsed: 0.400 s
% 3.45/0.84  % (30425)------------------------------
% 3.45/0.84  % (30425)------------------------------
% 3.45/0.91  % (30453)Time limit reached!
% 3.45/0.91  % (30453)------------------------------
% 3.45/0.91  % (30453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.45/0.92  % (30453)Termination reason: Time limit
% 3.45/0.92  % (30453)Termination phase: Saturation
% 3.45/0.92  
% 3.45/0.92  % (30453)Memory used [KB]: 6140
% 3.45/0.92  % (30453)Time elapsed: 0.500 s
% 3.45/0.92  % (30453)------------------------------
% 3.45/0.92  % (30453)------------------------------
% 4.10/0.95  % (30429)Time limit reached!
% 4.10/0.95  % (30429)------------------------------
% 4.10/0.95  % (30429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.10/0.95  % (30429)Termination reason: Time limit
% 4.10/0.95  
% 4.10/0.95  % (30429)Memory used [KB]: 14583
% 4.10/0.95  % (30429)Time elapsed: 0.510 s
% 4.10/0.95  % (30429)------------------------------
% 4.10/0.95  % (30429)------------------------------
% 4.10/0.97  % (30479)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 4.10/0.97  % (30437)Time limit reached!
% 4.10/0.97  % (30437)------------------------------
% 4.10/0.97  % (30437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.10/0.97  % (30437)Termination reason: Time limit
% 4.10/0.97  
% 4.10/0.97  % (30437)Memory used [KB]: 5500
% 4.10/0.97  % (30437)Time elapsed: 0.530 s
% 4.10/0.97  % (30437)------------------------------
% 4.10/0.97  % (30437)------------------------------
% 4.10/0.99  % (30478)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.51/1.05  % (30480)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 5.58/1.08  % (30430)Time limit reached!
% 5.58/1.08  % (30430)------------------------------
% 5.58/1.08  % (30430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.58/1.08  % (30430)Termination reason: Time limit
% 5.58/1.08  % (30430)Termination phase: Saturation
% 5.58/1.08  
% 5.58/1.08  % (30430)Memory used [KB]: 8059
% 5.58/1.08  % (30430)Time elapsed: 0.600 s
% 5.58/1.08  % (30430)------------------------------
% 5.58/1.08  % (30430)------------------------------
% 5.58/1.09  % (30481)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 5.91/1.14  % (30482)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 6.75/1.24  % (30424)Time limit reached!
% 6.75/1.24  % (30424)------------------------------
% 6.75/1.24  % (30424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.75/1.24  % (30424)Termination reason: Time limit
% 6.75/1.24  
% 6.75/1.24  % (30424)Memory used [KB]: 7675
% 6.75/1.24  % (30424)Time elapsed: 0.823 s
% 6.75/1.24  % (30424)------------------------------
% 6.75/1.24  % (30424)------------------------------
% 6.75/1.25  % (30483)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 7.17/1.33  % (30426)Time limit reached!
% 7.17/1.33  % (30426)------------------------------
% 7.17/1.33  % (30426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.17/1.33  % (30426)Termination reason: Time limit
% 7.17/1.33  
% 7.17/1.33  % (30426)Memory used [KB]: 11897
% 7.17/1.33  % (30426)Time elapsed: 0.914 s
% 7.17/1.33  % (30426)------------------------------
% 7.17/1.33  % (30426)------------------------------
% 7.87/1.37  % (30484)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 7.87/1.41  % (30451)Time limit reached!
% 7.87/1.41  % (30451)------------------------------
% 7.87/1.41  % (30451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.87/1.41  % (30451)Termination reason: Time limit
% 7.87/1.41  % (30451)Termination phase: Saturation
% 7.87/1.41  
% 7.87/1.41  % (30451)Memory used [KB]: 13176
% 7.87/1.41  % (30451)Time elapsed: 1.0000 s
% 7.87/1.41  % (30451)------------------------------
% 7.87/1.41  % (30451)------------------------------
% 8.16/1.43  % (30435)Time limit reached!
% 8.16/1.43  % (30435)------------------------------
% 8.16/1.43  % (30435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.16/1.43  % (30435)Termination reason: Time limit
% 8.16/1.43  % (30435)Termination phase: Saturation
% 8.16/1.43  
% 8.16/1.43  % (30435)Memory used [KB]: 19061
% 8.16/1.43  % (30435)Time elapsed: 1.0000 s
% 8.16/1.43  % (30435)------------------------------
% 8.16/1.43  % (30435)------------------------------
% 8.40/1.48  % (30485)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 8.40/1.50  % (30450)Refutation found. Thanks to Tanya!
% 8.40/1.50  % SZS status Theorem for theBenchmark
% 8.40/1.50  % SZS output start Proof for theBenchmark
% 8.40/1.50  fof(f11584,plain,(
% 8.40/1.50    $false),
% 8.40/1.50    inference(avatar_sat_refutation,[],[f148,f167,f171,f11582])).
% 8.40/1.50  fof(f11582,plain,(
% 8.40/1.50    ~spl2_1 | ~spl2_2 | spl2_3),
% 8.40/1.50    inference(avatar_contradiction_clause,[],[f11581])).
% 8.40/1.50  fof(f11581,plain,(
% 8.40/1.50    $false | (~spl2_1 | ~spl2_2 | spl2_3)),
% 8.40/1.50    inference(subsumption_resolution,[],[f7784,f11569])).
% 8.40/1.50  fof(f11569,plain,(
% 8.40/1.50    ( ! [X2] : (r1_tarski(k1_relat_1(k7_relat_1(sK1,X2)),k1_relat_1(k8_relat_1(k9_relat_1(sK1,X2),sK1)))) ) | ~spl2_1),
% 8.40/1.50    inference(superposition,[],[f245,f2318])).
% 8.40/1.50  fof(f2318,plain,(
% 8.40/1.50    ( ! [X1] : (k7_relat_1(sK1,X1) = k7_relat_1(k8_relat_1(k9_relat_1(sK1,X1),sK1),X1)) ) | ~spl2_1),
% 8.40/1.50    inference(superposition,[],[f230,f160])).
% 8.40/1.50  fof(f160,plain,(
% 8.40/1.50    ( ! [X8,X7] : (k7_relat_1(k8_relat_1(X7,sK1),X8) = k8_relat_1(X7,k7_relat_1(sK1,X8))) ) | ~spl2_1),
% 8.40/1.50    inference(resolution,[],[f147,f131])).
% 8.40/1.50  fof(f131,plain,(
% 8.40/1.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1))) )),
% 8.40/1.50    inference(cnf_transformation,[],[f77])).
% 8.40/1.50  fof(f77,plain,(
% 8.40/1.50    ! [X0,X1,X2] : (k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 8.40/1.50    inference(ennf_transformation,[],[f45])).
% 8.40/1.50  fof(f45,axiom,(
% 8.40/1.50    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k8_relat_1(X0,X2),X1) = k8_relat_1(X0,k7_relat_1(X2,X1)))),
% 8.40/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_relat_1)).
% 8.40/1.50  fof(f147,plain,(
% 8.40/1.50    v1_relat_1(sK1) | ~spl2_1),
% 8.40/1.50    inference(avatar_component_clause,[],[f146])).
% 8.40/1.50  fof(f146,plain,(
% 8.40/1.50    spl2_1 <=> v1_relat_1(sK1)),
% 8.40/1.50    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 8.40/1.50  fof(f230,plain,(
% 8.40/1.50    ( ! [X17] : (k7_relat_1(sK1,X17) = k8_relat_1(k9_relat_1(sK1,X17),k7_relat_1(sK1,X17))) ) | ~spl2_1),
% 8.40/1.50    inference(forward_demodulation,[],[f224,f149])).
% 8.40/1.50  fof(f149,plain,(
% 8.40/1.50    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) ) | ~spl2_1),
% 8.40/1.50    inference(resolution,[],[f147,f99])).
% 8.40/1.50  fof(f99,plain,(
% 8.40/1.50    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 8.40/1.50    inference(cnf_transformation,[],[f67])).
% 8.40/1.50  fof(f67,plain,(
% 8.40/1.50    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 8.40/1.50    inference(ennf_transformation,[],[f46])).
% 8.40/1.50  fof(f46,axiom,(
% 8.40/1.50    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 8.40/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 8.40/1.50  fof(f224,plain,(
% 8.40/1.50    ( ! [X17] : (k7_relat_1(sK1,X17) = k8_relat_1(k2_relat_1(k7_relat_1(sK1,X17)),k7_relat_1(sK1,X17))) ) | ~spl2_1),
% 8.40/1.50    inference(resolution,[],[f158,f130])).
% 8.40/1.50  fof(f130,plain,(
% 8.40/1.50    ( ! [X0] : (~v1_relat_1(X0) | k8_relat_1(k2_relat_1(X0),X0) = X0) )),
% 8.40/1.50    inference(cnf_transformation,[],[f76])).
% 8.40/1.50  fof(f76,plain,(
% 8.40/1.50    ! [X0] : (k8_relat_1(k2_relat_1(X0),X0) = X0 | ~v1_relat_1(X0))),
% 8.40/1.50    inference(ennf_transformation,[],[f44])).
% 8.40/1.50  fof(f44,axiom,(
% 8.40/1.50    ! [X0] : (v1_relat_1(X0) => k8_relat_1(k2_relat_1(X0),X0) = X0)),
% 8.40/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_relat_1)).
% 8.40/1.50  fof(f158,plain,(
% 8.40/1.50    ( ! [X6] : (v1_relat_1(k7_relat_1(sK1,X6))) ) | ~spl2_1),
% 8.40/1.50    inference(resolution,[],[f147,f125])).
% 8.40/1.50  fof(f125,plain,(
% 8.40/1.50    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1))) )),
% 8.40/1.50    inference(cnf_transformation,[],[f75])).
% 8.40/1.50  fof(f75,plain,(
% 8.40/1.50    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 8.40/1.50    inference(ennf_transformation,[],[f39])).
% 8.40/1.50  fof(f39,axiom,(
% 8.40/1.50    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 8.40/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 8.40/1.50  fof(f245,plain,(
% 8.40/1.50    ( ! [X12,X11] : (r1_tarski(k1_relat_1(k7_relat_1(k8_relat_1(X11,sK1),X12)),k1_relat_1(k8_relat_1(X11,sK1)))) ) | ~spl2_1),
% 8.40/1.50    inference(resolution,[],[f163,f121])).
% 8.40/1.50  fof(f121,plain,(
% 8.40/1.50    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))) )),
% 8.40/1.50    inference(cnf_transformation,[],[f73])).
% 8.40/1.50  fof(f73,plain,(
% 8.40/1.50    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 8.40/1.50    inference(ennf_transformation,[],[f52])).
% 8.40/1.50  fof(f52,axiom,(
% 8.40/1.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 8.40/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).
% 8.40/1.50  fof(f163,plain,(
% 8.40/1.50    ( ! [X11] : (v1_relat_1(k8_relat_1(X11,sK1))) ) | ~spl2_1),
% 8.40/1.50    inference(resolution,[],[f147,f141])).
% 8.40/1.50  fof(f141,plain,(
% 8.40/1.50    ( ! [X0,X1] : (~v1_relat_1(X1) | v1_relat_1(k8_relat_1(X0,X1))) )),
% 8.40/1.50    inference(cnf_transformation,[],[f80])).
% 8.40/1.50  fof(f80,plain,(
% 8.40/1.50    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 8.40/1.50    inference(ennf_transformation,[],[f40])).
% 8.40/1.50  fof(f40,axiom,(
% 8.40/1.50    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 8.40/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 8.40/1.50  fof(f7784,plain,(
% 8.40/1.50    ~r1_tarski(k1_relat_1(k7_relat_1(sK1,sK0)),k1_relat_1(k8_relat_1(k9_relat_1(sK1,sK0),sK1))) | (~spl2_1 | ~spl2_2 | spl2_3)),
% 8.40/1.50    inference(forward_demodulation,[],[f7783,f535])).
% 8.40/1.50  fof(f535,plain,(
% 8.40/1.50    ( ! [X1] : (k1_relat_1(k7_relat_1(sK1,X1)) = k3_xboole_0(X1,k1_relat_1(sK1))) ) | ~spl2_1),
% 8.40/1.50    inference(superposition,[],[f155,f119])).
% 8.40/1.50  fof(f119,plain,(
% 8.40/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 8.40/1.50    inference(cnf_transformation,[],[f2])).
% 8.40/1.50  fof(f2,axiom,(
% 8.40/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 8.40/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 8.40/1.50  fof(f155,plain,(
% 8.40/1.50    ( ! [X3] : (k1_relat_1(k7_relat_1(sK1,X3)) = k3_xboole_0(k1_relat_1(sK1),X3)) ) | ~spl2_1),
% 8.40/1.50    inference(resolution,[],[f147,f120])).
% 8.40/1.50  fof(f120,plain,(
% 8.40/1.50    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 8.40/1.50    inference(cnf_transformation,[],[f72])).
% 8.40/1.50  fof(f72,plain,(
% 8.40/1.50    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 8.40/1.50    inference(ennf_transformation,[],[f53])).
% 8.40/1.50  fof(f53,axiom,(
% 8.40/1.50    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 8.40/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 8.40/1.50  fof(f7783,plain,(
% 8.40/1.50    ~r1_tarski(k3_xboole_0(sK0,k1_relat_1(sK1)),k1_relat_1(k8_relat_1(k9_relat_1(sK1,sK0),sK1))) | (~spl2_1 | ~spl2_2 | spl2_3)),
% 8.40/1.50    inference(superposition,[],[f170,f1517])).
% 8.40/1.50  fof(f1517,plain,(
% 8.40/1.50    ( ! [X0] : (k9_relat_1(k4_relat_1(sK1),X0) = k1_relat_1(k8_relat_1(X0,sK1))) ) | (~spl2_1 | ~spl2_2)),
% 8.40/1.50    inference(forward_demodulation,[],[f1516,f241])).
% 8.40/1.50  fof(f241,plain,(
% 8.40/1.50    ( ! [X5] : (k1_relat_1(k8_relat_1(X5,sK1)) = k2_relat_1(k4_relat_1(k8_relat_1(X5,sK1)))) ) | ~spl2_1),
% 8.40/1.50    inference(resolution,[],[f163,f102])).
% 8.40/1.50  fof(f102,plain,(
% 8.40/1.50    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 8.40/1.50    inference(cnf_transformation,[],[f69])).
% 8.40/1.50  fof(f69,plain,(
% 8.40/1.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 8.40/1.50    inference(ennf_transformation,[],[f47])).
% 8.40/1.50  fof(f47,axiom,(
% 8.40/1.50    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 8.40/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 8.40/1.50  fof(f1516,plain,(
% 8.40/1.50    ( ! [X0] : (k9_relat_1(k4_relat_1(sK1),X0) = k2_relat_1(k4_relat_1(k8_relat_1(X0,sK1)))) ) | (~spl2_1 | ~spl2_2)),
% 8.40/1.50    inference(superposition,[],[f172,f628])).
% 8.40/1.50  fof(f628,plain,(
% 8.40/1.50    ( ! [X5] : (k7_relat_1(k4_relat_1(sK1),X5) = k4_relat_1(k8_relat_1(X5,sK1))) ) | (~spl2_1 | ~spl2_2)),
% 8.40/1.50    inference(forward_demodulation,[],[f627,f162])).
% 8.40/1.50  fof(f162,plain,(
% 8.40/1.50    ( ! [X10] : (k8_relat_1(X10,sK1) = k5_relat_1(sK1,k6_relat_1(X10))) ) | ~spl2_1),
% 8.40/1.50    inference(resolution,[],[f147,f134])).
% 8.40/1.50  fof(f134,plain,(
% 8.40/1.50    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 8.40/1.50    inference(cnf_transformation,[],[f79])).
% 8.40/1.50  fof(f79,plain,(
% 8.40/1.50    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 8.40/1.50    inference(ennf_transformation,[],[f43])).
% 8.40/1.50  fof(f43,axiom,(
% 8.40/1.50    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 8.40/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 8.40/1.50  fof(f627,plain,(
% 8.40/1.50    ( ! [X5] : (k7_relat_1(k4_relat_1(sK1),X5) = k4_relat_1(k5_relat_1(sK1,k6_relat_1(X5)))) ) | (~spl2_1 | ~spl2_2)),
% 8.40/1.50    inference(forward_demodulation,[],[f626,f184])).
% 8.40/1.50  fof(f184,plain,(
% 8.40/1.50    ( ! [X9] : (k7_relat_1(k4_relat_1(sK1),X9) = k5_relat_1(k6_relat_1(X9),k4_relat_1(sK1))) ) | ~spl2_2),
% 8.40/1.50    inference(resolution,[],[f166,f133])).
% 8.40/1.50  fof(f133,plain,(
% 8.40/1.50    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 8.40/1.50    inference(cnf_transformation,[],[f78])).
% 8.40/1.50  fof(f78,plain,(
% 8.40/1.50    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 8.40/1.50    inference(ennf_transformation,[],[f54])).
% 8.40/1.50  fof(f54,axiom,(
% 8.40/1.50    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 8.40/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 8.40/1.50  fof(f166,plain,(
% 8.40/1.50    v1_relat_1(k4_relat_1(sK1)) | ~spl2_2),
% 8.40/1.50    inference(avatar_component_clause,[],[f165])).
% 8.40/1.50  fof(f165,plain,(
% 8.40/1.50    spl2_2 <=> v1_relat_1(k4_relat_1(sK1))),
% 8.40/1.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 8.40/1.50  fof(f626,plain,(
% 8.40/1.50    ( ! [X5] : (k4_relat_1(k5_relat_1(sK1,k6_relat_1(X5))) = k5_relat_1(k6_relat_1(X5),k4_relat_1(sK1))) ) | ~spl2_1),
% 8.40/1.50    inference(forward_demodulation,[],[f618,f104])).
% 8.40/1.50  fof(f104,plain,(
% 8.40/1.50    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 8.40/1.50    inference(cnf_transformation,[],[f50])).
% 8.40/1.50  fof(f50,axiom,(
% 8.40/1.50    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 8.40/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).
% 8.40/1.50  fof(f618,plain,(
% 8.40/1.50    ( ! [X5] : (k4_relat_1(k5_relat_1(sK1,k6_relat_1(X5))) = k5_relat_1(k4_relat_1(k6_relat_1(X5)),k4_relat_1(sK1))) ) | ~spl2_1),
% 8.40/1.50    inference(resolution,[],[f150,f135])).
% 8.40/1.50  fof(f135,plain,(
% 8.40/1.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 8.40/1.50    inference(cnf_transformation,[],[f38])).
% 8.40/1.50  fof(f38,axiom,(
% 8.40/1.50    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 8.40/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 8.40/1.50  fof(f150,plain,(
% 8.40/1.50    ( ! [X1] : (~v1_relat_1(X1) | k4_relat_1(k5_relat_1(sK1,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(sK1))) ) | ~spl2_1),
% 8.40/1.50    inference(resolution,[],[f147,f100])).
% 8.40/1.50  fof(f100,plain,(
% 8.40/1.50    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))) )),
% 8.40/1.50    inference(cnf_transformation,[],[f68])).
% 8.40/1.50  fof(f68,plain,(
% 8.40/1.50    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 8.40/1.50    inference(ennf_transformation,[],[f48])).
% 8.40/1.50  fof(f48,axiom,(
% 8.40/1.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 8.40/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_relat_1)).
% 8.40/1.50  fof(f172,plain,(
% 8.40/1.50    ( ! [X0] : (k2_relat_1(k7_relat_1(k4_relat_1(sK1),X0)) = k9_relat_1(k4_relat_1(sK1),X0)) ) | ~spl2_2),
% 8.40/1.50    inference(resolution,[],[f166,f99])).
% 8.40/1.50  fof(f170,plain,(
% 8.40/1.50    ~r1_tarski(k3_xboole_0(sK0,k1_relat_1(sK1)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0))) | spl2_3),
% 8.40/1.50    inference(avatar_component_clause,[],[f169])).
% 8.40/1.50  fof(f169,plain,(
% 8.40/1.50    spl2_3 <=> r1_tarski(k3_xboole_0(sK0,k1_relat_1(sK1)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0)))),
% 8.40/1.50    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 8.40/1.50  fof(f171,plain,(
% 8.40/1.50    ~spl2_3),
% 8.40/1.50    inference(avatar_split_clause,[],[f144,f169])).
% 8.40/1.50  fof(f144,plain,(
% 8.40/1.50    ~r1_tarski(k3_xboole_0(sK0,k1_relat_1(sK1)),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0)))),
% 8.40/1.50    inference(forward_demodulation,[],[f82,f119])).
% 8.40/1.50  fof(f82,plain,(
% 8.40/1.50    ~r1_tarski(k3_xboole_0(k1_relat_1(sK1),sK0),k9_relat_1(k4_relat_1(sK1),k9_relat_1(sK1,sK0)))),
% 8.40/1.50    inference(cnf_transformation,[],[f57])).
% 8.40/1.50  fof(f57,plain,(
% 8.40/1.50    ? [X0,X1] : (~r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))) & v1_relat_1(X1))),
% 8.40/1.50    inference(ennf_transformation,[],[f56])).
% 8.40/1.50  fof(f56,negated_conjecture,(
% 8.40/1.50    ~! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))))),
% 8.40/1.50    inference(negated_conjecture,[],[f55])).
% 8.40/1.50  fof(f55,conjecture,(
% 8.40/1.50    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k3_xboole_0(k1_relat_1(X1),X0),k9_relat_1(k4_relat_1(X1),k9_relat_1(X1,X0))))),
% 8.40/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_relat_1)).
% 8.40/1.50  fof(f167,plain,(
% 8.40/1.50    spl2_2 | ~spl2_1),
% 8.40/1.50    inference(avatar_split_clause,[],[f153,f146,f165])).
% 8.40/1.50  fof(f153,plain,(
% 8.40/1.50    v1_relat_1(k4_relat_1(sK1)) | ~spl2_1),
% 8.40/1.50    inference(resolution,[],[f147,f103])).
% 8.40/1.50  fof(f103,plain,(
% 8.40/1.50    ( ! [X0] : (~v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0))) )),
% 8.40/1.50    inference(cnf_transformation,[],[f70])).
% 8.40/1.50  fof(f70,plain,(
% 8.40/1.50    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 8.40/1.50    inference(ennf_transformation,[],[f37])).
% 8.40/1.50  fof(f37,axiom,(
% 8.40/1.50    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 8.40/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 8.40/1.50  fof(f148,plain,(
% 8.40/1.50    spl2_1),
% 8.40/1.50    inference(avatar_split_clause,[],[f81,f146])).
% 8.40/1.50  fof(f81,plain,(
% 8.40/1.50    v1_relat_1(sK1)),
% 8.40/1.50    inference(cnf_transformation,[],[f57])).
% 8.40/1.50  % SZS output end Proof for theBenchmark
% 8.40/1.50  % (30450)------------------------------
% 8.40/1.50  % (30450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.40/1.50  % (30450)Termination reason: Refutation
% 8.40/1.50  
% 8.40/1.50  % (30450)Memory used [KB]: 16375
% 8.40/1.50  % (30450)Time elapsed: 1.065 s
% 8.40/1.50  % (30450)------------------------------
% 8.40/1.50  % (30450)------------------------------
% 8.40/1.50  % (30422)Success in time 1.127 s
%------------------------------------------------------------------------------
