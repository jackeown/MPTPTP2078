%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:24 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 459 expanded)
%              Number of leaves         :   17 ( 142 expanded)
%              Depth                    :   19
%              Number of atoms          :  203 ( 959 expanded)
%              Number of equality atoms :   74 ( 394 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f615,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f75,f80,f125,f604])).

fof(f604,plain,
    ( ~ spl3_3
    | spl3_7 ),
    inference(avatar_contradiction_clause,[],[f574])).

fof(f574,plain,
    ( $false
    | ~ spl3_3
    | spl3_7 ),
    inference(unit_resulting_resolution,[],[f74,f124,f540])).

fof(f540,plain,(
    ! [X2,X1] :
      ( k3_xboole_0(X2,X1) = X1
      | ~ r1_tarski(X1,X2) ) ),
    inference(superposition,[],[f441,f162])).

fof(f162,plain,(
    ! [X2,X3] :
      ( k3_xboole_0(X3,X2) = X3
      | ~ r1_tarski(X3,X2) ) ),
    inference(superposition,[],[f156,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1)) = X1
      | ~ r1_tarski(X1,X0) ) ),
    inference(global_subsumption,[],[f54,f55,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1)) = X1
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f129,f58])).

fof(f58,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f129,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1)) = X1
      | ~ r1_tarski(X1,k2_relat_1(k6_relat_1(X0)))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f49,f114])).

fof(f114,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k9_relat_1(k6_relat_1(X0),X1) ),
    inference(global_subsumption,[],[f54,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k9_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f112,f58])).

fof(f112,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k6_relat_1(k3_xboole_0(X0,X1)))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f46,f110])).

fof(f110,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X3),X2) = k6_relat_1(k3_xboole_0(X3,X2)) ),
    inference(global_subsumption,[],[f54,f108])).

fof(f108,plain,(
    ! [X2,X3] :
      ( k7_relat_1(k6_relat_1(X3),X2) = k6_relat_1(k3_xboole_0(X3,X2))
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(superposition,[],[f56,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f56,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

fof(f55,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f54,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f156,plain,(
    ! [X0,X1] : k3_xboole_0(X1,X0) = k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1)) ),
    inference(global_subsumption,[],[f54,f55,f155])).

fof(f155,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,X0) = k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f154,f114])).

fof(f154,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f153,f134])).

fof(f134,plain,(
    ! [X1] : k3_xboole_0(X1,X1) = X1 ),
    inference(global_subsumption,[],[f54,f55,f59,f133])).

fof(f133,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,X1)
      | k3_xboole_0(X1,X1) = X1
      | ~ v1_funct_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f132,f58])).

fof(f132,plain,(
    ! [X1] :
      ( k3_xboole_0(X1,X1) = X1
      | ~ r1_tarski(X1,k2_relat_1(k6_relat_1(X1)))
      | ~ v1_funct_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f127,f114])).

fof(f127,plain,(
    ! [X1] :
      ( k9_relat_1(k6_relat_1(X1),X1) = X1
      | ~ r1_tarski(X1,k2_relat_1(k6_relat_1(X1)))
      | ~ v1_funct_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(superposition,[],[f49,f102])).

fof(f102,plain,(
    ! [X0] : k10_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(global_subsumption,[],[f54,f101])).

fof(f101,plain,(
    ! [X0] :
      ( k10_relat_1(k6_relat_1(X0),X0) = X0
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f97,f57])).

fof(f57,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f97,plain,(
    ! [X0] :
      ( k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f53,f58])).

fof(f53,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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

fof(f153,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f147,f114])).

fof(f147,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k9_relat_1(k6_relat_1(X0),X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f52,f57])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).

fof(f441,plain,(
    ! [X12,X11] : k3_xboole_0(X12,X11) = k3_xboole_0(X11,k3_xboole_0(X12,X11)) ),
    inference(superposition,[],[f156,f408])).

fof(f408,plain,(
    ! [X0,X1] : k3_xboole_0(X1,X0) = k10_relat_1(k6_relat_1(X0),X1) ),
    inference(forward_demodulation,[],[f379,f156])).

fof(f379,plain,(
    ! [X0,X1] : k10_relat_1(k6_relat_1(X0),X1) = k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1)) ),
    inference(superposition,[],[f120,f134])).

fof(f120,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X1,k10_relat_1(k6_relat_1(X0),X2)) = k10_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),X2) ),
    inference(global_subsumption,[],[f54,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,k10_relat_1(k6_relat_1(X0),X2)) = k10_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),X2)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f45,f110])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f124,plain,
    ( k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl3_7
  <=> k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f74,plain,
    ( r1_tarski(k10_relat_1(sK0,sK2),sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl3_3
  <=> r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f125,plain,
    ( ~ spl3_1
    | ~ spl3_7
    | spl3_4 ),
    inference(avatar_split_clause,[],[f119,f77,f122,f62])).

fof(f62,plain,
    ( spl3_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f77,plain,
    ( spl3_4
  <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f119,plain,
    ( k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK0)
    | spl3_4 ),
    inference(superposition,[],[f79,f45])).

fof(f79,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f80,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f41,f77])).

fof(f41,plain,(
    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(k10_relat_1(sK0,sK2),sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(k10_relat_1(sK0,X2),X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X2,X1] :
        ( k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2)
        & r1_tarski(k10_relat_1(sK0,X2),X1) )
   => ( k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)
      & r1_tarski(k10_relat_1(sK0,sK2),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

fof(f75,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f40,f72])).

fof(f40,plain,(
    r1_tarski(k10_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f65,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f38,f62])).

fof(f38,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:49:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (23258)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (23250)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (23237)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (23238)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (23242)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (23248)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (23243)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (23241)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (23251)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (23239)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (23259)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.30/0.54  % (23261)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.30/0.54  % (23236)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.30/0.54  % (23265)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.30/0.54  % (23265)Refutation not found, incomplete strategy% (23265)------------------------------
% 1.30/0.54  % (23265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (23265)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (23265)Memory used [KB]: 1663
% 1.30/0.54  % (23265)Time elapsed: 0.128 s
% 1.30/0.54  % (23265)------------------------------
% 1.30/0.54  % (23265)------------------------------
% 1.30/0.54  % (23237)Refutation not found, incomplete strategy% (23237)------------------------------
% 1.30/0.54  % (23237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (23248)Refutation not found, incomplete strategy% (23248)------------------------------
% 1.30/0.54  % (23248)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.54  % (23253)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.30/0.54  % (23237)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.54  
% 1.30/0.54  % (23237)Memory used [KB]: 1791
% 1.30/0.54  % (23237)Time elapsed: 0.111 s
% 1.30/0.54  % (23237)------------------------------
% 1.30/0.54  % (23237)------------------------------
% 1.30/0.54  % (23240)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.30/0.54  % (23255)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.30/0.54  % (23245)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.30/0.54  % (23249)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.30/0.54  % (23262)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.30/0.54  % (23247)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.30/0.55  % (23264)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.30/0.55  % (23260)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.30/0.55  % (23264)Refutation not found, incomplete strategy% (23264)------------------------------
% 1.30/0.55  % (23264)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (23264)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (23264)Memory used [KB]: 10746
% 1.30/0.55  % (23264)Time elapsed: 0.141 s
% 1.30/0.55  % (23264)------------------------------
% 1.30/0.55  % (23264)------------------------------
% 1.30/0.55  % (23262)Refutation not found, incomplete strategy% (23262)------------------------------
% 1.30/0.55  % (23262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (23262)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (23262)Memory used [KB]: 6396
% 1.30/0.55  % (23262)Time elapsed: 0.142 s
% 1.30/0.55  % (23262)------------------------------
% 1.30/0.55  % (23262)------------------------------
% 1.30/0.55  % (23254)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.30/0.55  % (23257)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.30/0.55  % (23252)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.30/0.55  % (23252)Refutation not found, incomplete strategy% (23252)------------------------------
% 1.30/0.55  % (23252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (23252)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (23252)Memory used [KB]: 10618
% 1.30/0.55  % (23252)Time elapsed: 0.140 s
% 1.30/0.55  % (23252)------------------------------
% 1.30/0.55  % (23252)------------------------------
% 1.30/0.55  % (23254)Refutation not found, incomplete strategy% (23254)------------------------------
% 1.30/0.55  % (23254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.55  % (23254)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.55  
% 1.30/0.55  % (23254)Memory used [KB]: 1791
% 1.30/0.55  % (23254)Time elapsed: 0.143 s
% 1.30/0.55  % (23254)------------------------------
% 1.30/0.55  % (23254)------------------------------
% 1.50/0.55  % (23246)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.50/0.55  % (23248)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.55  
% 1.50/0.55  % (23248)Memory used [KB]: 10746
% 1.50/0.55  % (23248)Time elapsed: 0.113 s
% 1.50/0.55  % (23248)------------------------------
% 1.50/0.55  % (23248)------------------------------
% 1.50/0.56  % (23244)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.50/0.56  % (23246)Refutation not found, incomplete strategy% (23246)------------------------------
% 1.50/0.56  % (23246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (23246)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (23246)Memory used [KB]: 10746
% 1.50/0.56  % (23246)Time elapsed: 0.153 s
% 1.50/0.56  % (23246)------------------------------
% 1.50/0.56  % (23246)------------------------------
% 1.50/0.56  % (23256)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.50/0.56  % (23261)Refutation not found, incomplete strategy% (23261)------------------------------
% 1.50/0.56  % (23261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (23261)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (23261)Memory used [KB]: 6268
% 1.50/0.56  % (23261)Time elapsed: 0.134 s
% 1.50/0.56  % (23261)------------------------------
% 1.50/0.56  % (23261)------------------------------
% 1.50/0.56  % (23263)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.50/0.58  % (23259)Refutation found. Thanks to Tanya!
% 1.50/0.58  % SZS status Theorem for theBenchmark
% 1.50/0.58  % SZS output start Proof for theBenchmark
% 1.50/0.58  fof(f615,plain,(
% 1.50/0.58    $false),
% 1.50/0.58    inference(avatar_sat_refutation,[],[f65,f75,f80,f125,f604])).
% 1.50/0.58  fof(f604,plain,(
% 1.50/0.58    ~spl3_3 | spl3_7),
% 1.50/0.58    inference(avatar_contradiction_clause,[],[f574])).
% 1.50/0.58  fof(f574,plain,(
% 1.50/0.58    $false | (~spl3_3 | spl3_7)),
% 1.50/0.58    inference(unit_resulting_resolution,[],[f74,f124,f540])).
% 1.50/0.58  fof(f540,plain,(
% 1.50/0.58    ( ! [X2,X1] : (k3_xboole_0(X2,X1) = X1 | ~r1_tarski(X1,X2)) )),
% 1.50/0.58    inference(superposition,[],[f441,f162])).
% 1.50/0.58  fof(f162,plain,(
% 1.50/0.58    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X3 | ~r1_tarski(X3,X2)) )),
% 1.50/0.58    inference(superposition,[],[f156,f136])).
% 1.50/0.58  fof(f136,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1)) = X1 | ~r1_tarski(X1,X0)) )),
% 1.50/0.58    inference(global_subsumption,[],[f54,f55,f135])).
% 1.50/0.58  fof(f135,plain,(
% 1.50/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1)) = X1 | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.50/0.58    inference(forward_demodulation,[],[f129,f58])).
% 1.50/0.58  fof(f58,plain,(
% 1.50/0.58    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.50/0.58    inference(cnf_transformation,[],[f10])).
% 1.50/0.58  fof(f10,axiom,(
% 1.50/0.58    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.50/0.58  fof(f129,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1)) = X1 | ~r1_tarski(X1,k2_relat_1(k6_relat_1(X0))) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.50/0.58    inference(superposition,[],[f49,f114])).
% 1.50/0.58  fof(f114,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k9_relat_1(k6_relat_1(X0),X1)) )),
% 1.50/0.58    inference(global_subsumption,[],[f54,f113])).
% 1.50/0.58  fof(f113,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k9_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.50/0.58    inference(forward_demodulation,[],[f112,f58])).
% 1.50/0.58  fof(f112,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k6_relat_1(k3_xboole_0(X0,X1))) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.50/0.58    inference(superposition,[],[f46,f110])).
% 1.50/0.58  fof(f110,plain,(
% 1.50/0.58    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X3),X2) = k6_relat_1(k3_xboole_0(X3,X2))) )),
% 1.50/0.58    inference(global_subsumption,[],[f54,f108])).
% 1.50/0.58  fof(f108,plain,(
% 1.50/0.58    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X3),X2) = k6_relat_1(k3_xboole_0(X3,X2)) | ~v1_relat_1(k6_relat_1(X3))) )),
% 1.50/0.58    inference(superposition,[],[f56,f47])).
% 1.50/0.58  fof(f47,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f24])).
% 1.50/0.58  fof(f24,plain,(
% 1.50/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.50/0.58    inference(ennf_transformation,[],[f11])).
% 1.50/0.58  fof(f11,axiom,(
% 1.50/0.58    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 1.50/0.58  fof(f56,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 1.50/0.58    inference(cnf_transformation,[],[f17])).
% 1.50/0.58  fof(f17,axiom,(
% 1.50/0.58    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 1.50/0.58  fof(f46,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f23])).
% 1.50/0.58  fof(f23,plain,(
% 1.50/0.58    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.50/0.58    inference(ennf_transformation,[],[f7])).
% 1.50/0.58  fof(f7,axiom,(
% 1.50/0.58    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.50/0.58  fof(f49,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f28])).
% 1.50/0.58  fof(f28,plain,(
% 1.50/0.58    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.50/0.58    inference(flattening,[],[f27])).
% 1.50/0.58  fof(f27,plain,(
% 1.50/0.58    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.50/0.58    inference(ennf_transformation,[],[f14])).
% 1.50/0.58  fof(f14,axiom,(
% 1.50/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).
% 1.50/0.58  fof(f55,plain,(
% 1.50/0.58    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.50/0.58    inference(cnf_transformation,[],[f12])).
% 1.50/0.58  fof(f12,axiom,(
% 1.50/0.58    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.50/0.58  fof(f54,plain,(
% 1.50/0.58    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.50/0.58    inference(cnf_transformation,[],[f12])).
% 1.50/0.58  fof(f156,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1))) )),
% 1.50/0.58    inference(global_subsumption,[],[f54,f55,f155])).
% 1.50/0.58  fof(f155,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1)) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.50/0.58    inference(forward_demodulation,[],[f154,f114])).
% 1.50/0.58  fof(f154,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.50/0.58    inference(forward_demodulation,[],[f153,f134])).
% 1.50/0.58  fof(f134,plain,(
% 1.50/0.58    ( ! [X1] : (k3_xboole_0(X1,X1) = X1) )),
% 1.50/0.58    inference(global_subsumption,[],[f54,f55,f59,f133])).
% 1.50/0.58  fof(f133,plain,(
% 1.50/0.58    ( ! [X1] : (~r1_tarski(X1,X1) | k3_xboole_0(X1,X1) = X1 | ~v1_funct_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 1.50/0.58    inference(forward_demodulation,[],[f132,f58])).
% 1.50/0.58  fof(f132,plain,(
% 1.50/0.58    ( ! [X1] : (k3_xboole_0(X1,X1) = X1 | ~r1_tarski(X1,k2_relat_1(k6_relat_1(X1))) | ~v1_funct_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 1.50/0.58    inference(forward_demodulation,[],[f127,f114])).
% 1.50/0.58  fof(f127,plain,(
% 1.50/0.58    ( ! [X1] : (k9_relat_1(k6_relat_1(X1),X1) = X1 | ~r1_tarski(X1,k2_relat_1(k6_relat_1(X1))) | ~v1_funct_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X1))) )),
% 1.50/0.58    inference(superposition,[],[f49,f102])).
% 1.50/0.58  fof(f102,plain,(
% 1.50/0.58    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0) )),
% 1.50/0.58    inference(global_subsumption,[],[f54,f101])).
% 1.50/0.58  fof(f101,plain,(
% 1.50/0.58    ( ! [X0] : (k10_relat_1(k6_relat_1(X0),X0) = X0 | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.50/0.58    inference(forward_demodulation,[],[f97,f57])).
% 1.50/0.58  fof(f57,plain,(
% 1.50/0.58    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.50/0.58    inference(cnf_transformation,[],[f10])).
% 1.50/0.58  fof(f97,plain,(
% 1.50/0.58    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = k10_relat_1(k6_relat_1(X0),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.50/0.58    inference(superposition,[],[f53,f58])).
% 1.50/0.58  fof(f53,plain,(
% 1.50/0.58    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f32])).
% 1.50/0.58  fof(f32,plain,(
% 1.50/0.58    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.50/0.58    inference(ennf_transformation,[],[f9])).
% 1.50/0.58  fof(f9,axiom,(
% 1.50/0.58    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 1.50/0.58  fof(f59,plain,(
% 1.50/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.50/0.58    inference(equality_resolution,[],[f43])).
% 1.50/0.58  fof(f43,plain,(
% 1.50/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.50/0.58    inference(cnf_transformation,[],[f37])).
% 1.50/0.58  fof(f37,plain,(
% 1.50/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.50/0.58    inference(flattening,[],[f36])).
% 1.50/0.58  fof(f36,plain,(
% 1.50/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.50/0.58    inference(nnf_transformation,[],[f1])).
% 1.50/0.58  fof(f1,axiom,(
% 1.50/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.50/0.58  fof(f153,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k3_xboole_0(X0,X0)) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.50/0.58    inference(forward_demodulation,[],[f147,f114])).
% 1.50/0.58  fof(f147,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),k10_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(X1,k9_relat_1(k6_relat_1(X0),X0)) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.50/0.58    inference(superposition,[],[f52,f57])).
% 1.50/0.58  fof(f52,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f31])).
% 1.50/0.58  fof(f31,plain,(
% 1.50/0.58    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.50/0.58    inference(flattening,[],[f30])).
% 1.50/0.58  fof(f30,plain,(
% 1.50/0.58    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.50/0.58    inference(ennf_transformation,[],[f15])).
% 1.50/0.58  fof(f15,axiom,(
% 1.50/0.58    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_funct_1)).
% 1.50/0.58  fof(f441,plain,(
% 1.50/0.58    ( ! [X12,X11] : (k3_xboole_0(X12,X11) = k3_xboole_0(X11,k3_xboole_0(X12,X11))) )),
% 1.50/0.58    inference(superposition,[],[f156,f408])).
% 1.50/0.58  fof(f408,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k3_xboole_0(X1,X0) = k10_relat_1(k6_relat_1(X0),X1)) )),
% 1.50/0.58    inference(forward_demodulation,[],[f379,f156])).
% 1.50/0.58  fof(f379,plain,(
% 1.50/0.58    ( ! [X0,X1] : (k10_relat_1(k6_relat_1(X0),X1) = k3_xboole_0(X0,k10_relat_1(k6_relat_1(X0),X1))) )),
% 1.50/0.58    inference(superposition,[],[f120,f134])).
% 1.50/0.58  fof(f120,plain,(
% 1.50/0.58    ( ! [X2,X0,X1] : (k3_xboole_0(X1,k10_relat_1(k6_relat_1(X0),X2)) = k10_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),X2)) )),
% 1.50/0.58    inference(global_subsumption,[],[f54,f115])).
% 1.50/0.58  fof(f115,plain,(
% 1.50/0.58    ( ! [X2,X0,X1] : (k3_xboole_0(X1,k10_relat_1(k6_relat_1(X0),X2)) = k10_relat_1(k6_relat_1(k3_xboole_0(X0,X1)),X2) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.50/0.58    inference(superposition,[],[f45,f110])).
% 1.50/0.58  fof(f45,plain,(
% 1.50/0.58    ( ! [X2,X0,X1] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.50/0.58    inference(cnf_transformation,[],[f22])).
% 1.50/0.58  fof(f22,plain,(
% 1.50/0.58    ! [X0,X1,X2] : (k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 1.50/0.58    inference(ennf_transformation,[],[f13])).
% 1.50/0.58  fof(f13,axiom,(
% 1.50/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).
% 1.50/0.58  fof(f124,plain,(
% 1.50/0.58    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) | spl3_7),
% 1.50/0.58    inference(avatar_component_clause,[],[f122])).
% 1.50/0.58  fof(f122,plain,(
% 1.50/0.58    spl3_7 <=> k10_relat_1(sK0,sK2) = k3_xboole_0(sK1,k10_relat_1(sK0,sK2))),
% 1.50/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.50/0.58  fof(f74,plain,(
% 1.50/0.58    r1_tarski(k10_relat_1(sK0,sK2),sK1) | ~spl3_3),
% 1.50/0.58    inference(avatar_component_clause,[],[f72])).
% 1.50/0.58  fof(f72,plain,(
% 1.50/0.58    spl3_3 <=> r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 1.50/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.50/0.58  fof(f125,plain,(
% 1.50/0.58    ~spl3_1 | ~spl3_7 | spl3_4),
% 1.50/0.58    inference(avatar_split_clause,[],[f119,f77,f122,f62])).
% 1.50/0.58  fof(f62,plain,(
% 1.50/0.58    spl3_1 <=> v1_relat_1(sK0)),
% 1.50/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.50/0.58  fof(f77,plain,(
% 1.50/0.58    spl3_4 <=> k10_relat_1(sK0,sK2) = k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 1.50/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.50/0.58  fof(f119,plain,(
% 1.50/0.58    k10_relat_1(sK0,sK2) != k3_xboole_0(sK1,k10_relat_1(sK0,sK2)) | ~v1_relat_1(sK0) | spl3_4),
% 1.50/0.58    inference(superposition,[],[f79,f45])).
% 1.50/0.58  fof(f79,plain,(
% 1.50/0.58    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) | spl3_4),
% 1.50/0.58    inference(avatar_component_clause,[],[f77])).
% 1.50/0.58  fof(f80,plain,(
% 1.50/0.58    ~spl3_4),
% 1.50/0.58    inference(avatar_split_clause,[],[f41,f77])).
% 1.50/0.58  fof(f41,plain,(
% 1.50/0.58    k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 1.50/0.58    inference(cnf_transformation,[],[f35])).
% 1.50/0.58  fof(f35,plain,(
% 1.50/0.58    (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 1.50/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f34,f33])).
% 1.50/0.58  fof(f33,plain,(
% 1.50/0.58    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 1.50/0.58    introduced(choice_axiom,[])).
% 1.50/0.58  fof(f34,plain,(
% 1.50/0.58    ? [X2,X1] : (k10_relat_1(sK0,X2) != k10_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(k10_relat_1(sK0,X2),X1)) => (k10_relat_1(sK0,sK2) != k10_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(k10_relat_1(sK0,sK2),sK1))),
% 1.50/0.58    introduced(choice_axiom,[])).
% 1.50/0.58  fof(f21,plain,(
% 1.50/0.58    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.50/0.58    inference(flattening,[],[f20])).
% 1.50/0.58  fof(f20,plain,(
% 1.50/0.58    ? [X0] : (? [X1,X2] : (k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(k10_relat_1(X0,X2),X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.50/0.58    inference(ennf_transformation,[],[f19])).
% 1.50/0.58  fof(f19,negated_conjecture,(
% 1.50/0.58    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.50/0.58    inference(negated_conjecture,[],[f18])).
% 1.50/0.58  fof(f18,conjecture,(
% 1.50/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(k10_relat_1(X0,X2),X1) => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2)))),
% 1.50/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).
% 1.50/0.58  fof(f75,plain,(
% 1.50/0.58    spl3_3),
% 1.50/0.58    inference(avatar_split_clause,[],[f40,f72])).
% 1.50/0.58  fof(f40,plain,(
% 1.50/0.58    r1_tarski(k10_relat_1(sK0,sK2),sK1)),
% 1.50/0.58    inference(cnf_transformation,[],[f35])).
% 1.50/0.58  fof(f65,plain,(
% 1.50/0.58    spl3_1),
% 1.50/0.58    inference(avatar_split_clause,[],[f38,f62])).
% 1.50/0.58  fof(f38,plain,(
% 1.50/0.58    v1_relat_1(sK0)),
% 1.50/0.58    inference(cnf_transformation,[],[f35])).
% 1.50/0.58  % SZS output end Proof for theBenchmark
% 1.50/0.58  % (23259)------------------------------
% 1.50/0.58  % (23259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.58  % (23259)Termination reason: Refutation
% 1.50/0.58  
% 1.50/0.58  % (23259)Memory used [KB]: 11257
% 1.50/0.58  % (23259)Time elapsed: 0.160 s
% 1.50/0.58  % (23259)------------------------------
% 1.50/0.58  % (23259)------------------------------
% 1.50/0.58  % (23233)Success in time 0.21 s
%------------------------------------------------------------------------------
